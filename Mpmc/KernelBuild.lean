/-
  Copyright (c) 2026 Mohammad Mahdi Abdollahpour.
  The contents of this file are subject to the Common Public Attribution
  License Version 1.0 (the "License"); you may not use this file except in
  compliance with the License. You may obtain a copy of the License at
  https://opensource.org/license/cpal-1-0.
  The Original Code is mpmc-lean. The Initial Developer is Mohammad Mahdi
  Abdollahpour. See LICENSE and NOTICE.
-/
/-
  Real-invocation histories from a kernel path.

  `ObsHistory`/`KernelLinearize` already turn the tagged event list of a run
  into a linearizable history, but at *event* positions.  `BuildScan` records
  the real invocation/linearization/response positions, yet it is purely
  combinatorial.  This file connects the two: a scan of the actual schedule
  whose selected events are exactly the run's client events.

  The connection needs one kernel fact: an invocation emits at most one
  selected event (a successful push, a successful pop, or a legal failure)
  before it returns, and its return status determines the outcome.  We prove
  it with the post-event regions below:
  * push success: `(3,3)` with `rOk ≠ 0`, or `(4,0..3)`;
  * push full: the full-snapshot load/pos/ahead path, or `(6,0)`;
  * push exhausted: `(9,0)`;
  * pop success: `(7,3)` with `rOk ≠ 0`, or `(4,0..4)`;
  * pop empty: the empty-snapshot load/pos/parity path, or `(3,0)`;
  * pop exhausted: `(8,0)`.
-/
import Mpmc.ObsHistory
import Mpmc.KernelObserve
import Mpmc.KernelLoadObs

namespace Mpmc

open Mpmc.Kernel

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.unnecessarySimpa false

/-! ## Client events of a tag list -/

/-- The queue-level events recorded by one tagged step. -/
def StepTag.clientEvents : StepTag UInt64 → List (ClientEvent UInt64)
  | .event (.push v) r => [.step (.push v) r]
  | .event .pop r => [.step .pop r]
  | .event .helpW _ => []
  | .event .helpR _ => []
  | .obs k => [.obs k]
  | .stutter => []
  | .ret _ => []

/-- One tagged effect replays exactly its client events. -/
theorem Effect.clientEvents_trace {z : UInt64} {C limit : Nat} {hC : 0 < C}
    {s m s' m' : _} {tag : StepTag UInt64}
    (h : Effect z C limit hC s m s' m' tag) :
    ClientTrace C limit (sync s) tag.clientEvents (sync s') := by
  cases h with
  | stutter hm hs hmem =>
      cases hs; cases hmem
      exact ClientTrace.nil _
  | event a r hev =>
      cases hev with
      | push hi hm hprov hlim hcell v =>
          obtain ⟨s1, hstep, hhelp⟩ :=
            Step.push_sync_help (EventStep.step (z := z) (hC := hC)
              (EventStep.push (hC := hC) hi hm hprov hlim hcell v))
          exact ClientTrace.push hstep hhelp (ClientTrace.nil _)
      | pop hi hm hprov hlim p hcell =>
          obtain ⟨s1, hstep, hhelp⟩ :=
            Step.pop_sync_help (EventStep.step (z := z) (hC := hC)
              (EventStep.pop (hC := hC) hi hm hprov hlim p hcell))
          exact ClientTrace.pop hstep hhelp (ClientTrace.nil _)
      | helpW hi hm hw hW =>
          rw [sync_helpW]
          exact ClientTrace.nil _
      | helpR hi hm hr hR =>
          rw [sync_helpR]
          exact ClientTrace.nil _
  | obs k hm guard hs hmem =>
      cases hs; cases hmem
      exact ClientTrace.obs (ObsGuard.sync guard) (ClientTrace.nil _)
  | ret status hm hs hmem =>
      cases hs; cases hmem
      exact ClientTrace.nil _

/-- A tagged execution replays exactly the client events of its tag list. -/
theorem Exec.clientEvents_trace {n C limit : Nat} {hC : 0 < C}
    {kind : Fin n → Kind} {s : AbsState UInt64} {g : GState n}
    {ms : List (Move n)} {s' : AbsState UInt64} {g' : GState n}
    {tags : List (Fin n × StepTag UInt64)}
    (h : Exec kind C limit hC s g ms s' g' tags) :
    ClientTrace C limit (sync s)
      (tags.flatMap (fun p => p.2.clientEvents)) (sync s') := by
  induction h with
  | nil => exact ClientTrace.nil _
  | step hstep heff hs ih =>
      have h1 := Effect.clientEvents_trace (z := (0 : UInt64)) heff
      have h2 := ClientTrace.append h1 ih
      simpa [List.flatMap_cons, StepTag.clientEvents] using h2
  | invoke h hg' hshared href hs ih =>
      simpa [List.flatMap_cons, StepTag.clientEvents] using ih

/-! ## Execution stages

The stage of a thread is read off its local phase and registers.  It is the
abstract "where is this invocation" state used by the history scan: `pre`
before the selected event, `success`/`pushFull`/`popEmpty`/`exhausted` after
the event, and `done` after the return. -/

inductive Stage where
  | pre
  | success
  | pushFull
  | popEmpty
  | exhausted
  | done
  deriving DecidableEq, Repr

/-- The stage of a push thread.  The load/position and `ahead` phases are
shared between the full path and the retry path; `q + C = h` disambiguates
them, exactly as the program's `ahead` test does. -/
def pushStage (C : Nat) (loc : Local) : Stage :=
  match loc.phase with
  | .running 1 2 =>
      if (loc.regs rMarker).toNat / 2 + C = (loc.regs rHint).toNat then .pushFull else .pre
  | .running 1 3 =>
      if (loc.regs rMarker).toNat / 2 + C = (loc.regs rHint).toNat then .pushFull else .pre
  | .running 3 3 =>
      if loc.regs rOk = 0 then .pre else .success
  | .running 4 _ => .success
  | .running 5 0 =>
      if (loc.regs rMarker).toNat / 2 + C = (loc.regs rHint).toNat then .pushFull else .pre
  | .running 5 1 =>
      if (loc.regs rMarker).toNat / 2 + C = (loc.regs rHint).toNat then .pushFull else .pre
  | .running 6 _ => .pushFull
  | .running 9 _ => .exhausted
  | .returned _ => .done
  | _ => .pre

/-- The stage of a pop thread. -/
def popStage (C : Nat) (loc : Local) : Stage :=
  match loc.phase with
  | .running 1 2 =>
      if (loc.regs rMarker).toNat / 2 = (loc.regs rHint).toNat ∧
          (loc.regs rMarker).toNat % 2 = 0 then .popEmpty else .pre
  | .running 1 3 =>
      if (loc.regs rMarker).toNat / 2 = (loc.regs rHint).toNat ∧
          (loc.regs rMarker).toNat % 2 = 0 then .popEmpty else .pre
  | .running 2 0 =>
      if (loc.regs rMarker).toNat / 2 = (loc.regs rHint).toNat ∧
          (loc.regs rMarker).toNat % 2 = 0 then .popEmpty else .pre
  | .running 2 1 =>
      if (loc.regs rMarker).toNat / 2 = (loc.regs rHint).toNat ∧
          (loc.regs rMarker).toNat % 2 = 0 then .popEmpty else .pre
  | .running 3 0 => .popEmpty
  | .running 7 3 =>
      if loc.regs rOk = 0 then .pre else .success
  | .running 4 _ => .success
  | .running 8 0 => .exhausted
  | .returned _ => .done
  | _ => .pre

/-- The stage of a thread of either role. -/
def threadStage (C : Nat) (kind : Kind) (loc : Local) : Stage :=
  match kind with
  | .push => pushStage C loc
  | .pop => popStage C loc

/-- The stage a linearized outcome requires. -/
def stageOfOutcome : OpOutcome → Stage
  | .success _ _ => .success
  | .failure .pushFull => .pushFull
  | .failure .popEmpty => .popEmpty
  | .failure .pushExhausted => .exhausted
  | .failure .popExhausted => .exhausted

/-- The kernel status code returned when a thread is at a given stage.  A
push that observed a full queue returns `1`, a pop that observed an empty
queue returns `2`, a horizon failure returns `3`, and success returns `0`. -/
def Stage.status : Stage → UInt64
  | .pre => 0
  | .success => 0
  | .pushFull => 1
  | .popEmpty => 2
  | .exhausted => 3
  | .done => 0

/-- Every stage outcome is accepted by the corresponding abstract outcome. -/
theorem stageOfOutcome_accepts (o : OpOutcome) :
    o.acceptsStatus (stageOfOutcome o).status := by
  cases o with
  | success a r => cases a <;> rfl
  | failure k => cases k <;> simp [OpOutcome.acceptsStatus, stageOfOutcome, Stage.status]

/-- At the return of a successful operation, the success-path output stores
have copied the position/value registers: a push outputs its publication
position (`rHint`), a pop outputs the popped value (`rPayload`) and position
(`rHint`).  The implication is vacuous for failure stages. -/
def RetOutputs (kind : Kind) (C : Nat) (loc : Local) : Prop :=
  match kind with
  | .push => pushStage C loc = .success →
      loc.out0 = UInt64.ofNat (loc.regs rHint).toNat
  | .pop => popStage C loc = .success →
      loc.out0 = loc.regs rPayload ∧ loc.out1 = UInt64.ofNat (loc.regs rHint).toNat

/-- The neutral/selected transition classification of one step.  The tag is
either invisible (a stutter or a help CAS), a selected push/pop/failure
event that moves a `pre` stage to the matching post stage, or the exact
canonical return status of the current stage. -/
def StepClass (kind : Kind) (C : Nat) (loc loc' : Local) (tag : StepTag UInt64) : Prop :=
  let st := threadStage C kind loc
  let st' := threadStage C kind loc'
  (tag = .stutter ∧ st' = st) ∨
  ((tag = .event .helpW .helped ∨ tag = .event .helpR .helped) ∧ st' = st) ∨
  (tag = .obs .pushFull ∧ kind = .push ∧ st = .pre ∧ st' = .pushFull) ∨
  (tag = .obs .popEmpty ∧ kind = .pop ∧ st = .pre ∧ st' = .popEmpty) ∨
  (tag = .obs .pushExhausted ∧ kind = .push ∧ st = .pre ∧ st' = .exhausted) ∨
  (tag = .obs .popExhausted ∧ kind = .pop ∧ st = .pre ∧ st' = .exhausted) ∨
  (kind = .push ∧ ∃ v h, tag = .event (.push v) (.pushed h) ∧ v = loc.value ∧
      loc'.regs rHint = UInt64.ofNat h ∧ st = .pre ∧ st' = .success) ∨
  (kind = .pop ∧ ∃ h p, tag = .event .pop (.popped h p) ∧
      loc'.regs rHint = UInt64.ofNat h ∧ loc'.regs rPayload = p ∧
      st = .pre ∧ st' = .success) ∨
  (st ≠ .pre ∧ tag = .ret st.status ∧ ∃ v, loc'.phase = Phase.returned v ∧
      RetOutputs kind C loc)

/-- The three push phases at which a selected event is emitted: the hint
horizon test, the cell load, and the cell CAS. -/
def PushSelected (loc : Local) : Prop :=
  loc.phase = Phase.running 0 1 ∨
  loc.phase = Phase.running 1 1 ∨
  loc.phase = Phase.running 3 2

/-- The three pop phases at which a selected event is emitted. -/
def PopSelected (loc : Local) : Prop :=
  loc.phase = Phase.running 0 1 ∨
  loc.phase = Phase.running 1 1 ∨
  loc.phase = Phase.running 7 2

/-! ## The scan alignment state -/

/-- The register link between a successful outcome and the kernel local:
`rHint` holds the publication/consumption position and `rPayload` the popped
value.  These are exactly the registers that the success-path output stores
copy into `out0`/`out1`. -/
def OutcomeRegs {n : Nat} (o : OpOutcome) (loc : Local) : Prop :=
  match o with
  | .success (.push _) (.pushed h) => loc.regs rHint = UInt64.ofNat h
  | .success .pop (.popped h p) => loc.regs rHint = UInt64.ofNat h ∧ loc.regs rPayload = p
  | _ => True

/-- The outcome's action is compatible with the thread's role. -/
def OutcomeKind (kind : Kind) : OpOutcome → Prop
  | .success (.push _) _ => kind = .push
  | .success .pop _ => kind = .pop
  | _ => True

/-- A `BuildState` phase agrees with the kernel's local stage and, when the
operation is already linearized, the local stage is the one recorded in the
outcome. -/
def AlignThread {n : Nat} (C limit : Nat) (kind : Fin n → Kind)
    (g : GState n) (st : BuildState n) (i : Fin n) : Prop :=
  match st.phase i with
  | .idle =>
      (∃ v, (g.locals i).phase = Phase.returned v) ∨
      (g.locals i).phase = Phase.trapped
  | .invoked p =>
      p.input = (g.locals i).value ∧
      p.inv < st.pos ∧
      threadStage C (kind i) (g.locals i) = .pre
  | .linearized o =>
      threadStage C (kind i) (g.locals i) = stageOfOutcome o.outcome ∧
      OutcomeKind (kind i) o.outcome ∧ OutcomeRegs (n := n) o.outcome (g.locals i)

/-- The global scan alignment: every thread's scan phase matches its kernel
stage, and the scan state is well formed. -/
structure Align {n : Nat} (C limit : Nat) (kind : Fin n → Kind)
    (g : GState n) (st : BuildState n) : Prop where
  wf : st.WF
  thread : ∀ i, AlignThread C limit kind g st i

/-! ## Local certificates for one push/pop step -/

/-- A local certificate for one push operation. -/
def PushCert (C limit : Nat) (hC : 0 < C) (s : AbsState UInt64) (sh : Shared)
    (loc : Local) (r : OpResult) : Prop :=
  ∃ (s' : AbsState UInt64) (sh' : Shared) (loc' : Local) (tag : StepTag UInt64),
    After sh loc r sh' loc' ∧
    PushInv C limit s' sh' loc' loc'.phase ∧
    SharedRef C limit s' sh' ∧
    Inv C limit s' ∧
    Effect 0 C limit hC s (Shared.toMem sh) s' (Shared.toMem sh') tag ∧
    StepClass .push C loc loc' tag

/-- A local certificate for one pop operation. -/
def PopCert (C limit : Nat) (hC : 0 < C) (s : AbsState UInt64) (sh : Shared)
    (loc : Local) (r : OpResult) : Prop :=
  ∃ (s' : AbsState UInt64) (sh' : Shared) (loc' : Local) (tag : StepTag UInt64),
    After sh loc r sh' loc' ∧
    PopInv C limit s' sh' loc' loc'.phase ∧
    SharedRef C limit s' sh' ∧
    Inv C limit s' ∧
    Effect 0 C limit hC s (Shared.toMem sh) s' (Shared.toMem sh') tag ∧
    StepClass .pop C loc loc' tag

/-- A non-stutter event changes the memory. -/
theorem EventStep.mem_ne {V : Type} {z : V} {C limit : Nat} {hC : 0 < C}
    {s m s' m' : _} {a : Action V} {r : Result V}
    (h : EventStep z C limit hC s m (some a) (some r) s' m') : m ≠ m' := by
  intro heq
  cases h with
  | push hi hm hprov hlim hcell v =>
      rename_i h
      have hcellEq := congrArg (fun mm : Mem V => mm.cells (h % C)) heq
      simp [Mem.setCell] at hcellEq
      rw [hcell] at hcellEq
      have hmark := congrArg Cell.marker hcellEq
      simp [emptyCell, fullCell] at hmark
  | pop hi hm hprov hlim p hcell =>
      rename_i h
      have hcellEq := congrArg (fun mm : Mem V => mm.cells (h % C)) heq
      simp [Mem.setCell] at hcellEq
      rw [hcell] at hcellEq
      have hmark := congrArg Cell.marker hcellEq
      simp [emptyCell, fullCell] at hmark
      omega
  | helpW hi hm hw hW =>
      have hw' := congrArg (fun mm : Mem V => mm.w) heq
      simp at hw'
      omega
  | helpR hi hm hr hR =>
      have hr' := congrArg (fun mm : Mem V => mm.r) heq
      simp at hr'
      omega

/-! ## From a scan history to a linearizable history -/

/-- A history whose client events replay from `s0` to `s'` linearizes. -/
theorem BuildHistory.linearizes_of_clientEvents {n C limit : Nat}
    {kind : Fin n → Kind} {ms : List (Move n)}
    {tags : List (Fin n × StepTag UInt64)} {hist : ObsHistory n}
    {s0 s' : AbsState UInt64} {evs : List (ClientEvent UInt64)}
    (hb : BuildHistory kind ms tags hist)
    (hc : Canonical s0)
    (htrace : ClientTrace C limit s0 evs s')
    (hevents : hist.clientEvents = evs) :
    hist.Linearizes C limit s0 s' := by
  rw [ObsHistory.Linearizes, hevents]
  exact ClientTrace.toClientScan hc htrace

/-- The event list selected by a scan step is the concatenation of the
client events of the consumed tag. -/
theorem BuildScan.append {n : Nat} {kind : Fin n → Kind}
    {st0 st1 st2 : BuildState n}
    {l1 l2 : List (Move n × Fin n × StepTag UInt64)}
    (h1 : BuildScan kind st0 l1 st1) (h2 : BuildScan kind st1 l2 st2) :
    BuildScan kind st0 (l1 ++ l2) st2 := by
  induction h1 with
  | nil => exact h2
  | invoke hidle _ ih => exact BuildScan.invoke hidle (ih h2)
  | stutterStep _ ih => exact BuildScan.stutterStep (ih h2)
  | helpStep hhelp _ ih => exact BuildScan.helpStep hhelp (ih h2)
  | pushEvent hkind hp hval hinv _ ih => exact BuildScan.pushEvent hkind hp hval hinv (ih h2)
  | popEvent hkind hp hinv _ ih => exact BuildScan.popEvent hkind hp hinv (ih h2)
  | obsEvent hadmit hp hinv _ ih => exact BuildScan.obsEvent hadmit hp hinv (ih h2)
  | retLin hp hstatus _ ih => exact BuildScan.retLin hp hstatus (ih h2)
  | retPending hp hstatus _ ih => exact BuildScan.retPending hp hstatus (ih h2)
  | skipIdle hidle _ ih => exact BuildScan.skipIdle hidle (ih h2)

/-- A single scan step can be appended to the left of a scan. -/
theorem BuildScan.cons {n : Nat} {kind : Fin n → Kind}
    {st st1 st2 : BuildState n} {entry : Move n × Fin n × StepTag UInt64}
    {rest : List (Move n × Fin n × StepTag UInt64)}
    (h1 : BuildScan kind st [entry] st1)
    (h2 : BuildScan kind st1 rest st2) : BuildScan kind st (entry :: rest) st2 := by
  simpa using BuildScan.append h1 h2


theorem push_horizon_exhausted_phase {n C limit k : Nat} {kind : Fin n → Kind}
    {s : AbsState UInt64} {g g' : GState n} {i : Fin n}
    (hi : Inv C limit s) (hg : GRef C limit kind s g)
    (hC : 0 < C) (hpow : C = 2 ^ k) (hCmax : C ≤ 2 ^ 24)
    (hbound : limit < 2 ^ 63) (hlimitC : limit + C ≤ 2 ^ 63)
    (hk : kind i = .push)
    (hp : (g.locals i).phase = Phase.running 0 1)
    (hstep : GStep kind g i g')
    (hge : limit ≤ ((g.locals i).regs rHint).toNat) :
    (g'.locals i).phase = Phase.running 9 0 := by
  have hpinv : PushInv C limit s g.shared (g.locals i) (Phase.running 0 1) := by
    have h1 := hg.hlocal i
    simp only [ThreadInv, hk, hp] at h1
    exact h1
  cases hpinv with
  | hint h hpc hintEq hintLe =>
    have hle : h ≤ limit := Nat.le_trans hintLe (Nat.le_trans hi.hw_le hi.hlimit)
    have h64 : h < 2 ^ 64 := by have := hbound; omega
    have hgeH : limit ≤ h := by
      rw [hintEq] at hge
      simpa [uint64_toNat_ofNat_of_lt h64] using hge
    have hnot : ¬ ((toMState g.shared (g.locals i)).regs rHint <
        (toMState g.shared (g.locals i)).params.limit) := by
      show ¬ ((g.locals i).regs rHint < g.shared.params.limit)
      rw [hintEq, hg.hshared.limit_eq]
      intro hc
      have hc' := (u64_lt_ofNat_iff h64 (by omega)).mp hc
      omega
    have hst : opStep pushProgram 0 1 (toMState g.shared (g.locals i)) =
        .running 9 0 (toMState g.shared (g.locals i)) := by
      simp [opStep, pushProgram, eval, hnot]
    have hs := hstep
    simp only [GStep, programOf, hk, hp, hst] at hs
    rw [hs]
    simp [updLocal]

theorem push_horizon_tag {n C limit k : Nat} {kind : Fin n → Kind}
    {s : AbsState UInt64} {g g' : GState n} {i : Fin n}
    (hi : Inv C limit s) (hg : GRef C limit kind s g)
    (hC : 0 < C) (hpow : C = 2 ^ k) (hCmax : C ≤ 2 ^ 24)
    (hbound : limit < 2 ^ 63) (hlimitC : limit + C ≤ 2 ^ 63)
    (hk : kind i = .push)
    (hp : (g.locals i).phase = Phase.running 0 1)
    (hstep : GStep kind g i g') :
    ∃ s' tag, GRef C limit kind s' g' ∧ Inv C limit s' ∧
      Effect 0 C limit hC s (Shared.toMem g.shared) s' (Shared.toMem g'.shared) tag ∧
      ((limit ≤ ((g.locals i).regs rHint).toNat ∧ tag = .obs .pushExhausted ∧
          (g'.locals i).phase = Phase.running 9 0) ∨
       (¬ limit ≤ ((g.locals i).regs rHint).toNat ∧ tag = .stutter ∧
          (g'.locals i).phase = Phase.running 1 0)) := by
  by_cases hge : limit ≤ ((g.locals i).regs rHint).toNat
  · obtain ⟨s', tag, hg', hi', heff, htag⟩ :=
      push_horizon_exhausted_effect hi hg hC hpow hCmax hbound hlimitC hk hp hstep hge
    refine ⟨s', tag, hg', hi', heff, Or.inl ⟨hge, htag, ?_⟩⟩
    -- the effect lemma computes the post phase
    exact push_horizon_exhausted_phase hi hg hC hpow hCmax hbound hlimitC hk hp hstep hge
  · have hpinv : PushInv C limit s g.shared (g.locals i) (Phase.running 0 1) := by
      have h1 := hg.hlocal i
      simp only [ThreadInv, hk, hp] at h1
      exact h1
    cases hpinv with
    | hint h hpc hintEq hintLe =>
      have hle : h ≤ limit := Nat.le_trans hintLe (Nat.le_trans hi.hw_le hi.hlimit)
      have h64 : h < 2 ^ 64 := by have := hbound; omega
      have hnotge : ¬ limit ≤ h := by
        rw [hintEq] at hge
        simpa [uint64_toNat_ofNat_of_lt h64] using hge
      have hlt : h < limit := by omega
      have hcond : (toMState g.shared (g.locals i)).regs rHint <
          (toMState g.shared (g.locals i)).params.limit := by
        show (g.locals i).regs rHint < g.shared.params.limit
        rw [hintEq, hg.hshared.limit_eq]
        exact (u64_lt_ofNat_iff h64 (by omega)).mpr hlt
      have hst : opStep pushProgram 0 1 (toMState g.shared (g.locals i)) =
          .running 1 0 (toMState g.shared (g.locals i)) := by
        simp [opStep, pushProgram, eval, hcond]
      have hgshare : g'.shared = g.shared := by
        have hs := hstep
        simp only [GStep, programOf, hk, hp, hst] at hs
        rw [hs]
        simp [Shared.after, toMState]
      obtain ⟨s', hg', hev | ⟨hs, hsh⟩⟩ :=
        gstep_sim hi hg hC hpow hCmax hbound hlimitC hstep
      · -- an event is impossible: the branch changes no memory
        exfalso
        obtain ⟨a, res, hev⟩ := hev
        have hmem : Shared.toMem g'.shared = Shared.toMem g.shared := by rw [hgshare]
        exact (EventStep.mem_ne hev) hmem.symm
      · have hsEq : s' = s := hs
        subst s'
        have hphase : (g'.locals i).phase = Phase.running 1 0 := by
          have hs := hstep
          simp only [GStep, programOf, hk, hp, hst] at hs
          rw [hs]
          simp [updLocal]
        refine ⟨s, .stutter, hg', hi, ?_, Or.inr ⟨hge, rfl, hphase⟩⟩
        exact Effect.stutter (SharedRef.ref hg.hshared) rfl (by rw [hsh])



theorem push_load_phase {n C limit k : Nat} {kind : Fin n → Kind}
    {s : AbsState UInt64} {g g' : GState n} {i : Fin n}
    (hi : Inv C limit s) (hg : GRef C limit kind s g)
    (hC : 0 < C) (hpow : C = 2 ^ k) (hbound : limit < 2 ^ 63)
    (hk : kind i = .push)
    (hp : (g.locals i).phase = Phase.running 1 1)
    (hstep : GStep kind g i g') :
    (g'.locals i).phase = Phase.running 1 2 := by
  have hpinv : PushInv C limit s g.shared (g.locals i) (Phase.running 1 1) := by
    have h1 := hg.hlocal i
    simp only [ThreadInv, hk, hp] at h1
    exact h1
  cases hpinv with
  | slot h hpc hintEq hintLe hlim slotEq =>
    have h64 : h < 2 ^ 64 := by
      have h1 := hintLe
      have h2 := hi.hw_le
      have h3 := hi.hlimit
      have h4 := hbound
      omega
    have hmodle : h % C ≤ h := Nat.mod_le h C
    have hmod64 : h % C < 2 ^ 64 := by omega
    have hslotNat : ((g.locals i).regs rSlot).toNat = h % C := by
      rw [slotEq]
      exact uint64_toNat_ofNat_of_lt hmod64
    let m := (g.shared.cells (h % C)).marker.toNat
    let st0 := toMState g.shared (g.locals i)
    let regs1 := upd (st0.regs) rMarker (g.shared.cells (h % C)).marker
    let regs2 := upd regs1 rPayload (g.shared.cells (h % C)).payload
    let st' := { st0 with regs := regs2 }
    have hcellEq : (toMState g.shared (g.locals i)).cells
        ((toMState g.shared (g.locals i)).regs rSlot).toNat =
        g.shared.cells (h % C) := by
      show g.shared.cells ((g.locals i).regs rSlot).toNat = g.shared.cells (h % C)
      rw [hslotNat]
    have hst : opStep pushProgram 1 1 (toMState g.shared (g.locals i)) =
        .running 1 2 st' := by
      simp [opStep, pushProgram, execOp, eval, st', st0, regs1, regs2, hcellEq]
    have hs := hstep
    simp only [GStep, programOf, hk, hp, hst] at hs
    rw [hs]
    simp [updLocal]

theorem push_load_tag {n C limit k : Nat} {kind : Fin n → Kind}
    {s : AbsState UInt64} {g g' : GState n} {i : Fin n}
    (hi : Inv C limit s) (hg : GRef C limit kind s g)
    (hC : 0 < C) (hpow : C = 2 ^ k) (hCmax : C ≤ 2 ^ 24)
    (hbound : limit < 2 ^ 63) (hlimitC : limit + C ≤ 2 ^ 63)
    (hk : kind i = .push)
    (hp : (g.locals i).phase = Phase.running 1 1)
    (hstep : GStep kind g i g') :
    ∃ s' tag, GRef C limit kind s' g' ∧ Inv C limit s' ∧
      Effect 0 C limit hC s (Shared.toMem g.shared) s' (Shared.toMem g'.shared) tag ∧
      ((((g.shared.cells (((g.locals i).regs rSlot).toNat)).marker.toNat / 2 + C =
          ((g.locals i).regs rHint).toNat) ∧ tag = .obs .pushFull ∧
          (g'.locals i).phase = Phase.running 1 2) ∨
       (¬ ((g.shared.cells (((g.locals i).regs rSlot).toNat)).marker.toNat / 2 + C =
          ((g.locals i).regs rHint).toNat) ∧ tag = .stutter ∧
          (g'.locals i).phase = Phase.running 1 2)) := by
  by_cases hfull : (g.shared.cells (((g.locals i).regs rSlot).toNat)).marker.toNat / 2 + C =
      ((g.locals i).regs rHint).toNat
  · obtain ⟨s', tag, hg', hi', heff, htag⟩ :=
      push_load_full_effect hi hg hC hpow hCmax hbound hlimitC hk hp hstep hfull
    refine ⟨s', tag, hg', hi', heff, Or.inl ⟨hfull, htag, push_load_phase hi hg hC hpow hbound hk hp hstep⟩⟩
  · have hphase := push_load_phase hi hg hC hpow hbound hk hp hstep
    have hpinv : PushInv C limit s g.shared (g.locals i) (Phase.running 1 1) := by
      have h1 := hg.hlocal i
      simp only [ThreadInv, hk, hp] at h1
      exact h1
    cases hpinv with
    | slot h hpc hintEq hintLe hlim slotEq =>
      have h64 : h < 2 ^ 64 := by
        have h1 := hintLe
        have h2 := hi.hw_le
        have h3 := hi.hlimit
        have h4 := hbound
        omega
      have hmodle : h % C ≤ h := Nat.mod_le h C
      have hmod64 : h % C < 2 ^ 64 := by omega
      have hslotNat : ((g.locals i).regs rSlot).toNat = h % C := by
        rw [slotEq]
        exact uint64_toNat_ofNat_of_lt hmod64
      let m := (g.shared.cells (h % C)).marker.toNat
      let st0 := toMState g.shared (g.locals i)
      let regs1 := upd (st0.regs) rMarker (g.shared.cells (h % C)).marker
      let regs2 := upd regs1 rPayload (g.shared.cells (h % C)).payload
      let st' := { st0 with regs := regs2 }
      have hcellEq : (toMState g.shared (g.locals i)).cells
          ((toMState g.shared (g.locals i)).regs rSlot).toNat =
          g.shared.cells (h % C) := by
        show g.shared.cells ((g.locals i).regs rSlot).toNat = g.shared.cells (h % C)
        rw [hslotNat]
      have hst : opStep pushProgram 1 1 (toMState g.shared (g.locals i)) =
          .running 1 2 st' := by
        simp [opStep, pushProgram, execOp, eval, st', st0, regs1, regs2, hcellEq]
      have hgshare : g'.shared = g.shared := by
        have hs := hstep
        simp only [GStep, programOf, hk, hp, hst] at hs
        rw [hs]
        simp [Shared.after, st', st0, regs1, regs2, toMState]
      obtain ⟨s', hg', hev | ⟨hs, hsh⟩⟩ :=
        gstep_sim hi hg hC hpow hCmax hbound hlimitC hstep
      · exfalso
        obtain ⟨a, res, hev⟩ := hev
        have hmem : Shared.toMem g'.shared = Shared.toMem g.shared := by rw [hgshare]
        exact (EventStep.mem_ne hev) hmem.symm
      · have hsEq : s' = s := hs
        subst s'
        refine ⟨s, .stutter, hg', hi, ?_, Or.inr ⟨hfull, rfl, hphase⟩⟩
        exact Effect.stutter (SharedRef.ref hg.hshared) rfl (by rw [hsh])



theorem pop_horizon_phase {n C limit k : Nat} {kind : Fin n → Kind}
    {s : AbsState UInt64} {g g' : GState n} {i : Fin n}
    (hi : Inv C limit s) (hg : GRef C limit kind s g)
    (hC : 0 < C) (hpow : C = 2 ^ k) (hbound : limit < 2 ^ 63)
    (hk : kind i = .pop)
    (hp : (g.locals i).phase = Phase.running 0 1)
    (hstep : GStep kind g i g')
    (hge : limit ≤ ((g.locals i).regs rHint).toNat) :
    (g'.locals i).phase = Phase.running 8 0 := by
  have hpinv : PopInv C limit s g.shared (g.locals i) (Phase.running 0 1) := by
    have h1 := hg.hlocal i
    simp only [ThreadInv, hk, hp] at h1
    exact h1
  cases hpinv with
  | hint h hpc hintEq hintLe =>
    have hle : h ≤ limit := Nat.le_trans hintLe (Nat.le_trans hi.hr_le
      (Nat.le_trans hi.hR_le_W hi.hlimit))
    have h64 : h < 2 ^ 64 := by
      have h1 := hintLe
      have h2 := hi.hr_le
      have h3 := hi.hR_le_W
      have h4 := hi.hlimit
      have h5 := hbound
      omega
    have hgeH : limit ≤ h := by
      rw [hintEq] at hge
      simpa [uint64_toNat_ofNat_of_lt h64] using hge
    have hnot : ¬ ((toMState g.shared (g.locals i)).regs rHint <
        (toMState g.shared (g.locals i)).params.limit) := by
      show ¬ ((g.locals i).regs rHint < g.shared.params.limit)
      rw [hintEq, hg.hshared.limit_eq]
      intro hc
      have hc' := (u64_lt_ofNat_iff h64 (by omega)).mp hc
      omega
    have hst : opStep popProgram 0 1 (toMState g.shared (g.locals i)) =
        .running 8 0 (toMState g.shared (g.locals i)) := by
      simp [opStep, popProgram, eval, hnot]
    have hs := hstep
    simp only [GStep, programOf, hk, hp, hst] at hs
    rw [hs]
    simp [updLocal]

theorem pop_horizon_tag {n C limit k : Nat} {kind : Fin n → Kind}
    {s : AbsState UInt64} {g g' : GState n} {i : Fin n}
    (hi : Inv C limit s) (hg : GRef C limit kind s g)
    (hC : 0 < C) (hpow : C = 2 ^ k) (hCmax : C ≤ 2 ^ 24)
    (hbound : limit < 2 ^ 63) (hlimitC : limit + C ≤ 2 ^ 63)
    (hk : kind i = .pop)
    (hp : (g.locals i).phase = Phase.running 0 1)
    (hstep : GStep kind g i g') :
    ∃ s' tag, GRef C limit kind s' g' ∧ Inv C limit s' ∧
      Effect 0 C limit hC s (Shared.toMem g.shared) s' (Shared.toMem g'.shared) tag ∧
      ((limit ≤ ((g.locals i).regs rHint).toNat ∧ tag = .obs .popExhausted ∧
          (g'.locals i).phase = Phase.running 8 0) ∨
       (¬ limit ≤ ((g.locals i).regs rHint).toNat ∧ tag = .stutter ∧
          (g'.locals i).phase = Phase.running 1 0)) := by
  by_cases hge : limit ≤ ((g.locals i).regs rHint).toNat
  · obtain ⟨s', tag, hg', hi', heff, htag⟩ :=
      pop_horizon_exhausted_effect hi hg hC hpow hCmax hbound hlimitC hk hp hstep hge
    refine ⟨s', tag, hg', hi', heff, Or.inl ⟨hge, htag, pop_horizon_phase hi hg hC hpow hbound hk hp hstep hge⟩⟩
  · have hpinv : PopInv C limit s g.shared (g.locals i) (Phase.running 0 1) := by
      have h1 := hg.hlocal i
      simp only [ThreadInv, hk, hp] at h1
      exact h1
    cases hpinv with
    | hint h hpc hintEq hintLe =>
      have hle : h ≤ limit := Nat.le_trans hintLe (Nat.le_trans hi.hr_le
        (Nat.le_trans hi.hR_le_W hi.hlimit))
      have h64 : h < 2 ^ 64 := by
        have h1 := hintLe
        have h2 := hi.hr_le
        have h3 := hi.hR_le_W
        have h4 := hi.hlimit
        have h5 := hbound
        omega
      have hnotge : ¬ limit ≤ h := by
        rw [hintEq] at hge
        simpa [uint64_toNat_ofNat_of_lt h64] using hge
      have hlt : h < limit := by omega
      have hcond : (toMState g.shared (g.locals i)).regs rHint <
          (toMState g.shared (g.locals i)).params.limit := by
        show (g.locals i).regs rHint < g.shared.params.limit
        rw [hintEq, hg.hshared.limit_eq]
        exact (u64_lt_ofNat_iff h64 (by omega)).mpr hlt
      have hst : opStep popProgram 0 1 (toMState g.shared (g.locals i)) =
          .running 1 0 (toMState g.shared (g.locals i)) := by
        simp [opStep, popProgram, eval, hcond]
      have hgshare : g'.shared = g.shared := by
        have hs := hstep
        simp only [GStep, programOf, hk, hp, hst] at hs
        rw [hs]
        simp [Shared.after, toMState]
      obtain ⟨s', hg', hev | ⟨hs, hsh⟩⟩ :=
        gstep_sim hi hg hC hpow hCmax hbound hlimitC hstep
      · exfalso
        obtain ⟨a, res, hev⟩ := hev
        have hmem : Shared.toMem g'.shared = Shared.toMem g.shared := by rw [hgshare]
        exact (EventStep.mem_ne hev) hmem.symm
      · have hsEq : s' = s := hs
        subst s'
        have hphase : (g'.locals i).phase = Phase.running 1 0 := by
          have hs := hstep
          simp only [GStep, programOf, hk, hp, hst] at hs
          rw [hs]
          simp [updLocal]
        refine ⟨s, .stutter, hg', hi, ?_, Or.inr ⟨hge, rfl, hphase⟩⟩
        exact Effect.stutter (SharedRef.ref hg.hshared) rfl (by rw [hsh])



theorem pop_load_phase {n C limit k : Nat} {kind : Fin n → Kind}
    {s : AbsState UInt64} {g g' : GState n} {i : Fin n}
    (hi : Inv C limit s) (hg : GRef C limit kind s g)
    (hC : 0 < C) (hpow : C = 2 ^ k) (hbound : limit < 2 ^ 63)
    (hk : kind i = .pop)
    (hp : (g.locals i).phase = Phase.running 1 1)
    (hstep : GStep kind g i g') :
    (g'.locals i).phase = Phase.running 1 2 := by
  have hpinv : PopInv C limit s g.shared (g.locals i) (Phase.running 1 1) := by
    have h1 := hg.hlocal i
    simp only [ThreadInv, hk, hp] at h1
    exact h1
  cases hpinv with
  | slot h hpc hintEq hintLe hlim slotEq =>
    have h64 : h < 2 ^ 64 := by
      have h1 : h ≤ s.r := hintLe
      have h2 : s.r ≤ s.R := hi.hr_le
      have h3 : s.R ≤ s.W := hi.hR_le_W
      have h4 : s.W ≤ limit := hi.hlimit
      have h5 := hbound
      omega
    have hmodle : h % C ≤ h := Nat.mod_le h C
    have hmod64 : h % C < 2 ^ 64 := by omega
    have hslotNat : ((g.locals i).regs rSlot).toNat = h % C := by
      rw [slotEq]
      exact uint64_toNat_ofNat_of_lt hmod64
    let st0 := toMState g.shared (g.locals i)
    let regs1 := upd (st0.regs) rMarker (g.shared.cells (h % C)).marker
    let regs2 := upd regs1 rPayload (g.shared.cells (h % C)).payload
    let st' := { st0 with regs := regs2 }
    have hcellEq : (toMState g.shared (g.locals i)).cells
        ((toMState g.shared (g.locals i)).regs rSlot).toNat =
        g.shared.cells (h % C) := by
      show g.shared.cells ((g.locals i).regs rSlot).toNat = g.shared.cells (h % C)
      rw [hslotNat]
    have hst : opStep popProgram 1 1 (toMState g.shared (g.locals i)) =
        .running 1 2 st' := by
      simp [opStep, popProgram, execOp, eval, st', st0, regs1, regs2, hcellEq]
    have hs := hstep
    simp only [GStep, programOf, hk, hp, hst] at hs
    rw [hs]
    simp [updLocal]

theorem pop_load_tag {n C limit k : Nat} {kind : Fin n → Kind}
    {s : AbsState UInt64} {g g' : GState n} {i : Fin n}
    (hi : Inv C limit s) (hg : GRef C limit kind s g)
    (hC : 0 < C) (hpow : C = 2 ^ k) (hCmax : C ≤ 2 ^ 24)
    (hbound : limit < 2 ^ 63) (hlimitC : limit + C ≤ 2 ^ 63)
    (hk : kind i = .pop)
    (hp : (g.locals i).phase = Phase.running 1 1)
    (hstep : GStep kind g i g') :
    ∃ s' tag, GRef C limit kind s' g' ∧ Inv C limit s' ∧
      Effect 0 C limit hC s (Shared.toMem g.shared) s' (Shared.toMem g'.shared) tag ∧
      ((((g.shared.cells (((g.locals i).regs rSlot).toNat)).marker.toNat / 2 =
          ((g.locals i).regs rHint).toNat) ∧
        ((g.shared.cells (((g.locals i).regs rSlot).toNat)).marker.toNat % 2 = 0) ∧
        tag = .obs .popEmpty ∧ (g'.locals i).phase = Phase.running 1 2) ∨
       (¬ (((g.shared.cells (((g.locals i).regs rSlot).toNat)).marker.toNat / 2 =
          ((g.locals i).regs rHint).toNat) ∧
        ((g.shared.cells (((g.locals i).regs rSlot).toNat)).marker.toNat % 2 = 0)) ∧
        tag = .stutter ∧ (g'.locals i).phase = Phase.running 1 2)) := by
  by_cases hempty : (g.shared.cells (((g.locals i).regs rSlot).toNat)).marker.toNat / 2 =
        ((g.locals i).regs rHint).toNat ∧
      (g.shared.cells (((g.locals i).regs rSlot).toNat)).marker.toNat % 2 = 0
  · obtain ⟨s', tag, hg', hi', heff, htag⟩ :=
      pop_load_empty_effect hi hg hC hpow hCmax hbound hlimitC hk hp hstep hempty.1 hempty.2
    refine ⟨s', tag, hg', hi', heff, Or.inl ⟨hempty.1, hempty.2, htag,
      pop_load_phase hi hg hC hpow hbound hk hp hstep⟩⟩
  · have hphase := pop_load_phase hi hg hC hpow hbound hk hp hstep
    have hpinv : PopInv C limit s g.shared (g.locals i) (Phase.running 1 1) := by
      have h1 := hg.hlocal i
      simp only [ThreadInv, hk, hp] at h1
      exact h1
    cases hpinv with
    | slot h hpc hintEq hintLe hlim slotEq =>
      have h64 : h < 2 ^ 64 := by
        have h1 : h ≤ s.r := hintLe
        have h2 : s.r ≤ s.R := hi.hr_le
        have h3 : s.R ≤ s.W := hi.hR_le_W
        have h4 : s.W ≤ limit := hi.hlimit
        have h5 := hbound
        omega
      have hmodle : h % C ≤ h := Nat.mod_le h C
      have hmod64 : h % C < 2 ^ 64 := by omega
      have hslotNat : ((g.locals i).regs rSlot).toNat = h % C := by
        rw [slotEq]
        exact uint64_toNat_ofNat_of_lt hmod64
      let st0 := toMState g.shared (g.locals i)
      let regs1 := upd (st0.regs) rMarker (g.shared.cells (h % C)).marker
      let regs2 := upd regs1 rPayload (g.shared.cells (h % C)).payload
      let st' := { st0 with regs := regs2 }
      have hcellEq : (toMState g.shared (g.locals i)).cells
          ((toMState g.shared (g.locals i)).regs rSlot).toNat =
          g.shared.cells (h % C) := by
        show g.shared.cells ((g.locals i).regs rSlot).toNat = g.shared.cells (h % C)
        rw [hslotNat]
      have hst : opStep popProgram 1 1 (toMState g.shared (g.locals i)) =
          .running 1 2 st' := by
        simp [opStep, popProgram, execOp, eval, st', st0, regs1, regs2, hcellEq]
      have hgshare : g'.shared = g.shared := by
        have hs := hstep
        simp only [GStep, programOf, hk, hp, hst] at hs
        rw [hs]
        simp [Shared.after, st', st0, regs1, regs2, toMState]
      obtain ⟨s', hg', hev | ⟨hs, hsh⟩⟩ :=
        gstep_sim hi hg hC hpow hCmax hbound hlimitC hstep
      · exfalso
        obtain ⟨a, res, hev⟩ := hev
        have hmem : Shared.toMem g'.shared = Shared.toMem g.shared := by rw [hgshare]
        exact (EventStep.mem_ne hev) hmem.symm
      · have hsEq : s' = s := hs
        subst s'
        refine ⟨s, .stutter, hg', hi, ?_, Or.inr ⟨hempty, rfl, hphase⟩⟩
        exact Effect.stutter (SharedRef.ref hg.hshared) rfl (by rw [hsh])



theorem push_cas_tag {n C limit k : Nat} {kind : Fin n → Kind}
    {s : AbsState UInt64} {g g' : GState n} {i : Fin n}
    (hi : Inv C limit s) (hg : GRef C limit kind s g)
    (hC : 0 < C) (hpow : C = 2 ^ k) (hCmax : C ≤ 2 ^ 24)
    (hbound : limit < 2 ^ 63) (hlimitC : limit + C ≤ 2 ^ 63)
    (hk : kind i = .push)
    (hp0 : (g.locals i).phase = Phase.running 3 2)
    (hstep : GStep kind g i g') :
    ∃ s' tag, GRef C limit kind s' g' ∧ Inv C limit s' ∧
      Effect 0 C limit hC s (Shared.toMem g.shared) s' (Shared.toMem g'.shared) tag ∧
      ((∃ h : Nat, tag = .event (.push (g.locals i).value) (.pushed h) ∧
          (g'.locals i).phase = Phase.running 3 3 ∧ (g'.locals i).regs rOk = 1 ∧
          (g'.locals i).regs rHint = UInt64.ofNat h) ∨
       (tag = .stutter ∧ (g'.locals i).phase = Phase.running 3 3 ∧
          (g'.locals i).regs rOk = 0)) := by
  have hpinv : PushInv C limit s g.shared (g.locals i) (Phase.running 3 2) := by
    have h1 := hg.hlocal i
    simp only [ThreadInv, hk, hp0] at h1
    exact h1
  cases hpinv with
  | cas h hp =>
    have hmodle : h % C ≤ h := Nat.mod_le h C
    have hmod64 : h % C < 2 ^ 64 := by
      have h1 : h ≤ s.w := hp.hintLe
      have h2 : s.w ≤ s.W := hi.hw_le
      have h3 : s.W ≤ limit := hi.hlimit
      have h4 : limit < 2 ^ 64 := by omega
      omega
    have hslotNat : ((toMState g.shared (g.locals i)).regs rSlot).toNat = h % C := by
      show ((g.locals i).regs rSlot).toNat = h % C
      rw [hp.slotEq]
      exact uint64_toNat_ofNat_of_lt hmod64
    by_cases hsucc : (toMState g.shared (g.locals i)).cells
          ((toMState g.shared (g.locals i)).regs rSlot).toNat =
        { marker := (toMState g.shared (g.locals i)).regs rMarker,
          payload := (toMState g.shared (g.locals i)).regs rPayload }
    · let cnew : KCell :=
        { marker := (toMState g.shared (g.locals i)).regs rTmp0,
          payload := (toMState g.shared (g.locals i)).regs rTmp1 }
      let st1 : MState := { toMState g.shared (g.locals i) with
        cells := upd (toMState g.shared (g.locals i)).cells
          ((toMState g.shared (g.locals i)).regs rSlot).toNat cnew,
        regs := upd (toMState g.shared (g.locals i)).regs rOk 1 }
      have hst1 : opStep pushProgram 3 2 (toMState g.shared (g.locals i)) =
          .running 3 3 st1 := by
        simp [opStep, pushProgram, execOp, eval, hsucc, st1, cnew]
      obtain ⟨st', hst', hev⟩ :=
        pushCas_event_of_success hi hg.hshared hC hpow hbound hp.hlim hp hsucc
      have hstEq : st' = st1 := by
        rw [hst1] at hst'
        injection hst' with _ _ hh
        exact hh.symm
      subst hstEq
      let loc' : Local := { (g.locals i).after st1 with phase := Phase.running 3 3 }
      have hg' : g' = { shared := g.shared.after st1, locals := updLocal g.locals i loc' } := by
        have hs := hstep
        simp only [GStep, programOf, hk, hp0, hst1, loc'] at hs
        exact hs
      have hshared : SharedRef C limit (pushState s (g.locals i).value) (g.shared.after st1) := by
        have href : Ref 0 C (pushState s (g.locals i).value)
            (Shared.toMem (g.shared.after st1)) := EventStep.ref hev
        exact SharedRef.after_shared hg.hshared href
      have hgref : GRef C limit kind (pushState s (g.locals i).value) g' := by
        refine ⟨?_, ?_⟩
        · rw [hg']; exact hshared
        · intro j
          by_cases hj : j = i
          · subst j
            simp only [hg', updLocal]
            simp only [if_true]
            simp only [ThreadInv, hk]
            refine PushInv.casOk h ?_ ?_ ?_ ?_ ?_
            · simp [loc']
            · -- rOk = 1
              change ({ (g.locals i).after st1 with phase := Phase.running 3 3 } : Local).regs rOk ≠ 0
              simp [Local.after, st1, upd, toMState, rOk]
            · -- hint register
              simpa [loc', Local.after, st1, upd, rHint, rOk, toMState] using hp.hintEq
            · -- hint provenance
              simpa [pushState] using hp.hintLe
            · -- marker above 2h
              rw [EventStep.push_mem hev]
              simp [Mem.setCell, fullCell]
          · have hji : ¬ j = i := hj
            simp only [hg', updLocal, if_neg hji]
            exact ThreadInv.mono (hg.hlocal j) (EventStep.w_mono hev)
              (EventStep.r_mono hev) (fun k => EventStep.cell_marker_mono hev k)
      have hphase : (g'.locals i).phase = Phase.running 3 3 := by
        rw [hg']
        simp [updLocal, Local.after, loc']
      have hok : (g'.locals i).regs rOk = 1 := by
        rw [hg']
        simp [updLocal, Local.after, loc', st1, upd, toMState, rOk]
      have hlinkH : (g'.locals i).regs rHint = UInt64.ofNat h := by
        rw [hg']
        simpa [updLocal, if_true, Local.after, loc', st1, upd, toMState, rHint, rOk] using hp.hintEq
      have hev' : EventStep 0 C limit hC s (Shared.toMem g.shared)
          (some (.push (g.locals i).value)) (some (.pushed h))
          (pushState s (g.locals i).value) (Shared.toMem g'.shared) := by
        simpa [hg'] using hev
      exact ⟨pushState s (g.locals i).value, .event (.push (g.locals i).value) (.pushed h),
        hgref, EventStep.inv_some hi hev', Effect.event (.push (g.locals i).value) (.pushed h) hev',
        Or.inl ⟨h, rfl, hphase, hok, hlinkH⟩⟩
    · let st1f : MState := { toMState g.shared (g.locals i) with
        regs := upd (toMState g.shared (g.locals i)).regs rOk 0 }
      have hst1f : opStep pushProgram 3 2 (toMState g.shared (g.locals i)) =
          .running 3 3 st1f := by
        simp [opStep, pushProgram, execOp, eval, hsucc, st1f]
      let loc' : Local := { (g.locals i).after st1f with phase := Phase.running 3 3 }
      have hg' : g' = { shared := g.shared.after st1f, locals := updLocal g.locals i loc' } := by
        have hs := hstep
        simp only [GStep, programOf, hk, hp0, hst1f, loc'] at hs
        exact hs
      have hshared : SharedRef C limit s (g.shared.after st1f) := by
        rw [show g.shared.after st1f = g.shared by simp [Shared.after, st1f, toMState]]
        exact hg.hshared
      have hgref : GRef C limit kind s g' := by
        refine ⟨?_, ?_⟩
        · rw [hg']; exact hshared
        · intro j
          by_cases hj : j = i
          · subst j
            simp only [hg', updLocal]
            simp only [if_true]
            simp only [ThreadInv, hk]
            refine PushInv.casFail ?_ ?_
            · simp [loc']
            · simp [loc', Local.after, st1f, upd, rHint, rOk, toMState]
          · have hji : ¬ j = i := hj
            simp only [hg', updLocal, if_neg hji]
            exact hg.hlocal j
      have hphase : (g'.locals i).phase = Phase.running 3 3 := by
        rw [hg']
        simp [updLocal, Local.after, loc']
      have hok : (g'.locals i).regs rOk = 0 := by
        rw [hg']
        simp only [updLocal, if_true, loc']
        change ({ (g.locals i).after st1f with phase := Phase.running 3 3 } : Local).regs rOk = 0
        simp [Local.after, st1f, upd, toMState, rOk]
      exact ⟨s, .stutter, hgref, hi,
        Effect.stutter (SharedRef.ref hg.hshared) rfl (by rw [hg']; simp [Shared.after, st1f, toMState]),
        Or.inr ⟨rfl, hphase, hok⟩⟩



theorem pop_cas_tag {n C limit k : Nat} {kind : Fin n → Kind}
    {s : AbsState UInt64} {g g' : GState n} {i : Fin n}
    (hi : Inv C limit s) (hg : GRef C limit kind s g)
    (hC : 0 < C) (hpow : C = 2 ^ k) (hCmax : C ≤ 2 ^ 24)
    (hbound : limit < 2 ^ 63) (hlimitC : limit + C ≤ 2 ^ 63)
    (hk : kind i = .pop)
    (hp0 : (g.locals i).phase = Phase.running 7 2)
    (hstep : GStep kind g i g') :
    ∃ s' tag, GRef C limit kind s' g' ∧ Inv C limit s' ∧
      Effect 0 C limit hC s (Shared.toMem g.shared) s' (Shared.toMem g'.shared) tag ∧
      ((∃ (h : Nat) (p : UInt64), tag = .event .pop (.popped h p) ∧
          (g'.locals i).phase = Phase.running 7 3 ∧ (g'.locals i).regs rOk = 1 ∧
          (g'.locals i).regs rHint = UInt64.ofNat h ∧ (g'.locals i).regs rPayload = p) ∨
       (tag = .stutter ∧ (g'.locals i).phase = Phase.running 7 3 ∧
          (g'.locals i).regs rOk = 0)) := by
  have hpinv : PopInv C limit s g.shared (g.locals i) (Phase.running 7 2) := by
    have h1 := hg.hlocal i
    simp only [ThreadInv, hk, hp0] at h1
    exact h1
  cases hpinv with
  | cas h hp =>
    have hmodle : h % C ≤ h := Nat.mod_le h C
    have hmod64 : h % C < 2 ^ 64 := by
      have h1 : h ≤ s.r := hp.hintLe
      have h2 : s.r ≤ s.R := hi.hr_le
      have h3 : s.R ≤ s.W := hi.hR_le_W
      have h4 : s.W ≤ limit := hi.hlimit
      have h5 : limit < 2 ^ 64 := by omega
      omega
    have hslotNat : ((toMState g.shared (g.locals i)).regs rSlot).toNat = h % C := by
      show ((g.locals i).regs rSlot).toNat = h % C
      rw [hp.slotEq]
      exact uint64_toNat_ofNat_of_lt hmod64
    by_cases hsucc : (toMState g.shared (g.locals i)).cells
          ((toMState g.shared (g.locals i)).regs rSlot).toNat =
        { marker := (toMState g.shared (g.locals i)).regs rMarker,
          payload := (toMState g.shared (g.locals i)).regs rPayload }
    · let cnew : KCell :=
        { marker := (toMState g.shared (g.locals i)).regs rTmp0,
          payload := (toMState g.shared (g.locals i)).regs rTmp1 }
      let st1 : MState := { toMState g.shared (g.locals i) with
        cells := upd (toMState g.shared (g.locals i)).cells
          ((toMState g.shared (g.locals i)).regs rSlot).toNat cnew,
        regs := upd (toMState g.shared (g.locals i)).regs rOk 1 }
      have hst1 : opStep popProgram 7 2 (toMState g.shared (g.locals i)) =
          .running 7 3 st1 := by
        simp [opStep, popProgram, execOp, eval, hsucc, st1, cnew]
      obtain ⟨st', hst', hev, hpay⟩ :=
        popCas_event_of_success (k := k) hi hg.hshared hC hCmax hbound hlimitC hp.hlim hp hsucc
      have hstEq : st' = st1 := by
        rw [hst1] at hst'
        injection hst' with _ _ hh
        exact hh.symm
      subst hstEq
      let loc' : Local := { (g.locals i).after st1 with phase := Phase.running 7 3 }
      have hg' : g' = { shared := g.shared.after st1, locals := updLocal g.locals i loc' } := by
        have hs := hstep
        simp only [GStep, programOf, hk, hp0, hst1, loc'] at hs
        exact hs
      have hshared : SharedRef C limit (popState s) (g.shared.after st1) := by
        have href : Ref 0 C (popState s) (Shared.toMem (g.shared.after st1)) := EventStep.ref hev
        exact SharedRef.after_shared hg.hshared href
      have hgref : GRef C limit kind (popState s) g' := by
        refine ⟨?_, ?_⟩
        · rw [hg']; exact hshared
        · intro j
          by_cases hj : j = i
          · subst j
            simp only [hg', updLocal]
            simp only [if_true, ThreadInv, hk]
            refine PopInv.casOk h ?_ ?_ ?_ ?_ ?_
            · simp [loc']
            · simp [loc', Local.after, st1, upd, rHint, rOk, toMState]
            · simpa [loc', Local.after, st1, upd, rHint, rOk, toMState] using hp.hintEq
            · simpa [popState] using hp.hintLe
            · rw [EventStep.pop_mem hev]
              simp [Mem.setCell, emptyCell]
              omega
          · have hji : ¬ j = i := hj
            simp only [hg', updLocal, if_neg hji]
            exact ThreadInv.mono (hg.hlocal j) (EventStep.w_mono hev)
              (EventStep.r_mono hev) (fun k => EventStep.cell_marker_mono hev k)
      have hphase : (g'.locals i).phase = Phase.running 7 3 := by
        rw [hg']
        simp [updLocal, Local.after, loc']
      have hok : (g'.locals i).regs rOk = 1 := by
        rw [hg']
        simp [updLocal, Local.after, loc', st1, upd, toMState, rOk]
      have hlinkH : (g'.locals i).regs rHint = UInt64.ofNat h := by
        rw [hg']
        simpa [updLocal, if_true, Local.after, loc', st1, upd, toMState, rHint, rOk] using hp.hintEq
      have hlinkP : (g'.locals i).regs rPayload = (s.val h).getD 0 := by
        rw [hg']
        simpa [updLocal, if_true, Local.after, loc', st1, upd, toMState, rPayload, rOk] using hpay
      have hev' : EventStep 0 C limit hC s (Shared.toMem g.shared)
          (some .pop) (some (.popped h ((s.val h).getD 0)))
          (popState s) (Shared.toMem g'.shared) := by
        simpa [hg'] using hev
      exact ⟨popState s, .event .pop (.popped h ((s.val h).getD 0)),
        hgref, EventStep.inv_some hi hev', Effect.event .pop (.popped h ((s.val h).getD 0)) hev',
        Or.inl ⟨h, (s.val h).getD 0, rfl, hphase, hok, hlinkH, hlinkP⟩⟩
    · let st1f : MState := { toMState g.shared (g.locals i) with
        regs := upd (toMState g.shared (g.locals i)).regs rOk 0 }
      have hst1f : opStep popProgram 7 2 (toMState g.shared (g.locals i)) =
          .running 7 3 st1f := by
        simp [opStep, popProgram, execOp, eval, hsucc, st1f]
      let loc' : Local := { (g.locals i).after st1f with phase := Phase.running 7 3 }
      have hg' : g' = { shared := g.shared.after st1f, locals := updLocal g.locals i loc' } := by
        have hs := hstep
        simp only [GStep, programOf, hk, hp0, hst1f, loc'] at hs
        exact hs
      have hshared : SharedRef C limit s (g.shared.after st1f) := by
        rw [show g.shared.after st1f = g.shared by simp [Shared.after, st1f, toMState]]
        exact hg.hshared
      have hgref : GRef C limit kind s g' := by
        refine ⟨?_, ?_⟩
        · rw [hg']; exact hshared
        · intro j
          by_cases hj : j = i
          · subst j
            simp only [hg', updLocal]
            simp only [if_true, ThreadInv, hk]
            refine PopInv.casFail ?_ ?_
            · simp [loc']
            · simp [loc', Local.after, st1f, upd, rHint, rOk, toMState]
          · have hji : ¬ j = i := hj
            simp only [hg', updLocal, if_neg hji]
            exact hg.hlocal j
      have hphase : (g'.locals i).phase = Phase.running 7 3 := by
        rw [hg']
        simp [updLocal, Local.after, loc']
      have hok : (g'.locals i).regs rOk = 0 := by
        rw [hg']
        simp only [updLocal, if_true, loc']
        change ({ (g.locals i).after st1f with phase := Phase.running 7 3 } : Local).regs rOk = 0
        simp [Local.after, st1f, upd, toMState, rOk]
      exact ⟨s, .stutter, hgref, hi,
        Effect.stutter (SharedRef.ref hg.hshared) rfl (by rw [hg']; simp [Shared.after, st1f, toMState]),
        Or.inr ⟨rfl, hphase, hok⟩⟩



theorem push_help_tag {n C limit k : Nat} {kind : Fin n → Kind}
    {s : AbsState UInt64} {g g' : GState n} {i : Fin n}
    (hi : Inv C limit s) (hg : GRef C limit kind s g)
    (hC : 0 < C) (hpow : C = 2 ^ k) (hCmax : C ≤ 2 ^ 24)
    (hbound : limit < 2 ^ 63) (hlimitC : limit + C ≤ 2 ^ 63)
    (hk : kind i = .push)
    (hp0 : (g.locals i).phase = Phase.running 7 1)
    (hstep : GStep kind g i g') :
    ∃ s' tag, GRef C limit kind s' g' ∧ Inv C limit s' ∧
      Effect 0 C limit hC s (Shared.toMem g.shared) s' (Shared.toMem g'.shared) tag ∧
      ((tag = .event .helpW .helped ∧ (g'.locals i).phase = Phase.running 7 2) ∨
       (tag = .stutter ∧ (g'.locals i).phase = Phase.running 7 2)) := by
  have hpinv : PushInv C limit s g.shared (g.locals i) (Phase.running 7 1) := by
    have h1 := hg.hlocal i
    simp only [ThreadInv, hk, hp0] at h1
    exact h1
  cases hpinv with
  | help2 h hpc hp =>
    have hh63 : h < 2 ^ 63 :=
      Nat.lt_of_le_of_lt (Nat.le_trans hp.hintLe (Nat.le_trans hi.hw_le hi.hlimit)) hbound
    have h64 : h < 2 ^ 64 := Nat.lt_trans hh63 (by decide : 2 ^ 63 < 2 ^ 64)
    have h2h1 : h + 1 < 2 ^ 64 := by
      have hle := Nat.succ_le_of_lt hh63
      exact Nat.lt_of_le_of_lt hle (by decide : 2 ^ 63 < 2 ^ 64)
    by_cases hsucc : (toMState g.shared (g.locals i)).hintW =
        (toMState g.shared (g.locals i)).regs rHint
    · have hhint : g.shared.hintW.toNat = h := by
        have hw : g.shared.hintW = UInt64.ofNat h := by
          have hh := hsucc
          simp only [toMState] at hh
          rw [hp.hintReg] at hh
          exact hh
        rw [hw]
        exact uint64_toNat_ofNat_of_lt h64
      obtain ⟨st', hexec, hev⟩ := pushHint_event_of_success hi hg.hshared hC hp hhint h2h1
      have hst : opStep pushProgram 7 1 (toMState g.shared (g.locals i)) = .running 7 2 st' := by
        simp [opStep, pushProgram, hexec]
      let loc' : Local := { (g.locals i).after st' with phase := Phase.running 7 2 }
      have hg' : g' = { shared := g.shared.after st', locals := updLocal g.locals i loc' } := by
        have hs := hstep
        simp only [GStep, programOf, hk, hp0, hst, loc'] at hs
        exact hs
      have hshared : SharedRef C limit { s with w := s.w + 1 } (g.shared.after st') := by
        have href : Ref 0 C { s with w := s.w + 1 } (Shared.toMem (g.shared.after st')) :=
          EventStep.ref hev
        exact SharedRef.after_shared hg.hshared href
      have hgref : GRef C limit kind { s with w := s.w + 1 } g' := by
        refine ⟨?_, ?_⟩
        · rw [hg']; exact hshared
        · intro j
          by_cases hj : j = i
          · subst j
            simp only [hg', updLocal]
            simp only [if_true, ThreadInv, hk]
            refine PushInv.help3 ?_
            simp [loc']
          · have hji : ¬ j = i := hj
            simp only [hg', updLocal, if_neg hji]
            exact ThreadInv.mono (hg.hlocal j) (EventStep.w_mono hev)
              (EventStep.r_mono hev) (fun k => EventStep.cell_marker_mono hev k)
      have hphase : (g'.locals i).phase = Phase.running 7 2 := by
        rw [hg']
        simp [updLocal, Local.after, loc']
      have hev' : EventStep 0 C limit hC s (Shared.toMem g.shared)
          (some .helpW) (some .helped)
          { s with w := s.w + 1 } (Shared.toMem g'.shared) := by
        simpa [hg'] using hev
      exact ⟨{ s with w := s.w + 1 }, .event .helpW .helped, hgref,
        EventStep.inv_some hi hev', Effect.event .helpW .helped hev',
        Or.inl ⟨rfl, hphase⟩⟩
    · let st1 : MState := { toMState g.shared (g.locals i) with
        regs := upd (toMState g.shared (g.locals i)).regs rOk 0 }
      have hst : opStep pushProgram 7 1 (toMState g.shared (g.locals i)) = .running 7 2 st1 := by
        simp [opStep, pushProgram, execOp, eval, hsucc, st1]
      let loc' : Local := { (g.locals i).after st1 with phase := Phase.running 7 2 }
      have hg' : g' = { shared := g.shared.after st1, locals := updLocal g.locals i loc' } := by
        have hs := hstep
        simp only [GStep, programOf, hk, hp0, hst, loc'] at hs
        exact hs
      have hshared : SharedRef C limit s (g.shared.after st1) := by
        rw [show g.shared.after st1 = g.shared by simp [Shared.after, st1, toMState]]
        exact hg.hshared
      have hgref : GRef C limit kind s g' := by
        refine ⟨?_, ?_⟩
        · rw [hg']; exact hshared
        · intro j
          by_cases hj : j = i
          · subst j
            simp only [hg', updLocal]
            simp only [if_true, ThreadInv, hk]
            refine PushInv.help3 ?_
            simp [loc']
          · have hji : ¬ j = i := hj
            simp only [hg', updLocal, if_neg hji]
            exact hg.hlocal j
      have hphase : (g'.locals i).phase = Phase.running 7 2 := by
        rw [hg']
        simp [updLocal, Local.after, loc']
      exact ⟨s, .stutter, hgref, hi,
        Effect.stutter (SharedRef.ref hg.hshared) rfl (by rw [hg']; simp [Shared.after, st1, toMState]),
        Or.inr ⟨rfl, hphase⟩⟩


/-! ## Effect monotonicity and stage computations -/

/-- Every effect preserves the hint and cell-marker order. -/
theorem Effect.mono {C limit : Nat} {hC : 0 < C} {s : AbsState UInt64} {m : Mem UInt64}
    {s' : AbsState UInt64} {m' : Mem UInt64} {tag : StepTag UInt64}
    (h : Effect 0 C limit hC s m s' m' tag) :
    s.w ≤ s'.w ∧ s.r ≤ s'.r ∧ ∀ j, (m.cells j).marker ≤ (m'.cells j).marker := by
  cases h with
  | stutter hm hs hmem =>
      cases hs
      cases hmem
      exact ⟨Nat.le_refl _, Nat.le_refl _, fun j => Nat.le_refl _⟩
  | event a r hev =>
      exact ⟨EventStep.w_mono hev, EventStep.r_mono hev, EventStep.cell_marker_mono hev⟩
  | obs k hm guard hs hmem =>
      cases hs
      cases hmem
      exact ⟨Nat.le_refl _, Nat.le_refl _, fun j => Nat.le_refl _⟩
  | ret status hm hs hmem =>
      cases hs
      cases hmem
      exact ⟨Nat.le_refl _, Nat.le_refl _, fun j => Nat.le_refl _⟩

/-- Stages are determined by the phase and the three scanned registers. -/
theorem pushStage_congr {C : Nat} {loc loc' : Local}
    (hp : loc.phase = loc'.phase)
    (hm : loc.regs rMarker = loc'.regs rMarker)
    (hh : loc.regs rHint = loc'.regs rHint)
    (ho : loc.regs rOk = loc'.regs rOk) :
    pushStage C loc' = pushStage C loc := by
  simp [pushStage, hp, hm, hh, ho]

/-- The load step preserves the push stage (the marker and hint registers
are untouched and the two phases test the same condition). -/
theorem pushStage_load {C : Nat} {loc loc' : Local}
    (h1 : loc.phase = Phase.running 1 2) (h2 : loc'.phase = Phase.running 1 3)
    (hm : loc.regs rMarker = loc'.regs rMarker)
    (hh : loc.regs rHint = loc'.regs rHint) :
    pushStage C loc' = pushStage C loc := by
  simp [pushStage, h1, h2, hm, hh]

/-- The ready branch of the position test is `pre` on both sides. -/
theorem pushStage_pos_ready {C : Nat} {loc loc' : Local} (hC : 0 < C)
    (h1 : loc.phase = Phase.running 1 3) (h2 : loc'.phase = Phase.running 2 0)
    (hq : (loc.regs rMarker).toNat / 2 = (loc.regs rHint).toNat) :
    pushStage C loc' = pushStage C loc := by
  have hcond : ¬ ((loc.regs rMarker).toNat / 2 + C = (loc.regs rHint).toNat) := by
    omega
  simp [pushStage, h1, h2, hcond]

/-- The `ahead` branch of the position test keeps the same full-snapshot
condition. -/
theorem pushStage_pos_ahead {C : Nat} {loc loc' : Local}
    (h1 : loc.phase = Phase.running 1 3) (h2 : loc'.phase = Phase.running 5 0)
    (hm : loc.regs rMarker = loc'.regs rMarker)
    (hh : loc.regs rHint = loc'.regs rHint) :
    pushStage C loc' = pushStage C loc := by
  simp [pushStage, h1, h2, hm, hh]

/-- The lagging-hint help branch is `pre` on both sides. -/
theorem pushStage_ahead_help {C : Nat} {loc loc' : Local} (hC : 0 < C)
    (h1 : loc.phase = Phase.running 5 1) (h2 : loc'.phase = Phase.running 8 0)
    (hlt : (loc.regs rHint).toNat < (loc.regs rMarker).toNat / 2) :
    pushStage C loc' = pushStage C loc := by
  have hcond : ¬ ((loc.regs rMarker).toNat / 2 + C = (loc.regs rHint).toNat) := by
    omega
  simp [pushStage, h1, h2, hcond]

/-- Stages are determined by the phase and the scanned registers. -/
theorem popStage_congr {C : Nat} {loc loc' : Local}
    (hp : loc.phase = loc'.phase)
    (hm : loc.regs rMarker = loc'.regs rMarker)
    (hh : loc.regs rHint = loc'.regs rHint)
    (ho : loc.regs rOk = loc'.regs rOk) :
    popStage C loc' = popStage C loc := by
  simp [popStage, hp, hm, hh, ho]

theorem popStage_load {C : Nat} {loc loc' : Local}
    (h1 : loc.phase = Phase.running 1 2) (h2 : loc'.phase = Phase.running 1 3)
    (hm : loc.regs rMarker = loc'.regs rMarker)
    (hh : loc.regs rHint = loc'.regs rHint) :
    popStage C loc' = popStage C loc := by
  simp [popStage, h1, h2, hm, hh]

theorem popStage_pos_ready {C : Nat} {loc loc' : Local}
    (h1 : loc.phase = Phase.running 1 3) (h2 : loc'.phase = Phase.running 2 0)
    (hm : loc.regs rMarker = loc'.regs rMarker)
    (hh : loc.regs rHint = loc'.regs rHint) :
    popStage C loc' = popStage C loc := by
  simp [popStage, h1, h2, hm, hh]

theorem popStage_ready_even {C : Nat} {loc loc' : Local}
    (h1 : loc.phase = Phase.running 2 0) (h2 : loc'.phase = Phase.running 2 1)
    (hm : loc.regs rMarker = loc'.regs rMarker)
    (hh : loc.regs rHint = loc'.regs rHint) :
    popStage C loc' = popStage C loc := by
  simp [popStage, h1, h2, hm, hh]

theorem popStage_pos_ahead {C : Nat} {loc loc' : Local}
    (h1 : loc.phase = Phase.running 1 3) (h2 : loc'.phase = Phase.running 5 0)
    (hne : (loc.regs rMarker).toNat / 2 ≠ (loc.regs rHint).toNat) :
    popStage C loc' = popStage C loc := by
  have hcond : ¬ ((loc.regs rMarker).toNat / 2 = (loc.regs rHint).toNat ∧
      (loc.regs rMarker).toNat % 2 = 0) := fun h => hne h.1
  simp [popStage, h1, h2, hcond]

theorem popStage_even_empty {C : Nat} {loc loc' : Local}
    (h1 : loc.phase = Phase.running 2 1) (h2 : loc'.phase = Phase.running 3 0)
    (heq : (loc.regs rMarker).toNat / 2 = (loc.regs rHint).toNat)
    (heven : (loc.regs rMarker).toNat % 2 = 0) :
    popStage C loc' = popStage C loc := by
  simp [popStage, h1, h2, heq, heven]

theorem popStage_odd_cas {C : Nat} {loc loc' : Local}
    (h1 : loc.phase = Phase.running 2 1) (h2 : loc'.phase = Phase.running 7 0)
    (hodd : (loc.regs rMarker).toNat % 2 ≠ 0) :
    popStage C loc' = popStage C loc := by
  have hcond : ¬ ((loc.regs rMarker).toNat / 2 = (loc.regs rHint).toNat ∧
      (loc.regs rMarker).toNat % 2 = 0) := fun h => hodd h.2
  simp [popStage, h1, h2, hcond]

theorem pushStage_casFail {C : Nat} {loc loc' : Local}
    (h1 : loc.phase = Phase.running 3 3) (h2 : loc'.phase = Phase.running 0 0)
    (hok : loc.regs rOk = 0) :
    pushStage C loc' = pushStage C loc := by
  simp [pushStage, h1, h2, hok]

theorem pushStage_casOk {C : Nat} {loc loc' : Local}
    (h1 : loc.phase = Phase.running 3 3) (h2 : loc'.phase = Phase.running 4 0)
    (hok : loc.regs rOk ≠ 0) :
    pushStage C loc' = pushStage C loc := by
  simp [pushStage, h1, h2, hok]

theorem popStage_casFail {C : Nat} {loc loc' : Local}
    (h1 : loc.phase = Phase.running 7 3) (h2 : loc'.phase = Phase.running 0 0)
    (hok : loc.regs rOk = 0) :
    popStage C loc' = popStage C loc := by
  simp [popStage, h1, h2, hok]

theorem popStage_casOk {C : Nat} {loc loc' : Local}
    (h1 : loc.phase = Phase.running 7 3) (h2 : loc'.phase = Phase.running 4 0)
    (hok : loc.regs rOk ≠ 0) :
    popStage C loc' = popStage C loc := by
  simp [popStage, h1, h2, hok]

/-- The two `ahead` phases test the same full-snapshot condition. -/
theorem pushStage_ahead_step {C : Nat} {loc loc' : Local}
    (h1 : loc.phase = Phase.running 5 0) (h2 : loc'.phase = Phase.running 5 1)
    (hm : loc.regs rMarker = loc'.regs rMarker)
    (hh : loc.regs rHint = loc'.regs rHint) :
    pushStage C loc' = pushStage C loc := by
  simp [pushStage, h1, h2, hm, hh]


theorem push_cert {C limit k : Nat} {s : AbsState UInt64} {sh : Shared} {loc : Local}
    {pc oi : Nat} {r : OpResult}
    (hi : Inv C limit s) (hs : SharedRef C limit s sh)
    (hC : 0 < C) (hpow : C = 2 ^ k) (hbound : limit < 2 ^ 63)
    (hlimitC : limit + C ≤ 2 ^ 63)
    (hinv : PushInv C limit s sh loc (Phase.running pc oi))
    (hnot : ¬ PushSelected loc)
    (hstep : opStep pushProgram pc oi (toMState sh loc) = r) :
    PushCert C limit hC s sh loc r := by
  cases hinv with
  | entry hpc =>
    obtain ⟨s', sh', loc', hafter, hinv', hsh', hd⟩ :=
      push_local_step hi hs hC hpow hbound hlimitC hpc
        (PushInv.entry hpc) hstep
    cases hstep
    obtain ⟨hshEq, hlocEq⟩ := hafter
    have hstut : s' = s ∧ sh' = sh := by
      rcases hd with ⟨a, res, hev⟩ | hh
      · exfalso
        exact (EventStep.mem_ne hev) (by rw [hshEq]; simp [Shared.after, Shared.toMem, toMState, execOp])
      · exact hh
    obtain ⟨hsEq, hshEq'⟩ := hstut
    subst s'
    subst sh'
    refine ⟨s, sh, loc', .stutter, ⟨rfl, hlocEq⟩, hinv', hsh', hi, ?_, ?_⟩
    · exact Effect.stutter (SharedRef.ref hs) rfl rfl
    · simp [StepClass, threadStage, pushStage, Stage.status, hpc, hlocEq, Local.after, toMState, execOp, upd, rMarker, rHint, rPos, rOk]
  | hint h hpc hintEq hintLe => exact absurd (by simp [PushSelected, hpc]) hnot
  | check h hpc hintEq hintLe hlim =>
    obtain ⟨s', sh', loc', hafter, hinv', hsh', hd⟩ :=
      push_local_step hi hs hC hpow hbound hlimitC hpc
        (PushInv.check h hpc hintEq hintLe hlim) hstep
    cases hstep
    obtain ⟨hshEq, hlocEq⟩ := hafter
    have hstut : s' = s ∧ sh' = sh := by
      rcases hd with ⟨a, res, hev⟩ | hh
      · exfalso
        exact (EventStep.mem_ne hev) (by rw [hshEq]; simp [Shared.after, Shared.toMem, toMState, execOp])
      · exact hh
    obtain ⟨hsEq, hshEq'⟩ := hstut
    subst s'
    subst sh'
    refine ⟨s, sh, loc', .stutter, ⟨rfl, hlocEq⟩, hinv', hsh', hi, ?_, ?_⟩
    · exact Effect.stutter (SharedRef.ref hs) rfl rfl
    · simp [StepClass, threadStage, pushStage, Stage.status, hpc, hlocEq, Local.after, toMState, execOp, upd, rMarker, rHint, rPos, rOk]
  | slot h hpc hintEq hintLe hlim slotEq => exact absurd (by simp [PushSelected, hpc]) hnot
  | load h m q hpc hintEq hintLe hlim slotEq markerEq hm64 markerMono hq hq63 hfull =>
    obtain ⟨s', sh', loc', hafter, hinv', hsh', hd⟩ :=
      push_local_step hi hs hC hpow hbound hlimitC hpc
        (PushInv.load h m q hpc hintEq hintLe hlim slotEq markerEq hm64 markerMono hq hq63 hfull) hstep
    cases hstep
    obtain ⟨hshEq, hlocEq⟩ := hafter
    have hstut : s' = s ∧ sh' = sh := by
      rcases hd with ⟨a, res, hev⟩ | hh
      · exfalso
        exact (EventStep.mem_ne hev) (by rw [hshEq]; simp [Shared.after, Shared.toMem, toMState, execOp])
      · exact hh
    obtain ⟨hsEq, hshEq'⟩ := hstut
    subst s'
    subst sh'
    refine ⟨s, sh, loc', .stutter, ⟨rfl, hlocEq⟩, hinv', hsh', hi, ?_, ?_⟩
    · exact Effect.stutter (SharedRef.ref hs) rfl rfl
    · rw [StepClass]
      refine Or.inl ⟨rfl, ?_⟩
      rw [threadStage, threadStage]
      exact pushStage_load (C := C) (loc := loc) (loc' := loc') hpc (by rw [hlocEq])
        (by rw [hlocEq]; rfl) (by rw [hlocEq]; rfl)
  | pos h m q hpc hintEq hintLe hlim slotEq markerEq markerMono posEq hq hq63 hfull =>
    have h64 : h < 2 ^ 64 := by
      have h1 := hintLe
      have h2 := hi.hw_le
      have h3 := hi.hlimit
      omega
    have hq64 : q < 2 ^ 64 := by omega
    by_cases qh : q = h
    · have hcond : (toMState sh loc).regs rPos = (toMState sh loc).regs rHint := by
        show loc.regs rPos = loc.regs rHint
        rw [posEq, hintEq, u64_eq_ofNat_iff hq64 h64]
        exact qh
      have hst : opStep pushProgram 1 3 (toMState sh loc) = .running 2 0 (toMState sh loc) := by
        simp [opStep, pushProgram, eval, hcond]
      rw [hst] at hstep
      cases hstep
      obtain ⟨s', sh', loc', hafter, hinv', hsh', hd⟩ :=
        push_local_step hi hs hC hpow hbound hlimitC hpc
          (PushInv.pos h m q hpc hintEq hintLe hlim slotEq markerEq markerMono posEq hq hq63 hfull) hst
      obtain ⟨hshEq, hlocEq⟩ := hafter
      have hstut : s' = s ∧ sh' = sh := by
        rcases hd with ⟨a, res, hev⟩ | hh
        · exfalso
          exact (EventStep.mem_ne hev) (by rw [hshEq]; simp [Shared.after, Shared.toMem, toMState, execOp])
        · exact hh
      obtain ⟨hsEq, hshEq'⟩ := hstut
      subst s'
      subst sh'
      refine ⟨s, sh, loc', .stutter, ⟨rfl, hlocEq⟩, hinv', hsh', hi, ?_, ?_⟩
      · exact Effect.stutter (SharedRef.ref hs) rfl rfl
      · rw [StepClass]
        refine Or.inl ⟨rfl, ?_⟩
        rw [threadStage, threadStage]
        apply pushStage_pos_ready (C := C) hC hpc (by rw [hlocEq])
        have hm64 : m < 2 ^ 64 := by
          have h2 : m / 2 < 2 ^ 63 := by omega
          have h3 := (Nat.div_lt_iff_lt_mul (by decide : 0 < 2)).mp h2
          simpa [Nat.pow_succ, Nat.mul_comm] using h3
        rw [markerEq, hintEq, uint64_toNat_ofNat_of_lt hm64, uint64_toNat_ofNat_of_lt h64]
        omega
    · have hne : (toMState sh loc).regs rPos ≠ (toMState sh loc).regs rHint := by
        show loc.regs rPos ≠ loc.regs rHint
        rw [posEq, hintEq]
        intro hc
        exact qh ((u64_eq_ofNat_iff hq64 h64).mp hc)
      have hst : opStep pushProgram 1 3 (toMState sh loc) = .running 5 0 (toMState sh loc) := by
        simp [opStep, pushProgram, eval, hne]
      rw [hst] at hstep
      cases hstep
      obtain ⟨s', sh', loc', hafter, hinv', hsh', hd⟩ :=
        push_local_step hi hs hC hpow hbound hlimitC hpc
          (PushInv.pos h m q hpc hintEq hintLe hlim slotEq markerEq markerMono posEq hq hq63 hfull) hst
      obtain ⟨hshEq, hlocEq⟩ := hafter
      have hstut : s' = s ∧ sh' = sh := by
        rcases hd with ⟨a, res, hev⟩ | hh
        · exfalso
          exact (EventStep.mem_ne hev) (by rw [hshEq]; simp [Shared.after, Shared.toMem, toMState, execOp])
        · exact hh
      obtain ⟨hsEq, hshEq'⟩ := hstut
      subst s'
      subst sh'
      refine ⟨s, sh, loc', .stutter, ⟨rfl, hlocEq⟩, hinv', hsh', hi, ?_, ?_⟩
      · exact Effect.stutter (SharedRef.ref hs) rfl rfl
      · rw [StepClass]
        refine Or.inl ⟨rfl, ?_⟩
        rw [threadStage, threadStage]
        exact pushStage_pos_ahead (C := C) hpc (by rw [hlocEq])
          (by rw [hlocEq]; rfl) (by rw [hlocEq]; rfl)
  | readyTest h m q hpc hintEq hintLe hlim slotEq markerEq markerMono posEq hq hq63 hfull qeq =>
    obtain ⟨s', sh', loc', hafter, hinv', hsh', hd⟩ :=
      push_local_step hi hs hC hpow hbound hlimitC hpc
        (PushInv.readyTest h m q hpc hintEq hintLe hlim slotEq markerEq markerMono posEq hq hq63 hfull qeq) hstep
    cases hstep
    obtain ⟨hshEq, hlocEq⟩ := hafter
    have hstut : s' = s ∧ sh' = sh := by
      rcases hd with ⟨a, res, hev⟩ | hh
      · exfalso
        exact (EventStep.mem_ne hev) (by rw [hshEq]; simp [Shared.after, Shared.toMem, toMState, execOp])
      · exact hh
    obtain ⟨hsEq, hshEq'⟩ := hstut
    subst s'
    subst sh'
    refine ⟨s, sh, loc', .stutter, ⟨rfl, hlocEq⟩, hinv', hsh', hi, ?_, ?_⟩
    · exact Effect.stutter (SharedRef.ref hs) rfl rfl
    · simp [StepClass, threadStage, pushStage, Stage.status, hpc, hlocEq, Local.after, toMState, execOp, upd, rMarker, rHint, rPos, rOk]
  | evenTest h m q hpc hintEq hintLe hlim slotEq markerEq markerMono posEq hq hq63 hfull qeq tmp0Eq =>
    have hm2 : m % 2 < 2 ^ 64 := by omega
    have h64 : h < 2 ^ 64 := by
      have h1 := hintLe
      have h2 := hi.hw_le
      have h3 := hi.hlimit
      omega
    by_cases hpar : m % 2 = 0
    · have hcond : (toMState sh loc).regs rTmp0 = 0 := by
          show loc.regs rTmp0 = 0
          rw [tmp0Eq, u64_eq_zero_ofNat hm2, hpar]
      have hst : opStep pushProgram 2 1 (toMState sh loc) = .running 3 0 (toMState sh loc) := by
        simp [opStep, pushProgram, eval, hcond]
      rw [hst] at hstep
      cases hstep
      obtain ⟨s', sh', loc', hafter, hinv', hsh', hd⟩ :=
        push_local_step hi hs hC hpow hbound hlimitC hpc
          (PushInv.evenTest h m q hpc hintEq hintLe hlim slotEq markerEq markerMono posEq hq hq63 hfull qeq tmp0Eq) hst
      obtain ⟨hshEq, hlocEq⟩ := hafter
      have hstut : s' = s ∧ sh' = sh := by
        rcases hd with ⟨a, res, hev⟩ | hh
        · exfalso
          exact (EventStep.mem_ne hev) (by rw [hshEq]; simp [Shared.after, Shared.toMem, toMState, execOp])
        · exact hh
      obtain ⟨hsEq, hshEq'⟩ := hstut
      subst s'
      subst sh'
      refine ⟨s, sh, loc', .stutter, ⟨rfl, hlocEq⟩, hinv', hsh', hi, ?_, ?_⟩
      · exact Effect.stutter (SharedRef.ref hs) rfl rfl
      · simp [StepClass, threadStage, pushStage, hpc, hlocEq, Local.after, toMState, execOp, upd, rMarker, rHint, rPos, rOk]
    · have hcond : ¬ ((toMState sh loc).regs rTmp0 = 0) := by
        show ¬ (loc.regs rTmp0 = 0)
        rw [tmp0Eq]
        intro hc
        exact hpar ((u64_eq_zero_ofNat hm2).mp hc)
      have hst : opStep pushProgram 2 1 (toMState sh loc) = .running 7 0 (toMState sh loc) := by
        simp [opStep, pushProgram, eval, hcond]
      rw [hst] at hstep
      cases hstep
      obtain ⟨s', sh', loc', hafter, hinv', hsh', hd⟩ :=
        push_local_step hi hs hC hpow hbound hlimitC hpc
          (PushInv.evenTest h m q hpc hintEq hintLe hlim slotEq markerEq markerMono posEq hq hq63 hfull qeq tmp0Eq) hst
      obtain ⟨hshEq, hlocEq⟩ := hafter
      have hstut : s' = s ∧ sh' = sh := by
        rcases hd with ⟨a, res, hev⟩ | hh
        · exfalso
          exact (EventStep.mem_ne hev) (by rw [hshEq]; simp [Shared.after, Shared.toMem, toMState, execOp])
        · exact hh
      obtain ⟨hsEq, hshEq'⟩ := hstut
      subst s'
      subst sh'
      refine ⟨s, sh, loc', .stutter, ⟨rfl, hlocEq⟩, hinv', hsh', hi, ?_, ?_⟩
      · exact Effect.stutter (SharedRef.ref hs) rfl rfl
      · simp [StepClass, threadStage, pushStage, hpc, hlocEq, Local.after, toMState, execOp, upd, rMarker, rHint, rPos, rOk]
  | cas0 h m q hpc hintEq hintLe hlim slotEq markerEq markerMono posEq hq hq63 hfull qeq heven =>
    obtain ⟨s', sh', loc', hafter, hinv', hsh', hd⟩ :=
      push_local_step hi hs hC hpow hbound hlimitC hpc
        (PushInv.cas0 h m q hpc hintEq hintLe hlim slotEq markerEq markerMono posEq hq hq63 hfull qeq heven) hstep
    cases hstep
    obtain ⟨hshEq, hlocEq⟩ := hafter
    have hstut : s' = s ∧ sh' = sh := by
      rcases hd with ⟨a, res, hev⟩ | hh
      · exfalso
        exact (EventStep.mem_ne hev) (by rw [hshEq]; simp [Shared.after, Shared.toMem, toMState, execOp])
      · exact hh
    obtain ⟨hsEq, hshEq'⟩ := hstut
    subst s'
    subst sh'
    refine ⟨s, sh, loc', .stutter, ⟨rfl, hlocEq⟩, hinv', hsh', hi, ?_, ?_⟩
    · exact Effect.stutter (SharedRef.ref hs) rfl rfl
    · simp [StepClass, threadStage, pushStage, Stage.status, hpc, hlocEq, Local.after, toMState, execOp, upd, rMarker, rHint, rPos, rOk]
  | cas1 h hpc hintEq hintLe hlim slotEq markerEq desMarker =>
    obtain ⟨s', sh', loc', hafter, hinv', hsh', hd⟩ :=
      push_local_step hi hs hC hpow hbound hlimitC hpc
        (PushInv.cas1 h hpc hintEq hintLe hlim slotEq markerEq desMarker) hstep
    cases hstep
    obtain ⟨hshEq, hlocEq⟩ := hafter
    have hstut : s' = s ∧ sh' = sh := by
      rcases hd with ⟨a, res, hev⟩ | hh
      · exfalso
        exact (EventStep.mem_ne hev) (by rw [hshEq]; simp [Shared.after, Shared.toMem, toMState, execOp])
      · exact hh
    obtain ⟨hsEq, hshEq'⟩ := hstut
    subst s'
    subst sh'
    refine ⟨s, sh, loc', .stutter, ⟨rfl, hlocEq⟩, hinv', hsh', hi, ?_, ?_⟩
    · exact Effect.stutter (SharedRef.ref hs) rfl rfl
    · simp [StepClass, threadStage, pushStage, Stage.status, hpc, hlocEq, Local.after, toMState, execOp, upd, rMarker, rHint, rPos, rOk]
  | cas h hp => exact absurd (by simp [PushSelected, hp.hpc]) hnot
  | casFail hpc hok =>
    have hcond : (toMState sh loc).regs rOk = 0 := hok
    have hst : opStep pushProgram 3 3 (toMState sh loc) = .running 0 0 (toMState sh loc) := by
      simp [opStep, pushProgram, eval, hcond]
    rw [hst] at hstep
    cases hstep
    obtain ⟨s', sh', loc', hafter, hinv', hsh', hd⟩ :=
      push_local_step hi hs hC hpow hbound hlimitC hpc (PushInv.casFail hpc hok) hst
    obtain ⟨hshEq, hlocEq⟩ := hafter
    have hstut : s' = s ∧ sh' = sh := by
      rcases hd with ⟨a, res, hev⟩ | hh
      · exfalso
        exact (EventStep.mem_ne hev) (by rw [hshEq]; simp [Shared.after, Shared.toMem, toMState, execOp])
      · exact hh
    obtain ⟨hsEq, hshEq'⟩ := hstut
    subst s'
    subst sh'
    refine ⟨s, sh, loc', .stutter, ⟨rfl, hlocEq⟩, hinv', hsh', hi, ?_, ?_⟩
    · exact Effect.stutter (SharedRef.ref hs) rfl rfl
    · rw [StepClass]
      refine Or.inl ⟨rfl, ?_⟩
      rw [threadStage, threadStage]
      exact pushStage_casFail (C := C) hpc (by rw [hlocEq]) hok
  | casOk h hpc hok hintEq hintLe hmark =>
    have hcond : ¬ ((toMState sh loc).regs rOk = 0) := hok
    have hst : opStep pushProgram 3 3 (toMState sh loc) = .running 4 0 (toMState sh loc) := by
      simp [opStep, pushProgram, eval, hcond]
    rw [hst] at hstep
    cases hstep
    obtain ⟨s', sh', loc', hafter, hinv', hsh', hd⟩ :=
      push_local_step hi hs hC hpow hbound hlimitC hpc (PushInv.casOk h hpc hok hintEq hintLe hmark) hst
    obtain ⟨hshEq, hlocEq⟩ := hafter
    have hstut : s' = s ∧ sh' = sh := by
      rcases hd with ⟨a, res, hev⟩ | hh
      · exfalso
        exact (EventStep.mem_ne hev) (by rw [hshEq]; simp [Shared.after, Shared.toMem, toMState, execOp])
      · exact hh
    obtain ⟨hsEq, hshEq'⟩ := hstut
    subst s'
    subst sh'
    refine ⟨s, sh, loc', .stutter, ⟨rfl, hlocEq⟩, hinv', hsh', hi, ?_, ?_⟩
    · exact Effect.stutter (SharedRef.ref hs) rfl rfl
    · rw [StepClass]
      refine Or.inl ⟨rfl, ?_⟩
      rw [threadStage, threadStage]
      exact pushStage_casOk (C := C) hpc (by rw [hlocEq]) hok
  | hintPath0 h hpc hintEq hintLe hmark =>
    obtain ⟨s', sh', loc', hafter, hinv', hsh', hd⟩ :=
      push_local_step hi hs hC hpow hbound hlimitC hpc
        (PushInv.hintPath0 h hpc hintEq hintLe hmark) hstep
    cases hstep
    obtain ⟨hshEq, hlocEq⟩ := hafter
    have hstut : s' = s ∧ sh' = sh := by
      rcases hd with ⟨a, res, hev⟩ | hh
      · exfalso
        exact (EventStep.mem_ne hev) (by rw [hshEq]; simp [Shared.after, Shared.toMem, toMState, execOp])
      · exact hh
    obtain ⟨hsEq, hshEq'⟩ := hstut
    subst s'
    subst sh'
    refine ⟨s, sh, loc', .stutter, ⟨rfl, hlocEq⟩, hinv', hsh', hi, ?_, ?_⟩
    · exact Effect.stutter (SharedRef.ref hs) rfl rfl
    · simp [StepClass, threadStage, pushStage, Stage.status, hpc, hlocEq, Local.after, toMState, execOp, upd, rMarker, rHint, rPos, rOk]
  | hintPath1 h hpc hintEq hintLe hmark outEq =>
    obtain ⟨s', sh', loc', hafter, hinv', hsh', hd⟩ :=
      push_local_step hi hs hC hpow hbound hlimitC hpc
        (PushInv.hintPath1 h hpc hintEq hintLe hmark outEq) hstep
    cases hstep
    obtain ⟨hshEq, hlocEq⟩ := hafter
    have hstut : s' = s ∧ sh' = sh := by
      rcases hd with ⟨a, res, hev⟩ | hh
      · exfalso
        exact (EventStep.mem_ne hev) (by rw [hshEq]; simp [Shared.after, Shared.toMem, toMState, execOp])
      · exact hh
    obtain ⟨hsEq, hshEq'⟩ := hstut
    subst s'
    subst sh'
    refine ⟨s, sh, loc', .stutter, ⟨rfl, hlocEq⟩, hinv', hsh', hi, ?_, ?_⟩
    · exact Effect.stutter (SharedRef.ref hs) rfl rfl
    · simp [StepClass, threadStage, pushStage, Stage.status, hpc, hlocEq, Local.after, toMState, execOp, upd, rMarker, rHint, rPos, rOk]
  | hintPath2 h hpc hp outEq =>
    have h63 : h < 2 ^ 63 := by
      have h1 := hp.hintLe
      have h2 := hi.hw_le
      have h3 := hi.hlimit
      exact Nat.lt_of_le_of_lt (Nat.le_trans h1 (Nat.le_trans h2 h3)) hbound
    have h64 : h < 2 ^ 64 := by omega
    have h2h1 : h + 1 < 2 ^ 64 := by omega
    by_cases hsucc : (toMState sh loc).hintW = (toMState sh loc).regs rHint
    · have hhint : sh.hintW.toNat = h := by
        have hw : sh.hintW = UInt64.ofNat h := by
          have hh := hsucc
          simp only [toMState] at hh
          rw [hp.hintReg] at hh
          exact hh
        rw [hw]
        exact uint64_toNat_ofNat_of_lt h64
      obtain ⟨st', hexec, hev⟩ := pushHint_event_of_success hi hs hC hp hhint h2h1
      have hst : opStep pushProgram 4 2 (toMState sh loc) = .running 4 3 st' := by
        simp [opStep, pushProgram, hexec]
      rw [hst] at hstep
      cases hstep
      refine ⟨{ s with w := s.w + 1 }, sh.after st',
        { loc.after st' with phase := Phase.running 4 3 },
        .event .helpW .helped, ⟨rfl, rfl⟩, PushInv.hintPath3 h rfl
          (by rw [← hexec]; simp only [Local.after]
              rw [execOp_casHint_regs_of_ne (by decide : rHint ≠ rOk)]
              simpa [toMState] using hp.hintReg)
          (by rw [← hexec]; simp only [Local.after]
              rw [execOp_casHint_out0, execOp_casHint_regs_of_ne (by decide : rHint ≠ rOk)]
              simpa [toMState] using outEq),
        ?_,
        EventStep.inv_some hi hev, Effect.event .helpW .helped hev, ?_⟩
      · have href : Ref 0 C { s with w := s.w + 1 } (Shared.toMem (sh.after st')) :=
          EventStep.ref hev
        exact SharedRef.after_shared hs href
      · rw [StepClass]
        exact Or.inr (Or.inl ⟨Or.inl rfl, by
          simp [threadStage, pushStage, Local.after, hpc]⟩)
    · let st1 : MState := { toMState sh loc with regs := upd (toMState sh loc).regs rOk 0 }
      have hst : opStep pushProgram 4 2 (toMState sh loc) = .running 4 3 st1 := by
        simp [opStep, pushProgram, execOp, eval, hsucc, st1]
      rw [hst] at hstep
      cases hstep
      have hsh0 : sh.after st1 = sh := by simp [Shared.after, st1, toMState]
      refine ⟨s, sh.after st1, { loc.after st1 with phase := Phase.running 4 3 },
        .stutter, ⟨rfl, rfl⟩, PushInv.hintPath3 h rfl
          (by simpa [Local.after, st1, toMState, upd, rHint, rOk, rPayload, rTmp2] using hp.hintReg)
          (by simpa [Local.after, st1, toMState, upd, rHint, rOk, rPayload, rTmp2] using outEq),
        ?_, hi,
        Effect.stutter (SharedRef.ref hs) rfl (by rw [hsh0]), ?_⟩
      · rwa [hsh0]
      · rw [StepClass]
        exact Or.inl ⟨rfl, by
          simp [threadStage, pushStage, Local.after, hpc]⟩
  | hintPath3 h hpc hintEq outEq =>
    have hst : opStep pushProgram 4 3 (toMState sh loc) = .returned 0 (toMState sh loc) := by
      simp [opStep, pushProgram, eval]
    rw [hst] at hstep
    cases hstep
    obtain ⟨s', sh', loc', hafter, hinv', hsh', hd⟩ :=
      push_local_step hi hs hC hpow hbound hlimitC hpc
        (PushInv.hintPath3 h hpc hintEq outEq) hst
    obtain ⟨hshEq, hlocEq⟩ := hafter
    have hstut : s' = s ∧ sh' = sh := by
      rcases hd with ⟨a, res, hev⟩ | hh
      · exfalso
        exact (EventStep.mem_ne hev) (by rw [hshEq]; simp [Shared.after, Shared.toMem, toMState, execOp])
      · exact hh
    obtain ⟨hsEq, hshEq'⟩ := hstut
    subst s'
    subst sh'
    refine ⟨s, sh, loc', .ret 0, ⟨rfl, hlocEq⟩, hinv', hsh', hi, ?_, ?_⟩
    · exact Effect.ret 0 (SharedRef.ref hs) rfl rfl
    · simp [StepClass, threadStage, pushStage, Stage.status, RetOutputs, hintEq, outEq, UInt64.ofNat_toNat, hpc, hlocEq, Local.after, toMState, execOp, upd, rMarker, rHint, rPos, rOk]
  | fullAhead h m q hpc hintEq hintLe hlim slotEq markerEq hq hfull hqC posEq =>
    obtain ⟨s', sh', loc', hafter, hinv', hsh', hd⟩ :=
      push_local_step hi hs hC hpow hbound hlimitC hpc
        (PushInv.fullAhead h m q hpc hintEq hintLe hlim slotEq markerEq hq hfull hqC posEq) hstep
    cases hstep
    obtain ⟨hshEq, hlocEq⟩ := hafter
    have hstut : s' = s ∧ sh' = sh := by
      rcases hd with ⟨a, res, hev⟩ | hh
      · exfalso
        exact (EventStep.mem_ne hev) (by rw [hshEq]; simp [Shared.after, Shared.toMem, toMState, execOp])
      · exact hh
    obtain ⟨hsEq, hshEq'⟩ := hstut
    subst s'
    subst sh'
    refine ⟨s, sh, loc', .stutter, ⟨rfl, hlocEq⟩, hinv', hsh', hi, ?_, ?_⟩
    · exact Effect.stutter (SharedRef.ref hs) rfl rfl
    · rw [StepClass]
      refine Or.inl ⟨rfl, ?_⟩
      rw [threadStage, threadStage]
      exact pushStage_ahead_step (C := C) hpc (by rw [hlocEq]) (by rw [hlocEq]; rfl) (by rw [hlocEq]; rfl)
  | fullAhead1 h m q hpc hintEq hintLe hlim slotEq markerEq hq hfull hqC posEq =>
    have hqc : h - q = C := by omega
    have hcond : (toMState sh loc).regs rPos = (toMState sh loc).params.capacity := by
      show loc.regs rPos = sh.params.capacity
      rw [posEq, hqc, hs.capacity_eq]
    have hst : opStep pushProgram 5 1 (toMState sh loc) = .running 6 0 (toMState sh loc) := by
      simp [opStep, pushProgram, eval, hcond]
    rw [hst] at hstep
    cases hstep
    obtain ⟨s', sh', loc', hafter, hinv', hsh', hd⟩ :=
      push_local_step hi hs hC hpow hbound hlimitC hpc
        (PushInv.fullAhead1 h m q hpc hintEq hintLe hlim slotEq markerEq hq hfull hqC posEq) hst
    obtain ⟨hshEq, hlocEq⟩ := hafter
    have hstut : s' = s ∧ sh' = sh := by
      rcases hd with ⟨a, res, hev⟩ | hh
      · exfalso
        exact (EventStep.mem_ne hev) (by rw [hshEq]; simp [Shared.after, Shared.toMem, toMState, execOp])
      · exact hh
    obtain ⟨hsEq, hshEq'⟩ := hstut
    subst s'
    subst sh'
    refine ⟨s, sh, loc', .stutter, ⟨rfl, hlocEq⟩, hinv', hsh', hi, ?_, ?_⟩
    · exact Effect.stutter (SharedRef.ref hs) rfl rfl
    · have hcond' : (loc.regs rMarker).toNat / 2 + C = (loc.regs rHint).toNat := by
        rw [markerEq, hintEq]
        simp [uint64_toNat_ofNat_of_lt (by omega : m < 2 ^ 64)]
        omega
      simp [StepClass, threadStage, pushStage, hpc, hlocEq, Local.after, toMState, hcond']
  | ahead h m q hpc hintEq hintLe hlim slotEq markerEq markerMono hq hq63 hfull hltq posEq =>
    obtain ⟨s', sh', loc', hafter, hinv', hsh', hd⟩ :=
      push_local_step hi hs hC hpow hbound hlimitC hpc
        (PushInv.ahead h m q hpc hintEq hintLe hlim slotEq markerEq markerMono hq hq63 hfull hltq posEq) hstep
    cases hstep
    obtain ⟨hshEq, hlocEq⟩ := hafter
    have hstut : s' = s ∧ sh' = sh := by
      rcases hd with ⟨a, res, hev⟩ | hh
      · exfalso
        exact (EventStep.mem_ne hev) (by rw [hshEq]; simp [Shared.after, Shared.toMem, toMState, execOp])
      · exact hh
    obtain ⟨hsEq, hshEq'⟩ := hstut
    subst s'
    subst sh'
    refine ⟨s, sh, loc', .stutter, ⟨rfl, hlocEq⟩, hinv', hsh', hi, ?_, ?_⟩
    · exact Effect.stutter (SharedRef.ref hs) rfl rfl
    · rw [StepClass]
      refine Or.inl ⟨rfl, ?_⟩
      rw [threadStage, threadStage]
      exact pushStage_ahead_step (C := C) hpc (by rw [hlocEq]) (by rw [hlocEq]; rfl) (by rw [hlocEq]; rfl)
  | ahead1 h m q hpc hintEq hintLe hlim slotEq markerEq markerMono hq hq63 hltq posEq =>
    have hC63 : C < 2 ^ 63 := by omega
    have hqval : 2 ^ 64 - (q - h) < 2 ^ 64 := by omega
    have hC64 : C < 2 ^ 64 := by omega
    have hne : (toMState sh loc).regs rPos ≠ (toMState sh loc).params.capacity := by
      show loc.regs rPos ≠ sh.params.capacity
      rw [posEq, hs.capacity_eq]
      intro hc
      have heq : 2 ^ 64 - (q - h) = C := (u64_eq_ofNat_iff hqval hC64).mp hc
      omega
    have hst : opStep pushProgram 5 1 (toMState sh loc) = .running 8 0 (toMState sh loc) := by
      simp [opStep, pushProgram, eval, hne]
    rw [hst] at hstep
    cases hstep
    obtain ⟨s', sh', loc', hafter, hinv', hsh', hd⟩ :=
      push_local_step hi hs hC hpow hbound hlimitC hpc
        (PushInv.ahead1 h m q hpc hintEq hintLe hlim slotEq markerEq markerMono hq hq63 hltq posEq) hst
    obtain ⟨hshEq, hlocEq⟩ := hafter
    have hstut : s' = s ∧ sh' = sh := by
      rcases hd with ⟨a, res, hev⟩ | hh
      · exfalso
        exact (EventStep.mem_ne hev) (by rw [hshEq]; simp [Shared.after, Shared.toMem, toMState, execOp])
      · exact hh
    obtain ⟨hsEq, hshEq'⟩ := hstut
    subst s'
    subst sh'
    refine ⟨s, sh, loc', .stutter, ⟨rfl, hlocEq⟩, hinv', hsh', hi, ?_, ?_⟩
    · exact Effect.stutter (SharedRef.ref hs) rfl rfl
    · rw [StepClass]
      refine Or.inl ⟨rfl, ?_⟩
      rw [threadStage, threadStage]
      apply pushStage_ahead_help (C := C) hC hpc (by rw [hlocEq])
      have hm64 : m < 2 ^ 64 := by
        have h2 : m / 2 < 2 ^ 63 := by omega
        have h3 := (Nat.div_lt_iff_lt_mul (by decide : 0 < 2)).mp h2
        simpa [Nat.pow_succ, Nat.mul_comm] using h3
      have h64 : h < 2 ^ 64 := by
        have h1 := hintLe
        have h2 := hi.hw_le
        have h3 := hi.hlimit
        omega
      rw [markerEq, hintEq, uint64_toNat_ofNat_of_lt hm64, uint64_toNat_ofNat_of_lt h64]
      omega
  | full hpc =>
    have hst : opStep pushProgram 6 0 (toMState sh loc) = .returned 1 (toMState sh loc) := by
      simp [opStep, pushProgram, eval]
    rw [hst] at hstep
    cases hstep
    obtain ⟨s', sh', loc', hafter, hinv', hsh', hd⟩ :=
      push_local_step hi hs hC hpow hbound hlimitC hpc
        (PushInv.full hpc) hst
    obtain ⟨hshEq, hlocEq⟩ := hafter
    have hstut : s' = s ∧ sh' = sh := by
      rcases hd with ⟨a, res, hev⟩ | hh
      · exfalso
        exact (EventStep.mem_ne hev) (by rw [hshEq]; simp [Shared.after, Shared.toMem, toMState, execOp])
      · exact hh
    obtain ⟨hsEq, hshEq'⟩ := hstut
    subst s'
    subst sh'
    refine ⟨s, sh, loc', .ret 1, ⟨rfl, hlocEq⟩, hinv', hsh', hi, ?_, ?_⟩
    · exact Effect.ret 1 (SharedRef.ref hs) rfl rfl
    · simp [StepClass, threadStage, pushStage, Stage.status, RetOutputs, hpc, hlocEq, Local.after, toMState, execOp, upd, rMarker, rHint, rPos, rOk]
  | help0 h m q hpc hintEq hintLe markerEq markerMono hq hq63 hltq posEq =>
    have hq64 : q < 2 ^ 64 := by omega
    have hcond : (half : UInt64) < (toMState sh loc).regs rPos := by
      show UInt64.ofNat (2 ^ 63) < loc.regs rPos
      rw [posEq]
      exact (u64_lt_ofNat_iff (by decide : 2 ^ 63 < 2 ^ 64)
        (by omega : 2 ^ 64 - (q - h) < 2 ^ 64)).mpr (by omega)
    have hmark : 2 * h < ((Shared.toMem sh).cells (h % C)).marker := by
      have hm := markerMono
      have h2q : 2 * q ≤ m := by
        rw [hq, Nat.mul_comm]
        exact Nat.div_mul_le_self m 2
      omega
    have hst : opStep pushProgram 8 0 (toMState sh loc) = .running 7 0 (toMState sh loc) := by
      simp [opStep, pushProgram, eval, hcond]
    rw [hst] at hstep
    cases hstep
    obtain ⟨s', sh', loc', hafter, hinv', hsh', hd⟩ :=
      push_local_step hi hs hC hpow hbound hlimitC hpc
        (PushInv.help0 h m q hpc hintEq hintLe markerEq markerMono hq hq63 hltq posEq) hst
    obtain ⟨hshEq, hlocEq⟩ := hafter
    have hstut : s' = s ∧ sh' = sh := by
      rcases hd with ⟨a, res, hev⟩ | hh
      · exfalso
        exact (EventStep.mem_ne hev) (by rw [hshEq]; simp [Shared.after, Shared.toMem, toMState, execOp])
      · exact hh
    obtain ⟨hsEq, hshEq'⟩ := hstut
    subst s'
    subst sh'
    refine ⟨s, sh, loc', .stutter, ⟨rfl, hlocEq⟩, hinv', hsh', hi, ?_, ?_⟩
    · exact Effect.stutter (SharedRef.ref hs) rfl rfl
    · simp [StepClass, threadStage, pushStage, hpc, hlocEq, Local.after, toMState, execOp, upd, rMarker, rHint, rPos, rOk]
  | help1 h hpc hintEq hintLe hmark =>
    obtain ⟨s', sh', loc', hafter, hinv', hsh', hd⟩ :=
      push_local_step hi hs hC hpow hbound hlimitC hpc
        (PushInv.help1 h hpc hintEq hintLe hmark) hstep
    cases hstep
    obtain ⟨hshEq, hlocEq⟩ := hafter
    have hstut : s' = s ∧ sh' = sh := by
      rcases hd with ⟨a, res, hev⟩ | hh
      · exfalso
        exact (EventStep.mem_ne hev) (by rw [hshEq]; simp [Shared.after, Shared.toMem, toMState, execOp])
      · exact hh
    obtain ⟨hsEq, hshEq'⟩ := hstut
    subst s'
    subst sh'
    refine ⟨s, sh, loc', .stutter, ⟨rfl, hlocEq⟩, hinv', hsh', hi, ?_, ?_⟩
    · exact Effect.stutter (SharedRef.ref hs) rfl rfl
    · simp [StepClass, threadStage, pushStage, Stage.status, hpc, hlocEq, Local.after, toMState, execOp, upd, rMarker, rHint, rPos, rOk]
  | help2 h hpc hp =>
    have h63 : h < 2 ^ 63 := by
      have h1 := hp.hintLe
      have h2 := hi.hw_le
      have h3 := hi.hlimit
      exact Nat.lt_of_le_of_lt (Nat.le_trans h1 (Nat.le_trans h2 h3)) hbound
    have h64 : h < 2 ^ 64 := by omega
    have h2h1 : h + 1 < 2 ^ 64 := by omega
    by_cases hsucc : (toMState sh loc).hintW = (toMState sh loc).regs rHint
    · have hhint : sh.hintW.toNat = h := by
        have hw : sh.hintW = UInt64.ofNat h := by
          have hh := hsucc
          simp only [toMState] at hh
          rw [hp.hintReg] at hh
          exact hh
        rw [hw]
        exact uint64_toNat_ofNat_of_lt h64
      obtain ⟨st', hexec, hev⟩ := pushHint_event_of_success hi hs hC hp hhint h2h1
      have hst : opStep pushProgram 7 1 (toMState sh loc) = .running 7 2 st' := by
        simp [opStep, pushProgram, hexec]
      rw [hst] at hstep
      cases hstep
      refine ⟨{ s with w := s.w + 1 }, sh.after st',
        { loc.after st' with phase := Phase.running 7 2 },
        .event .helpW .helped, ⟨rfl, rfl⟩, PushInv.help3 rfl, ?_,
        EventStep.inv_some hi hev, Effect.event .helpW .helped hev, ?_⟩
      · have href : Ref 0 C { s with w := s.w + 1 } (Shared.toMem (sh.after st')) :=
          EventStep.ref hev
        exact SharedRef.after_shared hs href
      · rw [StepClass]
        exact Or.inr (Or.inl ⟨Or.inl rfl, by
          simp [threadStage, pushStage, Local.after, hpc]⟩)
    · let st1 : MState := { toMState sh loc with regs := upd (toMState sh loc).regs rOk 0 }
      have hst : opStep pushProgram 7 1 (toMState sh loc) = .running 7 2 st1 := by
        simp [opStep, pushProgram, execOp, eval, hsucc, st1]
      rw [hst] at hstep
      cases hstep
      have hsh0 : sh.after st1 = sh := by simp [Shared.after, st1, toMState]
      refine ⟨s, sh.after st1, { loc.after st1 with phase := Phase.running 7 2 },
        .stutter, ⟨rfl, rfl⟩, PushInv.help3 rfl, ?_, hi,
        Effect.stutter (SharedRef.ref hs) rfl (by rw [hsh0]), ?_⟩
      · rwa [hsh0]
      · rw [StepClass]
        exact Or.inl ⟨rfl, by
          simp [threadStage, pushStage, Local.after, hpc]⟩
  | help3 hpc =>
    obtain ⟨s', sh', loc', hafter, hinv', hsh', hd⟩ :=
      push_local_step hi hs hC hpow hbound hlimitC hpc
        (PushInv.help3 hpc) hstep
    cases hstep
    obtain ⟨hshEq, hlocEq⟩ := hafter
    have hstut : s' = s ∧ sh' = sh := by
      rcases hd with ⟨a, res, hev⟩ | hh
      · exfalso
        exact (EventStep.mem_ne hev) (by rw [hshEq]; simp [Shared.after, Shared.toMem, toMState, execOp])
      · exact hh
    obtain ⟨hsEq, hshEq'⟩ := hstut
    subst s'
    subst sh'
    refine ⟨s, sh, loc', .stutter, ⟨rfl, hlocEq⟩, hinv', hsh', hi, ?_, ?_⟩
    · exact Effect.stutter (SharedRef.ref hs) rfl rfl
    · simp [StepClass, threadStage, pushStage, Stage.status, hpc, hlocEq, Local.after, toMState, execOp, upd, rMarker, rHint, rPos, rOk]
  | exhausted hpc =>
    have hst : opStep pushProgram 9 0 (toMState sh loc) = .returned 3 (toMState sh loc) := by
      simp [opStep, pushProgram, eval]
    rw [hst] at hstep
    cases hstep
    obtain ⟨s', sh', loc', hafter, hinv', hsh', hd⟩ :=
      push_local_step hi hs hC hpow hbound hlimitC hpc
        (PushInv.exhausted hpc) hst
    obtain ⟨hshEq, hlocEq⟩ := hafter
    have hstut : s' = s ∧ sh' = sh := by
      rcases hd with ⟨a, res, hev⟩ | hh
      · exfalso
        exact (EventStep.mem_ne hev) (by rw [hshEq]; simp [Shared.after, Shared.toMem, toMState, execOp])
      · exact hh
    obtain ⟨hsEq, hshEq'⟩ := hstut
    subst s'
    subst sh'
    refine ⟨s, sh, loc', .ret 3, ⟨rfl, hlocEq⟩, hinv', hsh', hi, ?_, ?_⟩
    · exact Effect.ret 3 (SharedRef.ref hs) rfl rfl
    · simp [StepClass, threadStage, pushStage, Stage.status, RetOutputs, hpc, hlocEq, Local.after, toMState, execOp, upd, rMarker, rHint, rPos, rOk]



theorem pop_cert {C limit k : Nat} {s : AbsState UInt64} {sh : Shared} {loc : Local}
    {pc oi : Nat} {r : OpResult}
    (hi : Inv C limit s) (hs : SharedRef C limit s sh)
    (hC : 0 < C) (hpow : C = 2 ^ k) (hCmax : C ≤ 2 ^ 24)
    (hbound : limit < 2 ^ 63) (hlimitC : limit + C ≤ 2 ^ 63)
    (hinv : PopInv C limit s sh loc (Phase.running pc oi))
    (hnot : ¬ PopSelected loc)
    (hstep : opStep popProgram pc oi (toMState sh loc) = r) :
    PopCert C limit hC s sh loc r := by
  cases hinv with
  | entry hpc =>
    obtain ⟨s', sh', loc', hafter, hinv', hsh', hd⟩ :=
      pop_local_step hi hs hC hpow hCmax hbound hlimitC hpc
        (PopInv.entry hpc) hstep
    cases hstep
    obtain ⟨hshEq, hlocEq⟩ := hafter
    have hstut : s' = s ∧ sh' = sh := by
      rcases hd with ⟨a, res, hev⟩ | hh
      · exfalso
        exact (EventStep.mem_ne hev) (by rw [hshEq]; simp [Shared.after, Shared.toMem, toMState, execOp])
      · exact hh
    obtain ⟨hsEq, hshEq'⟩ := hstut
    subst s'
    subst sh'
    refine ⟨s, sh, loc', .stutter, ⟨rfl, hlocEq⟩, hinv', hsh', hi, ?_, ?_⟩
    · exact Effect.stutter (SharedRef.ref hs) rfl rfl
    · simp [StepClass, threadStage, popStage, Stage.status, hpc, hlocEq, Local.after, toMState, execOp, upd, rMarker, rHint, rPos, rOk]
  | hint h hpc hintEq hintLe => exact absurd (by simp [PopSelected, hpc]) hnot
  | check h hpc hintEq hintLe hlim =>
    obtain ⟨s', sh', loc', hafter, hinv', hsh', hd⟩ :=
      pop_local_step hi hs hC hpow hCmax hbound hlimitC hpc
        (PopInv.check h hpc hintEq hintLe hlim) hstep
    cases hstep
    obtain ⟨hshEq, hlocEq⟩ := hafter
    have hstut : s' = s ∧ sh' = sh := by
      rcases hd with ⟨a, res, hev⟩ | hh
      · exfalso
        exact (EventStep.mem_ne hev) (by rw [hshEq]; simp [Shared.after, Shared.toMem, toMState, execOp])
      · exact hh
    obtain ⟨hsEq, hshEq'⟩ := hstut
    subst s'
    subst sh'
    refine ⟨s, sh, loc', .stutter, ⟨rfl, hlocEq⟩, hinv', hsh', hi, ?_, ?_⟩
    · exact Effect.stutter (SharedRef.ref hs) rfl rfl
    · simp [StepClass, threadStage, popStage, Stage.status, hpc, hlocEq, Local.after, toMState, execOp, upd, rMarker, rHint, rPos, rOk]
  | slot h hpc hintEq hintLe hlim slotEq => exact absurd (by simp [PopSelected, hpc]) hnot
  | load h m q hpc hintEq hintLe hlim slotEq markerEq hm64 markerMono hq hq63 hle_q =>
    obtain ⟨s', sh', loc', hafter, hinv', hsh', hd⟩ :=
      pop_local_step hi hs hC hpow hCmax hbound hlimitC hpc
        (PopInv.load h m q hpc hintEq hintLe hlim slotEq markerEq hm64 markerMono hq hq63 hle_q) hstep
    cases hstep
    obtain ⟨hshEq, hlocEq⟩ := hafter
    have hstut : s' = s ∧ sh' = sh := by
      rcases hd with ⟨a, res, hev⟩ | hh
      · exfalso
        exact (EventStep.mem_ne hev) (by rw [hshEq]; simp [Shared.after, Shared.toMem, toMState, execOp])
      · exact hh
    obtain ⟨hsEq, hshEq'⟩ := hstut
    subst s'
    subst sh'
    refine ⟨s, sh, loc', .stutter, ⟨rfl, hlocEq⟩, hinv', hsh', hi, ?_, ?_⟩
    · exact Effect.stutter (SharedRef.ref hs) rfl rfl
    · rw [StepClass]
      refine Or.inl ⟨rfl, ?_⟩
      rw [threadStage, threadStage]
      exact popStage_load (C := C) hpc (by rw [hlocEq]) (by rw [hlocEq]; rfl) (by rw [hlocEq]; rfl)
  | pos h m q hpc hintEq hintLe hlim slotEq markerEq hm64 markerMono posEq hq hq63 hle_q =>
    have h64 : h < 2 ^ 64 := by
      have h1 := hintLe
      have h2 := hi.hr_le
      have h3 := hi.hR_le_W
      have h4 := hi.hlimit
      omega
    have hq64 : q < 2 ^ 64 := by omega
    by_cases qh : q = h
    · have hcond : (toMState sh loc).regs rPos = (toMState sh loc).regs rHint := by
        show loc.regs rPos = loc.regs rHint
        rw [posEq, hintEq, u64_eq_ofNat_iff hq64 h64]
        exact qh
      have hst : opStep popProgram 1 3 (toMState sh loc) = .running 2 0 (toMState sh loc) := by
        simp [opStep, popProgram, eval, hcond]
      rw [hst] at hstep
      cases hstep
      obtain ⟨s', sh', loc', hafter, hinv', hsh', hd⟩ :=
        pop_local_step hi hs hC hpow hCmax hbound hlimitC hpc
          (PopInv.pos h m q hpc hintEq hintLe hlim slotEq markerEq hm64 markerMono posEq hq hq63 hle_q) hst
      obtain ⟨hshEq, hlocEq⟩ := hafter
      have hstut : s' = s ∧ sh' = sh := by
        rcases hd with ⟨a, res, hev⟩ | hh
        · exfalso
          exact (EventStep.mem_ne hev) (by rw [hshEq]; simp [Shared.after, Shared.toMem, toMState, execOp])
        · exact hh
      obtain ⟨hsEq, hshEq'⟩ := hstut
      subst s'
      subst sh'
      refine ⟨s, sh, loc', .stutter, ⟨rfl, hlocEq⟩, hinv', hsh', hi, ?_, ?_⟩
      · exact Effect.stutter (SharedRef.ref hs) rfl rfl
      · rw [StepClass]
        refine Or.inl ⟨rfl, ?_⟩
        rw [threadStage, threadStage]
        apply popStage_pos_ready (C := C) hpc (by rw [hlocEq]) (by rw [hlocEq]; rfl) (by rw [hlocEq]; rfl)
    · have hne : (toMState sh loc).regs rPos ≠ (toMState sh loc).regs rHint := by
        show loc.regs rPos ≠ loc.regs rHint
        rw [posEq, hintEq]
        intro hc
        exact qh ((u64_eq_ofNat_iff hq64 h64).mp hc)
      have hst : opStep popProgram 1 3 (toMState sh loc) = .running 5 0 (toMState sh loc) := by
        simp [opStep, popProgram, eval, hne]
      rw [hst] at hstep
      cases hstep
      obtain ⟨s', sh', loc', hafter, hinv', hsh', hd⟩ :=
        pop_local_step hi hs hC hpow hCmax hbound hlimitC hpc
          (PopInv.pos h m q hpc hintEq hintLe hlim slotEq markerEq hm64 markerMono posEq hq hq63 hle_q) hst
      obtain ⟨hshEq, hlocEq⟩ := hafter
      have hstut : s' = s ∧ sh' = sh := by
        rcases hd with ⟨a, res, hev⟩ | hh
        · exfalso
          exact (EventStep.mem_ne hev) (by rw [hshEq]; simp [Shared.after, Shared.toMem, toMState, execOp])
        · exact hh
      obtain ⟨hsEq, hshEq'⟩ := hstut
      subst s'
      subst sh'
      refine ⟨s, sh, loc', .stutter, ⟨rfl, hlocEq⟩, hinv', hsh', hi, ?_, ?_⟩
      · exact Effect.stutter (SharedRef.ref hs) rfl rfl
      · rw [StepClass]
        refine Or.inl ⟨rfl, ?_⟩
        rw [threadStage, threadStage]
        apply popStage_pos_ahead (C := C) hpc (by rw [hlocEq])
        rw [markerEq, hintEq, uint64_toNat_ofNat_of_lt hm64, uint64_toNat_ofNat_of_lt h64]
        omega
  | readyTest h m q hpc hintEq hintLe hlim slotEq markerEq markerMono posEq hq hq63 hle_q qeq =>
    obtain ⟨s', sh', loc', hafter, hinv', hsh', hd⟩ :=
      pop_local_step hi hs hC hpow hCmax hbound hlimitC hpc
        (PopInv.readyTest h m q hpc hintEq hintLe hlim slotEq markerEq markerMono posEq hq hq63 hle_q qeq) hstep
    cases hstep
    obtain ⟨hshEq, hlocEq⟩ := hafter
    have hstut : s' = s ∧ sh' = sh := by
      rcases hd with ⟨a, res, hev⟩ | hh
      · exfalso
        exact (EventStep.mem_ne hev) (by rw [hshEq]; simp [Shared.after, Shared.toMem, toMState, execOp])
      · exact hh
    obtain ⟨hsEq, hshEq'⟩ := hstut
    subst s'
    subst sh'
    refine ⟨s, sh, loc', .stutter, ⟨rfl, hlocEq⟩, hinv', hsh', hi, ?_, ?_⟩
    · exact Effect.stutter (SharedRef.ref hs) rfl rfl
    · rw [StepClass]
      refine Or.inl ⟨rfl, ?_⟩
      rw [threadStage, threadStage]
      exact popStage_ready_even (C := C) hpc (by rw [hlocEq]) (by rw [hlocEq]; rfl) (by rw [hlocEq]; rfl)
  | evenTest h m q hpc hintEq hintLe hlim slotEq markerEq markerMono posEq hq hq63 hle_q qeq tmp0Eq =>
    have hm2 : m % 2 < 2 ^ 64 := by omega
    have h64 : h < 2 ^ 64 := by
      have h1 := hintLe
      have h2 := hi.hr_le
      have h3 := hi.hR_le_W
      have h4 := hi.hlimit
      omega
    have hm64 : m < 2 ^ 64 := by
      have h2 : m / 2 < 2 ^ 63 := by omega
      have h3 := (Nat.div_lt_iff_lt_mul (by decide : 0 < 2)).mp h2
      simpa [Nat.pow_succ, Nat.mul_comm] using h3
    have heq : (loc.regs rMarker).toNat / 2 = (loc.regs rHint).toNat := by
      rw [markerEq, hintEq, uint64_toNat_ofNat_of_lt hm64, uint64_toNat_ofNat_of_lt h64]
      omega
    by_cases hpar : m % 2 = 0
    · have hcond : (toMState sh loc).regs rTmp0 = 0 := by
        show loc.regs rTmp0 = 0
        rw [tmp0Eq, u64_eq_zero_ofNat hm2, hpar]
      have hst : opStep popProgram 2 1 (toMState sh loc) = .running 3 0 (toMState sh loc) := by
        simp [opStep, popProgram, eval, hcond]
      rw [hst] at hstep
      cases hstep
      obtain ⟨s', sh', loc', hafter, hinv', hsh', hd⟩ :=
        pop_local_step hi hs hC hpow hCmax hbound hlimitC hpc
          (PopInv.evenTest h m q hpc hintEq hintLe hlim slotEq markerEq markerMono posEq hq hq63 hle_q qeq tmp0Eq) hst
      obtain ⟨hshEq, hlocEq⟩ := hafter
      have hstut : s' = s ∧ sh' = sh := by
        rcases hd with ⟨a, res, hev⟩ | hh
        · exfalso
          exact (EventStep.mem_ne hev) (by rw [hshEq]; simp [Shared.after, Shared.toMem, toMState, execOp])
        · exact hh
      obtain ⟨hsEq, hshEq'⟩ := hstut
      subst s'
      subst sh'
      refine ⟨s, sh, loc', .stutter, ⟨rfl, hlocEq⟩, hinv', hsh', hi, ?_, ?_⟩
      · exact Effect.stutter (SharedRef.ref hs) rfl rfl
      · rw [StepClass]
        refine Or.inl ⟨rfl, ?_⟩
        rw [threadStage, threadStage]
        exact popStage_even_empty (C := C) hpc (by rw [hlocEq]) heq (by rw [markerEq, uint64_toNat_ofNat_of_lt hm64]; exact hpar)
    · have hpar' : m % 2 ≠ 0 := hpar
      have hodd : (loc.regs rMarker).toNat % 2 ≠ 0 := by
        rw [markerEq, uint64_toNat_ofNat_of_lt hm64]
        exact hpar'
      have hcond : ¬ ((toMState sh loc).regs rTmp0 = 0) := by
        show ¬ (loc.regs rTmp0 = 0)
        rw [tmp0Eq]
        intro hc
        exact hpar ((u64_eq_zero_ofNat hm2).mp hc)
      have hst : opStep popProgram 2 1 (toMState sh loc) = .running 7 0 (toMState sh loc) := by
        simp [opStep, popProgram, eval, hcond]
      rw [hst] at hstep
      cases hstep
      obtain ⟨s', sh', loc', hafter, hinv', hsh', hd⟩ :=
        pop_local_step hi hs hC hpow hCmax hbound hlimitC hpc
          (PopInv.evenTest h m q hpc hintEq hintLe hlim slotEq markerEq markerMono posEq hq hq63 hle_q qeq tmp0Eq) hst
      obtain ⟨hshEq, hlocEq⟩ := hafter
      have hstut : s' = s ∧ sh' = sh := by
        rcases hd with ⟨a, res, hev⟩ | hh
        · exfalso
          exact (EventStep.mem_ne hev) (by rw [hshEq]; simp [Shared.after, Shared.toMem, toMState, execOp])
        · exact hh
      obtain ⟨hsEq, hshEq'⟩ := hstut
      subst s'
      subst sh'
      refine ⟨s, sh, loc', .stutter, ⟨rfl, hlocEq⟩, hinv', hsh', hi, ?_, ?_⟩
      · exact Effect.stutter (SharedRef.ref hs) rfl rfl
      · rw [StepClass]
        refine Or.inl ⟨rfl, ?_⟩
        rw [threadStage, threadStage]
        exact popStage_odd_cas (C := C) hpc (by rw [hlocEq]) hodd
  | empty hpc =>
    have hst : opStep popProgram 3 0 (toMState sh loc) = .returned 2 (toMState sh loc) := by
      simp [opStep, popProgram, eval]
    rw [hst] at hstep
    cases hstep
    obtain ⟨s', sh', loc', hafter, hinv', hsh', hd⟩ :=
      pop_local_step hi hs hC hpow hCmax hbound hlimitC hpc
        (PopInv.empty hpc) hst
    obtain ⟨hshEq, hlocEq⟩ := hafter
    have hstut : s' = s ∧ sh' = sh := by
      rcases hd with ⟨a, res, hev⟩ | hh
      · exfalso
        exact (EventStep.mem_ne hev) (by rw [hshEq]; simp [Shared.after, Shared.toMem, toMState, execOp])
      · exact hh
    obtain ⟨hsEq, hshEq'⟩ := hstut
    subst s'
    subst sh'
    refine ⟨s, sh, loc', .ret 2, ⟨rfl, hlocEq⟩, hinv', hsh', hi, ?_, ?_⟩
    · exact Effect.ret 2 (SharedRef.ref hs) rfl rfl
    · simp [StepClass, threadStage, popStage, Stage.status, RetOutputs, hpc, hlocEq, Local.after, toMState, execOp, upd, rMarker, rHint, rPos, rOk]
  | cas0 h hpc hintEq hintLe hlim slotEq markerEq =>
    obtain ⟨s', sh', loc', hafter, hinv', hsh', hd⟩ :=
      pop_local_step hi hs hC hpow hCmax hbound hlimitC hpc
        (PopInv.cas0 h hpc hintEq hintLe hlim slotEq markerEq) hstep
    cases hstep
    obtain ⟨hshEq, hlocEq⟩ := hafter
    have hstut : s' = s ∧ sh' = sh := by
      rcases hd with ⟨a, res, hev⟩ | hh
      · exfalso
        exact (EventStep.mem_ne hev) (by rw [hshEq]; simp [Shared.after, Shared.toMem, toMState, execOp])
      · exact hh
    obtain ⟨hsEq, hshEq'⟩ := hstut
    subst s'
    subst sh'
    refine ⟨s, sh, loc', .stutter, ⟨rfl, hlocEq⟩, hinv', hsh', hi, ?_, ?_⟩
    · exact Effect.stutter (SharedRef.ref hs) rfl rfl
    · simp [StepClass, threadStage, popStage, Stage.status, hpc, hlocEq, Local.after, toMState, execOp, upd, rMarker, rHint, rPos, rOk]
  | cas1 h hpc hintEq hintLe hlim slotEq markerEq desMarker =>
    obtain ⟨s', sh', loc', hafter, hinv', hsh', hd⟩ :=
      pop_local_step hi hs hC hpow hCmax hbound hlimitC hpc
        (PopInv.cas1 h hpc hintEq hintLe hlim slotEq markerEq desMarker) hstep
    cases hstep
    obtain ⟨hshEq, hlocEq⟩ := hafter
    have hstut : s' = s ∧ sh' = sh := by
      rcases hd with ⟨a, res, hev⟩ | hh
      · exfalso
        exact (EventStep.mem_ne hev) (by rw [hshEq]; simp [Shared.after, Shared.toMem, toMState, execOp])
      · exact hh
    obtain ⟨hsEq, hshEq'⟩ := hstut
    subst s'
    subst sh'
    refine ⟨s, sh, loc', .stutter, ⟨rfl, hlocEq⟩, hinv', hsh', hi, ?_, ?_⟩
    · exact Effect.stutter (SharedRef.ref hs) rfl rfl
    · simp [StepClass, threadStage, popStage, Stage.status, hpc, hlocEq, Local.after, toMState, execOp, upd, rMarker, rHint, rPos, rOk]
  | cas h hp => exact absurd (by simp [PopSelected, hp.hpc]) hnot
  | casFail hpc hok =>
    have hcond : (toMState sh loc).regs rOk = 0 := hok
    have hst : opStep popProgram 7 3 (toMState sh loc) = .running 0 0 (toMState sh loc) := by
      simp [opStep, popProgram, eval, hcond]
    rw [hst] at hstep
    cases hstep
    obtain ⟨s', sh', loc', hafter, hinv', hsh', hd⟩ :=
      pop_local_step hi hs hC hpow hCmax hbound hlimitC hpc (PopInv.casFail hpc hok) hst
    obtain ⟨hshEq, hlocEq⟩ := hafter
    have hstut : s' = s ∧ sh' = sh := by
      rcases hd with ⟨a, res, hev⟩ | hh
      · exfalso
        exact (EventStep.mem_ne hev) (by rw [hshEq]; simp [Shared.after, Shared.toMem, toMState, execOp])
      · exact hh
    obtain ⟨hsEq, hshEq'⟩ := hstut
    subst s'
    subst sh'
    refine ⟨s, sh, loc', .stutter, ⟨rfl, hlocEq⟩, hinv', hsh', hi, ?_, ?_⟩
    · exact Effect.stutter (SharedRef.ref hs) rfl rfl
    · rw [StepClass]
      refine Or.inl ⟨rfl, ?_⟩
      rw [threadStage, threadStage]
      exact popStage_casFail (C := C) hpc (by rw [hlocEq]) hok
  | casOk h hpc hok hintEq hintLe hmark =>
    have hcond : ¬ ((toMState sh loc).regs rOk = 0) := hok
    have hst : opStep popProgram 7 3 (toMState sh loc) = .running 4 0 (toMState sh loc) := by
      simp [opStep, popProgram, eval, hcond]
    rw [hst] at hstep
    cases hstep
    obtain ⟨s', sh', loc', hafter, hinv', hsh', hd⟩ :=
      pop_local_step hi hs hC hpow hCmax hbound hlimitC hpc (PopInv.casOk h hpc hok hintEq hintLe hmark) hst
    obtain ⟨hshEq, hlocEq⟩ := hafter
    have hstut : s' = s ∧ sh' = sh := by
      rcases hd with ⟨a, res, hev⟩ | hh
      · exfalso
        exact (EventStep.mem_ne hev) (by rw [hshEq]; simp [Shared.after, Shared.toMem, toMState, execOp])
      · exact hh
    obtain ⟨hsEq, hshEq'⟩ := hstut
    subst s'
    subst sh'
    refine ⟨s, sh, loc', .stutter, ⟨rfl, hlocEq⟩, hinv', hsh', hi, ?_, ?_⟩
    · exact Effect.stutter (SharedRef.ref hs) rfl rfl
    · rw [StepClass]
      refine Or.inl ⟨rfl, ?_⟩
      rw [threadStage, threadStage]
      exact popStage_casOk (C := C) hpc (by rw [hlocEq]) hok
  | out0 h hpc hintEq hintLe hmark =>
    obtain ⟨s', sh', loc', hafter, hinv', hsh', hd⟩ :=
      pop_local_step hi hs hC hpow hCmax hbound hlimitC hpc
        (PopInv.out0 h hpc hintEq hintLe hmark) hstep
    cases hstep
    obtain ⟨hshEq, hlocEq⟩ := hafter
    have hstut : s' = s ∧ sh' = sh := by
      rcases hd with ⟨a, res, hev⟩ | hh
      · exfalso
        exact (EventStep.mem_ne hev) (by rw [hshEq]; simp [Shared.after, Shared.toMem, toMState, execOp])
      · exact hh
    obtain ⟨hsEq, hshEq'⟩ := hstut
    subst s'
    subst sh'
    refine ⟨s, sh, loc', .stutter, ⟨rfl, hlocEq⟩, hinv', hsh', hi, ?_, ?_⟩
    · exact Effect.stutter (SharedRef.ref hs) rfl rfl
    · simp [StepClass, threadStage, popStage, Stage.status, hpc, hlocEq, Local.after, toMState, execOp, upd, rMarker, rHint, rPos, rOk]
  | out1 h hpc hintEq hintLe hmark out0Eq =>
    obtain ⟨s', sh', loc', hafter, hinv', hsh', hd⟩ :=
      pop_local_step hi hs hC hpow hCmax hbound hlimitC hpc
        (PopInv.out1 h hpc hintEq hintLe hmark out0Eq) hstep
    cases hstep
    obtain ⟨hshEq, hlocEq⟩ := hafter
    have hstut : s' = s ∧ sh' = sh := by
      rcases hd with ⟨a, res, hev⟩ | hh
      · exfalso
        exact (EventStep.mem_ne hev) (by rw [hshEq]; simp [Shared.after, Shared.toMem, toMState, execOp])
      · exact hh
    obtain ⟨hsEq, hshEq'⟩ := hstut
    subst s'
    subst sh'
    refine ⟨s, sh, loc', .stutter, ⟨rfl, hlocEq⟩, hinv', hsh', hi, ?_, ?_⟩
    · exact Effect.stutter (SharedRef.ref hs) rfl rfl
    · simp [StepClass, threadStage, popStage, Stage.status, hpc, hlocEq, Local.after, toMState, execOp, upd, rMarker, rHint, rPos, rOk]
  | out2 h hpc hintEq hintLe hmark out0Eq out1Eq =>
    obtain ⟨s', sh', loc', hafter, hinv', hsh', hd⟩ :=
      pop_local_step hi hs hC hpow hCmax hbound hlimitC hpc
        (PopInv.out2 h hpc hintEq hintLe hmark out0Eq out1Eq) hstep
    cases hstep
    obtain ⟨hshEq, hlocEq⟩ := hafter
    have hstut : s' = s ∧ sh' = sh := by
      rcases hd with ⟨a, res, hev⟩ | hh
      · exfalso
        exact (EventStep.mem_ne hev) (by rw [hshEq]; simp [Shared.after, Shared.toMem, toMState, execOp])
      · exact hh
    obtain ⟨hsEq, hshEq'⟩ := hstut
    subst s'
    subst sh'
    refine ⟨s, sh, loc', .stutter, ⟨rfl, hlocEq⟩, hinv', hsh', hi, ?_, ?_⟩
    · exact Effect.stutter (SharedRef.ref hs) rfl rfl
    · simp [StepClass, threadStage, popStage, Stage.status, hpc, hlocEq, Local.after, toMState, execOp, upd, rMarker, rHint, rPos, rOk]
  | out3 h hpc hp out0Eq out1Eq =>
    have h63 : h < 2 ^ 63 := by
      have h1 := hp.hintLe
      have h2 := hi.hr_le
      have h3 := hi.hR_le_W
      have h4 := hi.hlimit
      exact Nat.lt_of_le_of_lt (Nat.le_trans h1 (Nat.le_trans h2 (Nat.le_trans h3 h4))) hbound
    have h64 : h < 2 ^ 64 := by omega
    have h2h1 : h + 1 < 2 ^ 64 := by omega
    by_cases hsucc : (toMState sh loc).hintR = (toMState sh loc).regs rHint
    · have hhint : sh.hintR.toNat = h := by
        have hw : sh.hintR = UInt64.ofNat h := by
          have hh := hsucc
          simp only [toMState] at hh
          rw [hp.hintReg] at hh
          exact hh
        rw [hw]
        exact uint64_toNat_ofNat_of_lt h64
      obtain ⟨st', hexec, hev⟩ := popHint_event_of_success hi hs hC hp hhint h2h1
      have hst : opStep popProgram 4 3 (toMState sh loc) = .running 4 4 st' := by
        simp [opStep, popProgram, hexec]
      rw [hst] at hstep
      cases hstep
      refine ⟨{ s with r := s.r + 1 }, sh.after st',
        { loc.after st' with phase := Phase.running 4 4 },
        .event .helpR .helped, ⟨rfl, rfl⟩, PopInv.out4 h rfl
          (by rw [← hexec]; simp only [Local.after]
              rw [execOp_casHint_regs_of_ne (by decide : rHint ≠ rOk)]
              simpa [toMState] using hp.hintReg)
          (by rw [← hexec]; simp only [Local.after]
              rw [execOp_casHint_out0, execOp_casHint_regs_of_ne (by decide : rPayload ≠ rOk)]
              simpa [toMState] using out0Eq)
          (by rw [← hexec]; simp only [Local.after]
              rw [execOp_casHint_out1, execOp_casHint_regs_of_ne (by decide : rHint ≠ rOk)]
              simpa [toMState] using out1Eq),
        ?_,
        EventStep.inv_some hi hev, Effect.event .helpR .helped hev, ?_⟩
      · have href : Ref 0 C { s with r := s.r + 1 } (Shared.toMem (sh.after st')) :=
          EventStep.ref hev
        exact SharedRef.after_shared hs href
      · rw [StepClass]
        exact Or.inr (Or.inl ⟨Or.inr rfl, by
          simp [threadStage, popStage, Local.after, hpc]⟩)
    · let st1 : MState := { toMState sh loc with regs := upd (toMState sh loc).regs rOk 0 }
      have hst : opStep popProgram 4 3 (toMState sh loc) = .running 4 4 st1 := by
        simp [opStep, popProgram, execOp, eval, hsucc, st1]
      rw [hst] at hstep
      cases hstep
      have hsh0 : sh.after st1 = sh := by simp [Shared.after, st1, toMState]
      refine ⟨s, sh.after st1, { loc.after st1 with phase := Phase.running 4 4 },
        .stutter, ⟨rfl, rfl⟩, PopInv.out4 h rfl
          (by simpa [Local.after, st1, toMState, upd, rHint, rOk, rPayload, rTmp2] using hp.hintReg)
          (by simpa [Local.after, st1, toMState, upd, rHint, rOk, rPayload, rTmp2] using out0Eq)
          (by simpa [Local.after, st1, toMState, upd, rHint, rOk, rPayload, rTmp2] using out1Eq),
        ?_, hi,
        Effect.stutter (SharedRef.ref hs) rfl (by rw [hsh0]), ?_⟩
      · rwa [hsh0]
      · rw [StepClass]
        exact Or.inl ⟨rfl, by
          simp [threadStage, popStage, Local.after, hpc]⟩
  | out4 h hpc hintEq out0Eq out1Eq =>
    have hst : opStep popProgram 4 4 (toMState sh loc) = .returned 0 (toMState sh loc) := by
      simp [opStep, popProgram, eval]
    rw [hst] at hstep
    cases hstep
    obtain ⟨s', sh', loc', hafter, hinv', hsh', hd⟩ :=
      pop_local_step hi hs hC hpow hCmax hbound hlimitC hpc
        (PopInv.out4 h hpc hintEq out0Eq out1Eq) hst
    obtain ⟨hshEq, hlocEq⟩ := hafter
    have hstut : s' = s ∧ sh' = sh := by
      rcases hd with ⟨a, res, hev⟩ | hh
      · exfalso
        exact (EventStep.mem_ne hev) (by rw [hshEq]; simp [Shared.after, Shared.toMem, toMState, execOp])
      · exact hh
    obtain ⟨hsEq, hshEq'⟩ := hstut
    subst s'
    subst sh'
    refine ⟨s, sh, loc', .ret 0, ⟨rfl, hlocEq⟩, hinv', hsh', hi, ?_, ?_⟩
    · exact Effect.ret 0 (SharedRef.ref hs) rfl rfl
    · simp [StepClass, threadStage, popStage, Stage.status, RetOutputs, hintEq, out0Eq, out1Eq, UInt64.ofNat_toNat, hpc, hlocEq, Local.after, toMState, execOp, upd, rMarker, rHint, rPos, rOk]
  | ahead h m q hpc hintEq hintLe hlim slotEq markerEq markerMono hq hq63 hle_q qne posEq =>
    obtain ⟨s', sh', loc', hafter, hinv', hsh', hd⟩ :=
      pop_local_step hi hs hC hpow hCmax hbound hlimitC hpc
        (PopInv.ahead h m q hpc hintEq hintLe hlim slotEq markerEq markerMono hq hq63 hle_q qne posEq) hstep
    cases hstep
    obtain ⟨hshEq, hlocEq⟩ := hafter
    have hstut : s' = s ∧ sh' = sh := by
      rcases hd with ⟨a, res, hev⟩ | hh
      · exfalso
        exact (EventStep.mem_ne hev) (by rw [hshEq]; simp [Shared.after, Shared.toMem, toMState, execOp])
      · exact hh
    obtain ⟨hsEq, hshEq'⟩ := hstut
    subst s'
    subst sh'
    refine ⟨s, sh, loc', .stutter, ⟨rfl, hlocEq⟩, hinv', hsh', hi, ?_, ?_⟩
    · exact Effect.stutter (SharedRef.ref hs) rfl rfl
    · simp [StepClass, threadStage, popStage, Stage.status, hpc, hlocEq, Local.after, toMState, execOp, upd, rMarker, rHint, rPos, rOk]
  | ahead1 h m q hpc hintEq hintLe hlim slotEq markerEq markerMono hq hq63 hle_q qne posEq =>
    have hq64 : q < 2 ^ 64 := by omega
    have hcond : (toMState sh loc).regs rPos < (half : UInt64) := by
      show loc.regs rPos < UInt64.ofNat (2 ^ 63)
      rw [posEq]
      exact (u64_lt_ofNat_iff (by omega : q - h < 2 ^ 64) (by decide : 2 ^ 63 < 2 ^ 64)).mpr (by omega)
    have hst : opStep popProgram 5 1 (toMState sh loc) = .running 6 0 (toMState sh loc) := by
      simp [opStep, popProgram, eval, hcond]
    rw [hst] at hstep
    cases hstep
    obtain ⟨s', sh', loc', hafter, hinv', hsh', hd⟩ :=
      pop_local_step hi hs hC hpow hCmax hbound hlimitC hpc
        (PopInv.ahead1 h m q hpc hintEq hintLe hlim slotEq markerEq markerMono hq hq63 hle_q qne posEq) hst
    obtain ⟨hshEq, hlocEq⟩ := hafter
    have hstut : s' = s ∧ sh' = sh := by
      rcases hd with ⟨a, res, hev⟩ | hh
      · exfalso
        exact (EventStep.mem_ne hev) (by rw [hshEq]; simp [Shared.after, Shared.toMem, toMState, execOp])
      · exact hh
    obtain ⟨hsEq, hshEq'⟩ := hstut
    subst s'
    subst sh'
    refine ⟨s, sh, loc', .stutter, ⟨rfl, hlocEq⟩, hinv', hsh', hi, ?_, ?_⟩
    · exact Effect.stutter (SharedRef.ref hs) rfl rfl
    · simp [StepClass, threadStage, popStage, Stage.status, hpc, hlocEq, Local.after, toMState, execOp, upd, rMarker, rHint, rPos, rOk]
  | help0 h hpc hintEq hintLe hmark =>
    obtain ⟨s', sh', loc', hafter, hinv', hsh', hd⟩ :=
      pop_local_step hi hs hC hpow hCmax hbound hlimitC hpc
        (PopInv.help0 h hpc hintEq hintLe hmark) hstep
    cases hstep
    obtain ⟨hshEq, hlocEq⟩ := hafter
    have hstut : s' = s ∧ sh' = sh := by
      rcases hd with ⟨a, res, hev⟩ | hh
      · exfalso
        exact (EventStep.mem_ne hev) (by rw [hshEq]; simp [Shared.after, Shared.toMem, toMState, execOp])
      · exact hh
    obtain ⟨hsEq, hshEq'⟩ := hstut
    subst s'
    subst sh'
    refine ⟨s, sh, loc', .stutter, ⟨rfl, hlocEq⟩, hinv', hsh', hi, ?_, ?_⟩
    · exact Effect.stutter (SharedRef.ref hs) rfl rfl
    · simp [StepClass, threadStage, popStage, Stage.status, hpc, hlocEq, Local.after, toMState, execOp, upd, rMarker, rHint, rPos, rOk]
  | help1 h hpc hp =>
    have h63 : h < 2 ^ 63 := by
      have h1 := hp.hintLe
      have h2 := hi.hr_le
      have h3 := hi.hR_le_W
      have h4 := hi.hlimit
      exact Nat.lt_of_le_of_lt (Nat.le_trans h1 (Nat.le_trans h2 (Nat.le_trans h3 h4))) hbound
    have h64 : h < 2 ^ 64 := by omega
    have h2h1 : h + 1 < 2 ^ 64 := by omega
    by_cases hsucc : (toMState sh loc).hintR = (toMState sh loc).regs rHint
    · have hhint : sh.hintR.toNat = h := by
        have hw : sh.hintR = UInt64.ofNat h := by
          have hh := hsucc
          simp only [toMState] at hh
          rw [hp.hintReg] at hh
          exact hh
        rw [hw]
        exact uint64_toNat_ofNat_of_lt h64
      obtain ⟨st', hexec, hev⟩ := popHint_event_of_success hi hs hC hp hhint h2h1
      have hst : opStep popProgram 6 1 (toMState sh loc) = .running 6 2 st' := by
        simp [opStep, popProgram, hexec]
      rw [hst] at hstep
      cases hstep
      refine ⟨{ s with r := s.r + 1 }, sh.after st',
        { loc.after st' with phase := Phase.running 6 2 },
        .event .helpR .helped, ⟨rfl, rfl⟩, PopInv.help2 rfl, ?_,
        EventStep.inv_some hi hev, Effect.event .helpR .helped hev, ?_⟩
      · have href : Ref 0 C { s with r := s.r + 1 } (Shared.toMem (sh.after st')) :=
          EventStep.ref hev
        exact SharedRef.after_shared hs href
      · rw [StepClass]
        exact Or.inr (Or.inl ⟨Or.inr rfl, by
          simp [threadStage, popStage, Local.after, hpc]⟩)
    · let st1 : MState := { toMState sh loc with regs := upd (toMState sh loc).regs rOk 0 }
      have hst : opStep popProgram 6 1 (toMState sh loc) = .running 6 2 st1 := by
        simp [opStep, popProgram, execOp, eval, hsucc, st1]
      rw [hst] at hstep
      cases hstep
      have hsh0 : sh.after st1 = sh := by simp [Shared.after, st1, toMState]
      refine ⟨s, sh.after st1, { loc.after st1 with phase := Phase.running 6 2 },
        .stutter, ⟨rfl, rfl⟩, PopInv.help2 rfl, ?_, hi,
        Effect.stutter (SharedRef.ref hs) rfl (by rw [hsh0]), ?_⟩
      · rwa [hsh0]
      · rw [StepClass]
        exact Or.inl ⟨rfl, by
          simp [threadStage, popStage, Local.after, hpc]⟩
  | help2 hpc =>
    obtain ⟨s', sh', loc', hafter, hinv', hsh', hd⟩ :=
      pop_local_step hi hs hC hpow hCmax hbound hlimitC hpc
        (PopInv.help2 hpc) hstep
    cases hstep
    obtain ⟨hshEq, hlocEq⟩ := hafter
    have hstut : s' = s ∧ sh' = sh := by
      rcases hd with ⟨a, res, hev⟩ | hh
      · exfalso
        exact (EventStep.mem_ne hev) (by rw [hshEq]; simp [Shared.after, Shared.toMem, toMState, execOp])
      · exact hh
    obtain ⟨hsEq, hshEq'⟩ := hstut
    subst s'
    subst sh'
    refine ⟨s, sh, loc', .stutter, ⟨rfl, hlocEq⟩, hinv', hsh', hi, ?_, ?_⟩
    · exact Effect.stutter (SharedRef.ref hs) rfl rfl
    · simp [StepClass, threadStage, popStage, Stage.status, hpc, hlocEq, Local.after, toMState, execOp, upd, rMarker, rHint, rPos, rOk]
  | exhausted hpc =>
    have hst : opStep popProgram 8 0 (toMState sh loc) = .returned 3 (toMState sh loc) := by
      simp [opStep, popProgram, eval]
    rw [hst] at hstep
    cases hstep
    obtain ⟨s', sh', loc', hafter, hinv', hsh', hd⟩ :=
      pop_local_step hi hs hC hpow hCmax hbound hlimitC hpc
        (PopInv.exhausted hpc) hst
    obtain ⟨hshEq, hlocEq⟩ := hafter
    have hstut : s' = s ∧ sh' = sh := by
      rcases hd with ⟨a, res, hev⟩ | hh
      · exfalso
        exact (EventStep.mem_ne hev) (by rw [hshEq]; simp [Shared.after, Shared.toMem, toMState, execOp])
      · exact hh
    obtain ⟨hsEq, hshEq'⟩ := hstut
    subst s'
    subst sh'
    refine ⟨s, sh, loc', .ret 3, ⟨rfl, hlocEq⟩, hinv', hsh', hi, ?_, ?_⟩
    · exact Effect.ret 3 (SharedRef.ref hs) rfl rfl
    · simp [StepClass, threadStage, popStage, Stage.status, RetOutputs, hpc, hlocEq, Local.after, toMState, execOp, upd, rMarker, rHint, rPos, rOk]



/-- The cell-load step of either role: the marker register becomes the
loaded cell marker, the payload register the cell payload, and the hint
register is untouched. -/
theorem load_regs {n : Nat} {kind : Fin n → Kind}
    {g g' : GState n} {i : Fin n}
    (hk : kind i = .push ∨ kind i = .pop)
    (hp : (g.locals i).phase = Phase.running 1 1)
    (hstep : GStep kind g i g') :
    (g'.locals i).phase = Phase.running 1 2 ∧
    (g'.locals i).regs rMarker =
      (g.shared.cells (((g.locals i).regs rSlot).toNat)).marker ∧
    (g'.locals i).regs rHint = (g.locals i).regs rHint := by
  rcases hk with hk | hk
  · have hst : opStep (programOf (kind i)) 1 1 (toMState g.shared (g.locals i)) =
        .running 1 2 { toMState g.shared (g.locals i) with
          regs := upd (upd (toMState g.shared (g.locals i)).regs rMarker
            (g.shared.cells (((g.locals i).regs rSlot).toNat)).marker) rPayload
            (g.shared.cells (((g.locals i).regs rSlot).toNat)).payload } := by
      rw [hk]
      simp [programOf, opStep, pushProgram, execOp, eval, toMState, upd]
    have hg'eq := hstep
    simp only [GStep, hp, hst] at hg'eq
    constructor
    · rw [hg'eq]; simp [updLocal, Local.after]
    constructor
    · rw [hg'eq]; simp [updLocal, Local.after, toMState, upd, rMarker, rHint, rPayload]
    · rw [hg'eq]; simp [updLocal, Local.after, toMState, upd, rMarker, rHint, rPayload]
  · have hst : opStep (programOf (kind i)) 1 1 (toMState g.shared (g.locals i)) =
        .running 1 2 { toMState g.shared (g.locals i) with
          regs := upd (upd (toMState g.shared (g.locals i)).regs rMarker
            (g.shared.cells (((g.locals i).regs rSlot).toNat)).marker) rPayload
            (g.shared.cells (((g.locals i).regs rSlot).toNat)).payload } := by
      rw [hk]
      simp [programOf, opStep, popProgram, execOp, eval, toMState, upd]
    have hg'eq := hstep
    simp only [GStep, hp, hst] at hg'eq
    constructor
    · rw [hg'eq]; simp [updLocal, Local.after]
    constructor
    · rw [hg'eq]; simp [updLocal, Local.after, toMState, upd, rMarker, rHint, rPayload]
    · rw [hg'eq]; simp [updLocal, Local.after, toMState, upd, rMarker, rHint, rPayload]

/-- Package a local certificate into the global tagged step. -/
theorem gstep_tag_aux {n C limit : Nat} {kind : Fin n → Kind}
    {s : AbsState UInt64} {g g' : GState n} {i : Fin n}
    {s' : AbsState UInt64} {sh' : Shared} {loc' : Local} {tag : StepTag UInt64}
    {hC : 0 < C}
    (hi : Inv C limit s) (hg : GRef C limit kind s g)
    (hshared : g'.shared = sh')
    (hother : ∀ j, j ≠ i → g'.locals j = g.locals j)
    (hlocal : g'.locals i = loc')
    (hsh' : SharedRef C limit s' sh') (hinvAbs : Inv C limit s')
    (hinv' : ThreadInv C limit s' sh' loc' (kind i))
    (heff : Effect 0 C limit hC s (Shared.toMem g.shared) s' (Shared.toMem sh') tag)
    (hclass : StepClass (kind i) C (g.locals i) loc' tag) :
    ∃ s' tag, GRef C limit kind s' g' ∧ Inv C limit s' ∧
      Effect 0 C limit hC s (Shared.toMem g.shared) s' (Shared.toMem g'.shared) tag ∧
      StepClass (kind i) C (g.locals i) (g'.locals i) tag := by
  have hmono := Effect.mono heff
  refine ⟨s', tag, ⟨?_, ?_⟩, hinvAbs, ?_, ?_⟩
  · rw [hshared]; exact hsh'
  · intro j
    by_cases hj : j = i
    · subst hj
      rw [hlocal, hshared]
      exact hinv'
    · rw [hother j hj, hshared]
      exact ThreadInv.mono (hg.hlocal j) hmono.1 hmono.2.1 hmono.2.2
  · rw [hshared]; exact heff
  · rw [hlocal]; exact hclass


theorem gstep_tag_push_ns {n C limit k : Nat} {kind : Fin n → Kind}
    {s : AbsState UInt64} {g g' : GState n} {i : Fin n} {pc oi : Nat}
    (hi : Inv C limit s) (hg : GRef C limit kind s g)
    (hC : 0 < C) (hpow : C = 2 ^ k) (hbound : limit < 2 ^ 63)
    (hlimitC : limit + C ≤ 2 ^ 63)
    (hk : kind i = .push)
    (hp : (g.locals i).phase = Phase.running pc oi)
    (hnot : ¬ PushSelected (g.locals i))
    (hstep : GStep kind g i g') :
    ∃ s' tag, GRef C limit kind s' g' ∧ Inv C limit s' ∧
      Effect 0 C limit hC s (Shared.toMem g.shared) s' (Shared.toMem g'.shared) tag ∧
      StepClass .push C (g.locals i) (g'.locals i) tag := by
  have hpinv : PushInv C limit s g.shared (g.locals i) (.running pc oi) := by
    have h1 := hg.hlocal i
    simp only [ThreadInv, hk, hp] at h1
    exact h1
  cases hr : opStep pushProgram pc oi (toMState g.shared (g.locals i)) with
  | running pc' oi' st' =>
    have hcert : PushCert C limit hC s g.shared (g.locals i) (.running pc' oi' st') :=
      push_cert hi hg.hshared hC hpow hbound hlimitC hpinv hnot hr
    obtain ⟨s', sh', loc', tag, hafter, hinv', hsh', hinvAbs, heff, hclass⟩ := hcert
    obtain ⟨hshEq, hlocEq⟩ := hafter
    have hlocPhase : loc'.phase = Phase.running pc' oi' := by rw [hlocEq]
    have hr' : opStep (programOf (kind i)) pc oi (toMState g.shared (g.locals i)) = (.running pc' oi' st') := by
      rw [hk]; exact hr
    have hg'eq : g' = { shared := g.shared.after st', locals := updLocal g.locals i { (g.locals i).after st' with phase := Phase.running pc' oi' } } := by
      have hs := hstep
      simp only [GStep, hp, hr'] at hs
      exact hs
    have hshared : g'.shared = sh' := by rw [hg'eq]; exact hshEq.symm
    have hother : ∀ j, j ≠ i → g'.locals j = g.locals j := by
      intro j hj; rw [hg'eq]; simp [updLocal, hj]
    have hlocal : g'.locals i = loc' := by rw [hg'eq]; simpa [updLocal] using hlocEq.symm
    have hinvT : ThreadInv C limit s' sh' loc' (kind i) := by
      simpa [ThreadInv, hk, hlocPhase] using hinv'
    have hres := gstep_tag_aux (kind := kind) (i := i) (g' := g') (s' := s') (sh' := sh') (loc' := loc') (tag := tag)
      hi hg hshared hother hlocal hsh' hinvAbs hinvT heff (by simpa [hk] using hclass)
    simpa [hk] using hres

  | returned v st' =>
    have hcert : PushCert C limit hC s g.shared (g.locals i) (.returned v st') :=
      push_cert hi hg.hshared hC hpow hbound hlimitC hpinv hnot hr
    obtain ⟨s', sh', loc', tag, hafter, hinv', hsh', hinvAbs, heff, hclass⟩ := hcert
    obtain ⟨hshEq, hlocEq⟩ := hafter
    have hlocPhase : loc'.phase = Phase.returned v := by rw [hlocEq]
    have hr' : opStep (programOf (kind i)) pc oi (toMState g.shared (g.locals i)) = (.returned v st') := by
      rw [hk]; exact hr
    have hg'eq : g' = { shared := g.shared.after st', locals := updLocal g.locals i { (g.locals i).after st' with phase := Phase.returned v } } := by
      have hs := hstep
      simp only [GStep, hp, hr'] at hs
      exact hs
    have hshared : g'.shared = sh' := by rw [hg'eq]; exact hshEq.symm
    have hother : ∀ j, j ≠ i → g'.locals j = g.locals j := by
      intro j hj; rw [hg'eq]; simp [updLocal, hj]
    have hlocal : g'.locals i = loc' := by rw [hg'eq]; simpa [updLocal] using hlocEq.symm
    have hinvT : ThreadInv C limit s' sh' loc' (kind i) := by
      simp [ThreadInv, hk, hlocPhase]
    have hres := gstep_tag_aux (kind := kind) (i := i) (g' := g') (s' := s') (sh' := sh') (loc' := loc') (tag := tag)
      hi hg hshared hother hlocal hsh' hinvAbs hinvT heff (by simpa [hk] using hclass)
    simpa [hk] using hres

  | trapped st' =>
    have hcert : PushCert C limit hC s g.shared (g.locals i) (.trapped st') :=
      push_cert hi hg.hshared hC hpow hbound hlimitC hpinv hnot hr
    obtain ⟨s', sh', loc', tag, hafter, hinv', hsh', hinvAbs, heff, hclass⟩ := hcert
    obtain ⟨hshEq, hlocEq⟩ := hafter
    have hlocPhase : loc'.phase = Phase.trapped := by rw [hlocEq]
    have hr' : opStep (programOf (kind i)) pc oi (toMState g.shared (g.locals i)) = (.trapped st') := by
      rw [hk]; exact hr
    have hg'eq : g' = { shared := g.shared.after st', locals := updLocal g.locals i { (g.locals i).after st' with phase := Phase.trapped } } := by
      have hs := hstep
      simp only [GStep, hp, hr'] at hs
      exact hs
    have hshared : g'.shared = sh' := by rw [hg'eq]; exact hshEq.symm
    have hother : ∀ j, j ≠ i → g'.locals j = g.locals j := by
      intro j hj; rw [hg'eq]; simp [updLocal, hj]
    have hlocal : g'.locals i = loc' := by rw [hg'eq]; simpa [updLocal] using hlocEq.symm
    have hinvT : ThreadInv C limit s' sh' loc' (kind i) := by
      simp [ThreadInv, hk, hlocPhase]
    have hres := gstep_tag_aux (kind := kind) (i := i) (g' := g') (s' := s') (sh' := sh') (loc' := loc') (tag := tag)
      hi hg hshared hother hlocal hsh' hinvAbs hinvT heff (by simpa [hk] using hclass)
    simpa [hk] using hres


theorem gstep_tag_pop_ns {n C limit k : Nat} {kind : Fin n → Kind}
    {s : AbsState UInt64} {g g' : GState n} {i : Fin n} {pc oi : Nat}
    (hi : Inv C limit s) (hg : GRef C limit kind s g)
    (hC : 0 < C) (hpow : C = 2 ^ k) (hCmax : C ≤ 2 ^ 24) (hbound : limit < 2 ^ 63)
    (hlimitC : limit + C ≤ 2 ^ 63)
    (hk : kind i = .pop)
    (hp : (g.locals i).phase = Phase.running pc oi)
    (hnot : ¬ PopSelected (g.locals i))
    (hstep : GStep kind g i g') :
    ∃ s' tag, GRef C limit kind s' g' ∧ Inv C limit s' ∧
      Effect 0 C limit hC s (Shared.toMem g.shared) s' (Shared.toMem g'.shared) tag ∧
      StepClass .pop C (g.locals i) (g'.locals i) tag := by
  have hpinv : PopInv C limit s g.shared (g.locals i) (.running pc oi) := by
    have h1 := hg.hlocal i
    simp only [ThreadInv, hk, hp] at h1
    exact h1
  cases hr : opStep popProgram pc oi (toMState g.shared (g.locals i)) with
  | running pc' oi' st' =>
    have hcert : PopCert C limit hC s g.shared (g.locals i) (.running pc' oi' st') :=
      pop_cert hi hg.hshared hC hpow hCmax hbound hlimitC hpinv hnot hr
    obtain ⟨s', sh', loc', tag, hafter, hinv', hsh', hinvAbs, heff, hclass⟩ := hcert
    obtain ⟨hshEq, hlocEq⟩ := hafter
    have hlocPhase : loc'.phase = Phase.running pc' oi' := by rw [hlocEq]
    have hr' : opStep (programOf (kind i)) pc oi (toMState g.shared (g.locals i)) = (.running pc' oi' st') := by
      rw [hk]; exact hr
    have hg'eq : g' = { shared := g.shared.after st', locals := updLocal g.locals i { (g.locals i).after st' with phase := Phase.running pc' oi' } } := by
      have hs := hstep
      simp only [GStep, hp, hr'] at hs
      exact hs
    have hshared : g'.shared = sh' := by rw [hg'eq]; exact hshEq.symm
    have hother : ∀ j, j ≠ i → g'.locals j = g.locals j := by
      intro j hj; rw [hg'eq]; simp [updLocal, hj]
    have hlocal : g'.locals i = loc' := by rw [hg'eq]; simpa [updLocal] using hlocEq.symm
    have hinvT : ThreadInv C limit s' sh' loc' (kind i) := by
      simpa [ThreadInv, hk, hlocPhase] using hinv'
    have hres := gstep_tag_aux (kind := kind) (i := i) (g' := g') (s' := s') (sh' := sh') (loc' := loc') (tag := tag)
      hi hg hshared hother hlocal hsh' hinvAbs hinvT heff (by simpa [hk] using hclass)
    simpa [hk] using hres

  | returned v st' =>
    have hcert : PopCert C limit hC s g.shared (g.locals i) (.returned v st') :=
      pop_cert hi hg.hshared hC hpow hCmax hbound hlimitC hpinv hnot hr
    obtain ⟨s', sh', loc', tag, hafter, hinv', hsh', hinvAbs, heff, hclass⟩ := hcert
    obtain ⟨hshEq, hlocEq⟩ := hafter
    have hlocPhase : loc'.phase = Phase.returned v := by rw [hlocEq]
    have hr' : opStep (programOf (kind i)) pc oi (toMState g.shared (g.locals i)) = (.returned v st') := by
      rw [hk]; exact hr
    have hg'eq : g' = { shared := g.shared.after st', locals := updLocal g.locals i { (g.locals i).after st' with phase := Phase.returned v } } := by
      have hs := hstep
      simp only [GStep, hp, hr'] at hs
      exact hs
    have hshared : g'.shared = sh' := by rw [hg'eq]; exact hshEq.symm
    have hother : ∀ j, j ≠ i → g'.locals j = g.locals j := by
      intro j hj; rw [hg'eq]; simp [updLocal, hj]
    have hlocal : g'.locals i = loc' := by rw [hg'eq]; simpa [updLocal] using hlocEq.symm
    have hinvT : ThreadInv C limit s' sh' loc' (kind i) := by
      simp [ThreadInv, hk, hlocPhase]
    have hres := gstep_tag_aux (kind := kind) (i := i) (g' := g') (s' := s') (sh' := sh') (loc' := loc') (tag := tag)
      hi hg hshared hother hlocal hsh' hinvAbs hinvT heff (by simpa [hk] using hclass)
    simpa [hk] using hres

  | trapped st' =>
    have hcert : PopCert C limit hC s g.shared (g.locals i) (.trapped st') :=
      pop_cert hi hg.hshared hC hpow hCmax hbound hlimitC hpinv hnot hr
    obtain ⟨s', sh', loc', tag, hafter, hinv', hsh', hinvAbs, heff, hclass⟩ := hcert
    obtain ⟨hshEq, hlocEq⟩ := hafter
    have hlocPhase : loc'.phase = Phase.trapped := by rw [hlocEq]
    have hr' : opStep (programOf (kind i)) pc oi (toMState g.shared (g.locals i)) = (.trapped st') := by
      rw [hk]; exact hr
    have hg'eq : g' = { shared := g.shared.after st', locals := updLocal g.locals i { (g.locals i).after st' with phase := Phase.trapped } } := by
      have hs := hstep
      simp only [GStep, hp, hr'] at hs
      exact hs
    have hshared : g'.shared = sh' := by rw [hg'eq]; exact hshEq.symm
    have hother : ∀ j, j ≠ i → g'.locals j = g.locals j := by
      intro j hj; rw [hg'eq]; simp [updLocal, hj]
    have hlocal : g'.locals i = loc' := by rw [hg'eq]; simpa [updLocal] using hlocEq.symm
    have hinvT : ThreadInv C limit s' sh' loc' (kind i) := by
      simp [ThreadInv, hk, hlocPhase]
    have hres := gstep_tag_aux (kind := kind) (i := i) (g' := g') (s' := s') (sh' := sh') (loc' := loc') (tag := tag)
      hi hg hshared hother hlocal hsh' hinvAbs hinvT heff (by simpa [hk] using hclass)
    simpa [hk] using hres


theorem gstep_tag {n C limit k : Nat} {kind : Fin n → Kind} {s : AbsState UInt64}
    {g g' : GState n} {i : Fin n}
    (hi : Inv C limit s) (hg : GRef C limit kind s g)
    (hC : 0 < C) (hpow : C = 2 ^ k) (hCmax : C ≤ 2 ^ 24)
    (hbound : limit < 2 ^ 63) (hlimitC : limit + C ≤ 2 ^ 63)
    (hstep : GStep kind g i g') :
    ∃ s' tag, GRef C limit kind s' g' ∧ Inv C limit s' ∧
      Effect 0 C limit hC s (Shared.toMem g.shared) s' (Shared.toMem g'.shared) tag ∧
      StepClass (kind i) C (g.locals i) (g'.locals i) tag := by
  cases hk : kind i with
  | push =>
    cases hp : (g.locals i).phase with
    | running pc oi =>
      by_cases hsel : PushSelected (g.locals i)
      · rcases hsel with h01 | h11 | h32
        · obtain ⟨s', tag, hg', hi', heff, hcase⟩ :=
            push_horizon_tag hi hg hC hpow hCmax hbound hlimitC hk h01 hstep
          refine ⟨s', tag, hg', hi', heff, ?_⟩
          rcases hcase with ⟨hge, htag, hpost⟩ | ⟨hge, htag, hpost⟩
          · rw [StepClass]
            simp [threadStage, pushStage, Stage.status, htag, hpost, h01]
          · rw [StepClass]
            simp [threadStage, pushStage, Stage.status, htag, hpost, h01]
        · obtain ⟨hregPhase, hregM, hregH⟩ := load_regs (Or.inl hk) h11 hstep
          obtain ⟨s', tag, hg', hi', heff, hcase⟩ :=
            push_load_tag hi hg hC hpow hCmax hbound hlimitC hk h11 hstep
          refine ⟨s', tag, hg', hi', heff, ?_⟩
          rcases hcase with ⟨hfull, htag, hpost⟩ | ⟨hfull, htag, hpost⟩
          · rw [StepClass]
            simp [threadStage, pushStage, Stage.status, htag, hpost, hregPhase, hregM, hregH, hfull, h11]
          · rw [StepClass]
            simp [threadStage, pushStage, Stage.status, htag, hpost, hregPhase, hregM, hregH, hfull, h11]
        · obtain ⟨s', tag, hg', hi', heff, hcase⟩ :=
            push_cas_tag hi hg hC hpow hCmax hbound hlimitC hk h32 hstep
          refine ⟨s', tag, hg', hi', heff, ?_⟩
          rcases hcase with ⟨h, htag, hpost, hok, hlink⟩ | ⟨htag, hpost, hok⟩
          · rw [StepClass]
            refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, ?_⟩))))))
            exact ⟨(g.locals i).value, h, htag, rfl, hlink,
              by simp [threadStage, pushStage, h32],
              by simp [threadStage, pushStage, hpost, hok]⟩
          · rw [StepClass]
            exact Or.inl ⟨htag, by simp [threadStage, pushStage, h32, hpost, hok]⟩
      · exact gstep_tag_push_ns hi hg hC hpow hbound hlimitC hk hp hsel hstep
    | returned v => simp [GStep, hp] at hstep
    | trapped => simp [GStep, hp] at hstep
  | pop =>
    cases hp : (g.locals i).phase with
    | running pc oi =>
      by_cases hsel : PopSelected (g.locals i)
      · rcases hsel with h01 | h11 | h72
        · obtain ⟨s', tag, hg', hi', heff, hcase⟩ :=
            pop_horizon_tag hi hg hC hpow hCmax hbound hlimitC hk h01 hstep
          refine ⟨s', tag, hg', hi', heff, ?_⟩
          rcases hcase with ⟨hge, htag, hpost⟩ | ⟨hge, htag, hpost⟩
          · rw [StepClass]
            simp [threadStage, popStage, Stage.status, htag, hpost, h01]
          · rw [StepClass]
            simp [threadStage, popStage, Stage.status, htag, hpost, h01]
        · obtain ⟨hregPhase, hregM, hregH⟩ := load_regs (Or.inr hk) h11 hstep
          obtain ⟨s', tag, hg', hi', heff, hcase⟩ :=
            pop_load_tag hi hg hC hpow hCmax hbound hlimitC hk h11 hstep
          refine ⟨s', tag, hg', hi', heff, ?_⟩
          rcases hcase with ⟨heq, heven, htag, hpost⟩ | ⟨hne, htag, hpost⟩
          · rw [StepClass]
            simp [threadStage, popStage, Stage.status, htag, hpost, hregPhase, hregM, hregH, heq, heven, h11]
          · rw [StepClass]
            simp [threadStage, popStage, Stage.status, htag, hpost, hregPhase, hregM, hregH, hne, h11]
        · obtain ⟨s', tag, hg', hi', heff, hcase⟩ :=
            pop_cas_tag hi hg hC hpow hCmax hbound hlimitC hk h72 hstep
          refine ⟨s', tag, hg', hi', heff, ?_⟩
          rcases hcase with ⟨h, p, htag, hpost, hok, hlinkH, hlinkP⟩ | ⟨htag, hpost, hok⟩
          · rw [StepClass]
            refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, ?_⟩)))))))
            exact ⟨h, p, htag, hlinkH, hlinkP,
              by simp [threadStage, popStage, h72],
              by simp [threadStage, popStage, hpost, hok]⟩
          · rw [StepClass]
            exact Or.inl ⟨htag, by simp [threadStage, popStage, h72, hpost, hok]⟩
      · exact gstep_tag_pop_ns hi hg hC hpow hCmax hbound hlimitC hk hp hsel hstep
    | returned v => simp [GStep, hp] at hstep
    | trapped => simp [GStep, hp] at hstep



/-- A kernel step preserves the invoking value of the stepping thread. -/
theorem GStep.value_eq {n : Nat} {kind : Fin n → Kind} {g g' : GState n} {i : Fin n}
    (h : GStep kind g i g') : (g'.locals i).value = (g.locals i).value := by
  cases hp : (g.locals i).phase with
  | running pc oi =>
    cases hr : opStep (programOf (kind i)) pc oi (toMState g.shared (g.locals i)) with
    | running pc' oi' st' =>
      have hs := h; simp only [GStep, hp, hr] at hs
      rw [hs]; simp [updLocal, Local.after]
    | returned v st' =>
      have hs := h; simp only [GStep, hp, hr] at hs
      rw [hs]; simp [updLocal, Local.after]
    | trapped st' =>
      have hs := h; simp only [GStep, hp, hr] at hs
      rw [hs]; simp [updLocal, Local.after]
  | returned v => simp [GStep, hp] at h
  | trapped => simp [GStep, hp] at h

/-- A kernel step touches only the stepping thread's local state. -/
theorem GStep.others {n : Nat} {kind : Fin n → Kind} {g g' : GState n} {i : Fin n}
    (h : GStep kind g i g') : ∀ j, j ≠ i → g'.locals j = g.locals j := by
  intro j hj
  cases hp : (g.locals i).phase with
  | running pc oi =>
    cases hr : opStep (programOf (kind i)) pc oi (toMState g.shared (g.locals i)) with
    | running pc' oi' st' =>
      have hs := h; simp only [GStep, hp, hr] at hs
      rw [hs]; simp [updLocal, hj]
    | returned v st' =>
      have hs := h; simp only [GStep, hp, hr] at hs
      rw [hs]; simp [updLocal, hj]
    | trapped st' =>
      have hs := h; simp only [GStep, hp, hr] at hs
      rw [hs]; simp [updLocal, hj]
  | returned v => simp [GStep, hp] at h
  | trapped => simp [GStep, hp] at h

theorem stageOfOutcome_ne_pre (o : OpOutcome) : stageOfOutcome o ≠ .pre := by
  cases o with
  | success a r => cases a <;> simp [stageOfOutcome]
  | failure k => cases k <;> simp [stageOfOutcome]

/-- Alignment transfers when another thread's local state is unchanged. -/
theorem AlignThread.congr_local {n C limit : Nat} {kind : Fin n → Kind}
    {g g' : GState n} {st : BuildState n} {i : Fin n}
    (h : AlignThread C limit kind g st i) (hloc : g'.locals i = g.locals i) :
    AlignThread C limit kind g' st i := by
  cases hp : st.phase i <;> simp only [AlignThread, hp] at h ⊢
  · rcases h with ⟨v, hv⟩ | hv
    · exact Or.inl ⟨v, by simpa [hloc] using hv⟩
    · exact Or.inr (by simpa [hloc] using hv)
  · rcases h with ⟨hin, hpos, hst⟩
    exact ⟨by simpa [hloc] using hin, hpos, by simpa [hloc] using hst⟩
  · simpa [hloc] using h

/-- The alignment after updating only thread `i`'s scan phase. -/
theorem Align.of_step {n C limit : Nat} {kind : Fin n → Kind} {g g' : GState n}
    {st st' : BuildState n} {i : Fin n}
    (ha : Align C limit kind g st) (hwf : st'.WF) (hpos : st.pos ≤ st'.pos)
    (hphase : ∀ j, j ≠ i → st'.phase j = st.phase j)
    (hothers : ∀ j, j ≠ i → g'.locals j = g.locals j)
    (hi : AlignThread C limit kind g' st' i) :
    Align C limit kind g' st' := by
  refine ⟨hwf, ?_⟩
  intro j
  by_cases hj : j = i
  · subst hj; exact hi
  · have h := AlignThread.congr_local (ha.thread j) (hothers j hj)
    have hpj := hphase j hj
    cases hq : st.phase j
    · simp only [AlignThread, hpj, hq] at h ⊢
      simpa using h
    · simp only [AlignThread, hpj, hq] at h ⊢
      obtain ⟨hin, hposj, hstj⟩ := h
      exact ⟨by simpa using hin, by omega, by simpa using hstj⟩
    · simp only [AlignThread, hpj, hq] at h ⊢
      simpa using h

def OpOutcome.clientEvent : OpOutcome → ClientEvent UInt64
  | .success a r => .step a r
  | .failure k => .obs k

theorem closeLin_outcomes {n : Nat} (id : OpId n) (ret : Nat) (l : List (LinOp n)) :
    (closeLin id ret l).map (fun o => o.outcome.clientEvent) =
      l.map (fun o => o.outcome.clientEvent) := by
  induction l with
  | nil => rfl
  | cons a as ih =>
      by_cases hid : a.id = id
      · by_cases hret : a.ret = none
        · simp [closeLin, hid, hret, ih]
        · simp [closeLin, hid, hret, ih]
      · by_cases hret : a.ret = none
        · simp [closeLin, hid, hret, ih]
        · simp [closeLin, hid, hret, ih]

@[simp] theorem execOp_set_regs_of_ne {r x : Nat} (hx : x ≠ r) (e : Expr) (st : MState) :
    (execOp (.set r e) st).regs x = st.regs x := by
  simp only [execOp, upd]
  exact if_neg hx

theorem push_success_regs {n C limit k : Nat} {kind : Fin n → Kind}
    {s : AbsState UInt64} {g g' : GState n} {i : Fin n}
    (hg : GRef C limit kind s g) (hk : kind i = .push) (hstep : GStep kind g i g')
    (hstage : pushStage C (g.locals i) = .success) :
    (g'.locals i).regs rHint = (g.locals i).regs rHint ∧
    (g'.locals i).regs rPayload = (g.locals i).regs rPayload := by
  have hti := hg.hlocal i
  cases hp : (g.locals i).phase with
  | running pc oi =>
      have hinv : PushInv C limit s g.shared (g.locals i) (.running pc oi) := by
        simpa only [ThreadInv, hk, hp] using hti
      cases hinv with
      | entry => simp_all [pushStage]
      | hint => simp_all [pushStage]
      | check => simp_all [pushStage]
      | slot => simp_all [pushStage]
      | load h m q hpc hintEq hintLe hlim slotEq markerEq hm64 markerMono hq hq63 hfull =>
          by_cases hc : ((g.locals i).regs rMarker).toNat / 2 + C = ((g.locals i).regs rHint).toNat
          · simp [pushStage, hpc, hc] at hstage
          · simp [pushStage, hpc, hc] at hstage
      | pos h m q hpc hintEq hintLe hlim slotEq markerEq markerMono posEq hq hq63 hfull =>
          by_cases hc : ((g.locals i).regs rMarker).toNat / 2 + C = ((g.locals i).regs rHint).toNat
          · simp [pushStage, hpc, hc] at hstage
          · simp [pushStage, hpc, hc] at hstage
      | readyTest => simp_all [pushStage]
      | evenTest => simp_all [pushStage]
      | cas0 => simp_all [pushStage]
      | cas1 => simp_all [pushStage]
      | cas => simp_all [pushStage]
      | casFail hpc hok => simp_all [pushStage, hok]
      | casOk h hpc hok hintEq hintLe hmark =>
          have hst : opStep pushProgram 3 3 (toMState g.shared (g.locals i)) = .running 4 0 (toMState g.shared (g.locals i)) := by
            simp only [opStep, pushProgram, toMState]
            by_cases h0 : (g.locals i).regs rOk = 0
            · simp [eval, h0] at hok
            · simp [eval, h0]
          have hg' := hstep
          simp only [GStep, hk, hpc, hst] at hg'
          rw [hg']
          simp [Local.after, updLocal, if_true, toMState, execOp, eval, upd, rHint, rPayload, rTmp2]
      | hintPath0 h hpc hintEq hintLe hmark =>
          have hst : opStep pushProgram 4 0 (toMState g.shared (g.locals i)) = .running 4 1 { toMState g.shared (g.locals i) with out0 := (toMState g.shared (g.locals i)).regs rHint } := by simp [opStep, pushProgram, execOp, eval, toMState]
          have hg' := hstep
          simp only [GStep, hk, hpc, hst] at hg'
          rw [hg']
          simp [Local.after, updLocal, if_true, toMState, execOp, eval, upd, rHint, rPayload, rTmp2]
      | hintPath1 h hpc hintEq hintLe hmark outEq =>
          have hst : opStep pushProgram 4 1 (toMState g.shared (g.locals i)) = .running 4 2 { toMState g.shared (g.locals i) with regs := upd (toMState g.shared (g.locals i)).regs rTmp2 ((toMState g.shared (g.locals i)).regs rHint + 1) } := by simp [opStep, pushProgram, execOp, eval, toMState]
          have hg' := hstep
          simp only [GStep, hk, hpc, hst] at hg'
          rw [hg']
          simp only [updLocal, if_true, Local.after, toMState]
          constructor
          · rw [execOp_set_regs_of_ne (by decide : rHint ≠ rTmp2)]
          · rw [execOp_set_regs_of_ne (by decide : rPayload ≠ rTmp2)]
      | hintPath2 h hpc hp outEq =>
          have hst : opStep pushProgram 4 2 (toMState g.shared (g.locals i)) = .running 4 3 (execOp (Op.casHint rOk Hint.write (Expr.var rHint) (Expr.var rTmp2) MemOrd.release) (toMState g.shared (g.locals i))) := by simp [opStep, pushProgram, execOp, eval, toMState]
          have hg' := hstep
          simp only [GStep, hk, hpc, hst] at hg'
          rw [hg']
          simp only [updLocal, if_true, Local.after, toMState]
          constructor
          · rw [execOp_casHint_regs_of_ne (by decide : rHint ≠ rOk)]
          · rw [execOp_casHint_regs_of_ne (by decide : rPayload ≠ rOk)]
      | hintPath3 h hpc hintEq outEq =>
          have hst : opStep pushProgram 4 3 (toMState g.shared (g.locals i)) = .returned 0 (toMState g.shared (g.locals i)) := by simp [opStep, pushProgram, execOp, eval, toMState]
          have hg' := hstep
          simp only [GStep, hk, hpc, hst] at hg'
          rw [hg']
          simp [Local.after, updLocal, if_true, toMState, execOp, eval, upd, rHint, rPayload, rTmp2]
      | fullAhead h m q hpc hintEq hintLe hlim slotEq markerEq hq hfull hqC posEq =>
          by_cases hc : ((g.locals i).regs rMarker).toNat / 2 + C = ((g.locals i).regs rHint).toNat
          · simp [pushStage, hpc, hc] at hstage
          · simp [pushStage, hpc, hc] at hstage
      | fullAhead1 h m q hpc hintEq hintLe hlim slotEq markerEq hq hfull hqC posEq =>
          by_cases hc : ((g.locals i).regs rMarker).toNat / 2 + C = ((g.locals i).regs rHint).toNat
          · simp [pushStage, hpc, hc] at hstage
          · simp [pushStage, hpc, hc] at hstage
      | ahead h m q hpc hintEq hintLe hlim slotEq markerEq markerMono hq hq63 hfull hltq posEq =>
          by_cases hc : ((g.locals i).regs rMarker).toNat / 2 + C = ((g.locals i).regs rHint).toNat
          · simp [pushStage, hpc, hc] at hstage
          · simp [pushStage, hpc, hc] at hstage
      | ahead1 h m q hpc hintEq hintLe hlim slotEq markerEq markerMono hq hq63 hltq posEq =>
          by_cases hc : ((g.locals i).regs rMarker).toNat / 2 + C = ((g.locals i).regs rHint).toNat
          · simp [pushStage, hpc, hc] at hstage
          · simp [pushStage, hpc, hc] at hstage
      | full => simp_all [pushStage]
      | help0 => simp_all [pushStage]
      | help1 => simp_all [pushStage]
      | help2 => simp_all [pushStage]
      | help3 => simp_all [pushStage]
      | exhausted => simp_all [pushStage]
  | returned v => simp_all [pushStage]
  | trapped => simp_all [pushStage]

theorem pop_success_regs {n C limit k : Nat} {kind : Fin n → Kind}
    {s : AbsState UInt64} {g g' : GState n} {i : Fin n}
    (hg : GRef C limit kind s g) (hk : kind i = .pop) (hstep : GStep kind g i g')
    (hstage : popStage C (g.locals i) = .success) :
    (g'.locals i).regs rHint = (g.locals i).regs rHint ∧
    (g'.locals i).regs rPayload = (g.locals i).regs rPayload := by
  have hti := hg.hlocal i
  cases hp : (g.locals i).phase with
  | running pc oi =>
      have hinv : PopInv C limit s g.shared (g.locals i) (.running pc oi) := by
        simpa only [ThreadInv, hk, hp] using hti
      cases hinv with
      | entry => simp_all [popStage]
      | hint => simp_all [popStage]
      | check => simp_all [popStage]
      | slot => simp_all [popStage]
      | load h m q hpc hintEq hintLe hlim slotEq markerEq hm64 markerMono hq hq63 hle_q =>
          by_cases hc : ((g.locals i).regs rMarker).toNat / 2 = ((g.locals i).regs rHint).toNat ∧ ((g.locals i).regs rMarker).toNat % 2 = 0
          · simp [popStage, hpc, hc] at hstage
          · simp [popStage, hpc, hc] at hstage
      | pos h m q hpc hintEq hintLe hlim slotEq markerEq hm64 markerMono posEq hq hq63 hle_q =>
          by_cases hc : ((g.locals i).regs rMarker).toNat / 2 = ((g.locals i).regs rHint).toNat ∧ ((g.locals i).regs rMarker).toNat % 2 = 0
          · simp [popStage, hpc, hc] at hstage
          · simp [popStage, hpc, hc] at hstage
      | readyTest h m q hpc hintEq hintLe hlim slotEq markerEq markerMono posEq hq hq63 hle_q qeq =>
          by_cases hc : ((g.locals i).regs rMarker).toNat / 2 = ((g.locals i).regs rHint).toNat ∧ ((g.locals i).regs rMarker).toNat % 2 = 0
          · simp [popStage, hpc, hc] at hstage
          · simp [popStage, hpc, hc] at hstage
      | evenTest h m q hpc hintEq hintLe hlim slotEq markerEq markerMono posEq hq hq63 hle_q qeq tmp0Eq =>
          by_cases hc : ((g.locals i).regs rMarker).toNat / 2 = ((g.locals i).regs rHint).toNat ∧ ((g.locals i).regs rMarker).toNat % 2 = 0
          · simp [popStage, hpc, hc] at hstage
          · simp [popStage, hpc, hc] at hstage
      | empty => simp_all [popStage]
      | cas0 => simp_all [popStage]
      | cas1 => simp_all [popStage]
      | cas => simp_all [popStage]
      | casFail hpc hok => simp_all [popStage, hok]
      | casOk h hpc hok hintEq hintLe hmark =>
          have hst : opStep popProgram 7 3 (toMState g.shared (g.locals i)) = .running 4 0 (toMState g.shared (g.locals i)) := by
            simp only [opStep, popProgram, toMState]
            by_cases h0 : (g.locals i).regs rOk = 0
            · simp [eval, h0] at hok
            · simp [eval, h0]
          have hg' := hstep
          simp only [GStep, hk, hpc, hst] at hg'
          rw [hg']
          simp [Local.after, updLocal, if_true, toMState, execOp, eval, upd, rHint, rPayload, rTmp2]
      | out0 h hpc hintEq hintLe hmark =>
          have hst : opStep popProgram 4 0 (toMState g.shared (g.locals i)) = .running 4 1 { toMState g.shared (g.locals i) with out0 := (toMState g.shared (g.locals i)).regs rPayload } := by simp [opStep, popProgram, execOp, eval, toMState]
          have hg' := hstep
          simp only [GStep, hk, hpc, hst] at hg'
          rw [hg']
          simp [Local.after, updLocal, if_true, toMState, execOp, eval, upd, rHint, rPayload, rTmp2]
      | out1 h hpc hintEq hintLe hmark out0Eq =>
          have hst : opStep popProgram 4 1 (toMState g.shared (g.locals i)) = .running 4 2 { toMState g.shared (g.locals i) with out1 := (toMState g.shared (g.locals i)).regs rHint } := by simp [opStep, popProgram, execOp, eval, toMState]
          have hg' := hstep
          simp only [GStep, hk, hpc, hst] at hg'
          rw [hg']
          simp [Local.after, updLocal, if_true, toMState, execOp, eval, upd, rHint, rPayload, rTmp2]
      | out2 h hpc hintEq hintLe hmark out0Eq out1Eq =>
          have hst : opStep popProgram 4 2 (toMState g.shared (g.locals i)) = .running 4 3 { toMState g.shared (g.locals i) with regs := upd (toMState g.shared (g.locals i)).regs rTmp2 ((toMState g.shared (g.locals i)).regs rHint + 1) } := by simp [opStep, popProgram, execOp, eval, toMState]
          have hg' := hstep
          simp only [GStep, hk, hpc, hst] at hg'
          rw [hg']
          simp only [updLocal, if_true, Local.after, toMState]
          constructor
          · rw [execOp_set_regs_of_ne (by decide : rHint ≠ rTmp2)]
          · rw [execOp_set_regs_of_ne (by decide : rPayload ≠ rTmp2)]
      | out3 h hpc hp out0Eq out1Eq =>
          have hst : opStep popProgram 4 3 (toMState g.shared (g.locals i)) = .running 4 4 (execOp (Op.casHint rOk Hint.read (Expr.var rHint) (Expr.var rTmp2) MemOrd.release) (toMState g.shared (g.locals i))) := by simp [opStep, popProgram, execOp, eval, toMState]
          have hg' := hstep
          simp only [GStep, hk, hpc, hst] at hg'
          rw [hg']
          simp only [updLocal, if_true, Local.after, toMState]
          constructor
          · rw [execOp_casHint_regs_of_ne (by decide : rHint ≠ rOk)]
          · rw [execOp_casHint_regs_of_ne (by decide : rPayload ≠ rOk)]
      | out4 h hpc hintEq out0Eq out1Eq =>
          have hst : opStep popProgram 4 4 (toMState g.shared (g.locals i)) = .returned 0 (toMState g.shared (g.locals i)) := by simp [opStep, popProgram, execOp, eval, toMState]
          have hg' := hstep
          simp only [GStep, hk, hpc, hst] at hg'
          rw [hg']
          simp [Local.after, updLocal, if_true, toMState, execOp, eval, upd, rHint, rPayload, rTmp2]
      | ahead => simp_all [popStage]
      | ahead1 => simp_all [popStage]
      | help0 => simp_all [popStage]
      | help1 => simp_all [popStage]
      | help2 => simp_all [popStage]
      | exhausted => simp_all [popStage]
  | returned v => simp_all [popStage]
  | trapped => simp_all [popStage]


/-- A neutral kernel step preserves the outcome/register link: the registers
the success-path output stores copy are untouched by any step whose stage is
the outcome's stage. -/
theorem OutcomeRegs.step {n C limit k : Nat} {kind : Fin n → Kind}
    {s : AbsState UInt64} {g g' : GState n} {i : Fin n}
    (hg : GRef C limit kind s g) (hstep : GStep kind g i g')
    {o : OpOutcome}
    (hkind : OutcomeKind (kind i) o)
    (hstage : threadStage C (kind i) (g.locals i) = stageOfOutcome o)
    (hregs : OutcomeRegs (n := n) o (g.locals i)) :
    OutcomeRegs (n := n) o (g'.locals i) := by
  cases o with
  | success a r =>
      cases a with
      | push v =>
          cases r with
          | pushed h =>
              have hk : kind i = .push := hkind
              have hs : pushStage C (g.locals i) = .success := by
                rw [hk] at hstage
                simpa [threadStage, stageOfOutcome] using hstage
              have hmono := push_success_regs (k := 0) hg hk hstep hs
              simpa [OutcomeRegs] using (hmono.1.trans hregs)
          | popped h p => simp [OutcomeRegs]
          | helped => simp [OutcomeRegs]
      | pop =>
          cases r with
          | popped h p =>
              have hk : kind i = .pop := hkind
              have hs : popStage C (g.locals i) = .success := by
                rw [hk] at hstage
                simpa [threadStage, stageOfOutcome] using hstage
              have hmono := pop_success_regs (k := 0) hg hk hstep hs
              exact ⟨hmono.1.trans hregs.1, hmono.2.trans hregs.2⟩
          | pushed h => simp [OutcomeRegs]
          | helped => simp [OutcomeRegs]
      | helpW => simp [OutcomeRegs]
      | helpR => simp [OutcomeRegs]
  | failure k => simp [OutcomeRegs]


theorem StepClass.ret_outputs {n : Nat} {kind : Kind} {C : Nat} {loc loc' : Local}
    {status : UInt64} (h : StepClass kind C loc loc' (.ret status)) :
    RetOutputs kind C loc := by
  rcases h with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _, _, _⟩ | ⟨h, _, _, _⟩ | ⟨h, _, _, _⟩ |
    ⟨h, _, _, _⟩ | ⟨_, _, _, h, _, _, _, _⟩ | ⟨_, _, _, h, _, _, _, _⟩ | ⟨_, _, h⟩
  · cases h
  · rcases h with h | h <;> cases h
  · cases h
  · cases h
  · cases h
  · cases h
  · cases h
  · cases h
  · obtain ⟨v, hv, hro⟩ := h; exact hro

/-- A return observation: the position, the linearized record, the thread,
the returned status, and the registers the caller observes. -/
structure RetObs (n : Nat) where
  pos : Nat
  lin : Nat
  thread : Fin n
  status : UInt64
  outcome : OpOutcome
  /-- The kernel thread's local state at the return step. -/
  loc : Local

/-- The observation fits one schedule move: same position and thread, the
move is the matching return, and the observed outputs are the results of the
recorded outcome. -/
def RetObs.Fits {n : Nat} (r : RetObs n) (pos : Nat) (i : Fin n) (tag : StepTag UInt64) : Prop :=
  r.pos = pos ∧ r.thread = i ∧
  (∀ v h, r.outcome = .success (.push v) (.pushed h) → r.loc.out0 = UInt64.ofNat h) ∧
  (∀ h p, r.outcome = .success .pop (.popped h p) → r.loc.out0 = p ∧ r.loc.out1 = UInt64.ofNat h) ∧
  r.status = (stageOfOutcome r.outcome).status ∧
  (match tag with | .ret status => r.status = status | _ => False)

/-- The observation fits a whole schedule suffix: its position lies inside
the suffix, the indexed move is its return, and its outputs are the results
of its recorded outcome. -/
def RetObs.OK {n : Nat} (r : RetObs n) (base len : Nat)
    (tags : List (Fin n × StepTag UInt64)) : Prop :=
  base ≤ r.pos ∧ r.pos < base + len ∧
  tags[r.pos - base]? = some (r.thread, .ret r.status) ∧
  (∀ v h, r.outcome = .success (.push v) (.pushed h) → r.loc.out0 = UInt64.ofNat h) ∧
  (∀ h p, r.outcome = .success .pop (.popped h p) → r.loc.out0 = p ∧ r.loc.out1 = UInt64.ofNat h) ∧
  r.status = (stageOfOutcome r.outcome).status

theorem RetObs.sound {n C limit : Nat} {kind : Fin n → Kind}
    {g g' : GState n} {st : BuildState n} {i : Fin n} {o : LinOp n} {status : UInt64}
    (halign : Align C limit kind g st) (hph : st.phase i = ThreadPhase.linearized o)
    (hclass : StepClass (kind i) C (g.locals i) (g'.locals i) (.ret status)) :
    (∀ v h, o.outcome = .success (.push v) (.pushed h) → (g.locals i).out0 = UInt64.ofNat h) ∧
    (∀ h p, o.outcome = .success .pop (.popped h p) →
      (g.locals i).out0 = p ∧ (g.locals i).out1 = UInt64.ofNat h) := by
  constructor
  · intro v h hout
    have hth := halign.thread i
    simp only [AlignThread, hph] at hth
    obtain ⟨hstageO, hkindO, hregsO⟩ := hth
    have hro := StepClass.ret_outputs (n := n) hclass
    rw [hout] at hstageO hkindO hregsO
    rw [hkindO] at hstageO hro
    simp only [RetOutputs] at hro
    have hs : pushStage C (g.locals i) = .success := by
      simpa [threadStage, stageOfOutcome] using hstageO
    have hout0 := hro hs
    rw [hregsO] at hout0
    exact hout0.trans UInt64.ofNat_toNat
  · intro h p hout
    have hth := halign.thread i
    simp only [AlignThread, hph] at hth
    obtain ⟨hstageO, hkindO, hregsO⟩ := hth
    have hro := StepClass.ret_outputs (n := n) hclass
    rw [hout] at hstageO hkindO hregsO
    rw [hkindO] at hstageO hro
    simp only [RetOutputs] at hro
    have hs : popStage C (g.locals i) = .success := by
      simpa [threadStage, stageOfOutcome] using hstageO
    obtain ⟨ho0, ho1⟩ := hro hs
    obtain ⟨hh, hp⟩ := hregsO
    refine ⟨?_, ?_⟩
    · rw [ho0]; exact hp
    · rw [ho1, hh]
      exact UInt64.ofNat_toNat

/-- A record fitting one move fits that move prepended to a suffix. -/
theorem RetObs.fits_ok {n : Nat} {r : RetObs n} {pos msLen : Nat} {i : Fin n}
    {tag : StepTag UInt64} {tags : List (Fin n × StepTag UInt64)}
    (h : r.Fits pos i tag) :
    r.OK pos (msLen + 1) ((i, tag) :: tags) := by
  simp only [RetObs.Fits, RetObs.OK] at h ⊢
  obtain ⟨hpos, hthread, hs1, hs2, hstat, htag⟩ := h
  rw [hpos, hthread]
  cases tag with
  | ret status =>
      simp only at htag
      subst htag
      refine ⟨by omega, by omega, ?_, hs1, hs2, hstat⟩
      simp
  | stutter => simp at htag
  | event a r => simp at htag
  | obs k => simp at htag

/-- A record fitting a suffix also fits the move shifted in front of it. -/
theorem RetObs.ok_shift {n : Nat} {r : RetObs n} {base len : Nat} {i : Fin n}
    {tag : StepTag UInt64} {tags : List (Fin n × StepTag UInt64)}
    (h : r.OK (base + 1) len tags) :
    r.OK base (len + 1) ((i, tag) :: tags) := by
  simp only [RetObs.OK] at h ⊢
  obtain ⟨hge, hlt, hget, hs1, hs2, hstat⟩ := h
  have hidx : r.pos - base = (r.pos - (base + 1)) + 1 := by omega
  refine ⟨by omega, by omega, ?_, hs1, hs2, hstat⟩
  rw [hidx]
  simpa using hget

/-- Every linearized phase's record is already accumulated in `linOps`. -/
def BuildState.LinMem (st : BuildState n) : Prop :=
  ∀ i o, st.phase i = .linearized o → o ∈ st.linOps

/-- A phase's record belongs to the phase's thread. -/
def BuildState.ThreadOK (st : BuildState n) : Prop :=
  (∀ i o, st.phase i = .linearized o → o.id.thread = i) ∧
  (∀ i p, st.phase i = .invoked p → p.id.thread = i) ∧
  (∀ i o, st.phase i = .linearized o → o.ret = none)

theorem closeLin_exists {n : Nat} (id : OpId n) (ret : Nat) (l : List (LinOp n)) :
    ∀ {x : LinOp n}, x ∈ l →
      ∃ x' ∈ closeLin id ret l, x'.lin = x.lin ∧ x'.outcome = x.outcome ∧ x'.id = x.id := by
  induction l with
  | nil => intro x hx; simp at hx
  | cons a as ih =>
      intro x hx
      simp only [closeLin]
      rcases List.mem_cons.mp hx with hxa | hx
      · subst x
        by_cases hc : a.id = id ∧ a.ret = none
        · rw [if_pos hc]
          exact ⟨{ a with ret := some ret }, List.mem_cons_self, rfl, rfl, rfl⟩
        · rw [if_neg hc]
          exact ⟨a, List.mem_cons_self, rfl, rfl, rfl⟩
      · obtain ⟨x', hx', h1, h2, h3⟩ := ih hx
        exact ⟨x', List.mem_cons_of_mem _ hx', h1, h2, h3⟩

theorem closeLin_exists_id {n : Nat} (id : OpId n) (ret : Nat) (l : List (LinOp n)) :
    ∀ {x : LinOp n}, x.id = id → x.ret = none → x ∈ l →
      ∃ x' ∈ closeLin id ret l, x'.lin = x.lin ∧ x'.outcome = x.outcome ∧
        x'.id = x.id ∧ x'.ret = some ret := by
  induction l with
  | nil => intro x hid hret hx; simp at hx
  | cons a as ih =>
      intro x hid hret hx
      simp only [closeLin]
      rcases List.mem_cons.mp hx with hxa | hx
      · subst x
        rw [if_pos (show a.id = id ∧ a.ret = none from ⟨hid, hret⟩)]
        exact ⟨{ a with ret := some ret }, List.mem_cons_self, rfl, rfl, rfl, rfl⟩
      · by_cases ha : a.id = id ∧ a.ret = none
        · rw [if_pos ha]
          obtain ⟨x', hx', h1, h2, h3, h4⟩ := ih hid hret hx
          exact ⟨x', List.mem_cons_of_mem _ hx', h1, h2, h3, h4⟩
        · rw [if_neg ha]
          obtain ⟨x', hx', h1, h2, h3, h4⟩ := ih hid hret hx
          exact ⟨x', List.mem_cons_of_mem _ hx', h1, h2, h3, h4⟩

theorem BuildState.close_lin_exists {n : Nat} {st : BuildState n} {i : Fin n}
    {o x : LinOp n} (hx : x ∈ st.linOps) :
    ∃ x' ∈ (st.close i o).linOps, x'.lin = x.lin ∧ x'.outcome = x.outcome ∧ x'.id = x.id := by
  obtain ⟨x', hx1, h1, h2, h3⟩ := closeLin_exists o.id st.pos st.linOps hx
  refine ⟨x', ?_, h1, h2, h3⟩
  rw [BuildState.close_linOps]
  exact hx1

theorem BuildState.close_lin_exists_id {n : Nat} {st : BuildState n} {i : Fin n}
    {o x : LinOp n} (hid : x.id = o.id) (hret : x.ret = none) (hx : x ∈ st.linOps) :
    ∃ x' ∈ (st.close i o).linOps, x'.lin = x.lin ∧ x'.outcome = x.outcome ∧
      x'.id = x.id ∧ x'.ret = some st.pos := by
  obtain ⟨x', hx1, h1, h2, h3, h4⟩ := closeLin_exists_id o.id st.pos st.linOps hid hret hx
  refine ⟨x', ?_, h1, h2, h3, h4⟩
  rw [BuildState.close_linOps]
  exact hx1

theorem BuildState.linMem_init : (BuildState.init n).LinMem := by
  intro i o h; simp [BuildState.init] at h

theorem BuildState.threadOK_init : (BuildState.init n).ThreadOK := by
  refine ⟨?_, ?_, ?_⟩ <;> intro i o h <;> simp [BuildState.init] at h

theorem BuildState.linMem_advance {st : BuildState n} (h : st.LinMem) :
    st.advance.LinMem := by
  intro i o ho
  simp only [BuildState.advance_phase] at ho
  simpa [BuildState.advance_linOps] using h i o ho

theorem BuildState.threadOK_advance {st : BuildState n} (h : st.ThreadOK) :
    st.advance.ThreadOK := by
  refine ⟨?_, ?_, ?_⟩
  · intro i o ho; simp only [BuildState.advance_phase] at ho; exact h.1 i o ho
  · intro i p hp; simp only [BuildState.advance_phase] at hp; exact h.2.1 i p hp
  · intro i o ho; simp only [BuildState.advance_phase] at ho; exact h.2.2 i o ho

theorem BuildState.linMem_openInvoke {st : BuildState n} {i : Fin n} {v : UInt64}
    (h : st.LinMem) : (st.openInvoke i v).LinMem := by
  intro j o ho
  by_cases hj : j = i
  · subst hj
    simp only [BuildState.openInvoke_phase, setFun_same] at ho
    cases ho
  · have ho' : st.phase j = .linearized o := by
      simpa [BuildState.openInvoke_phase, setFun_of_ne _ _ hj] using ho
    simpa [BuildState.openInvoke_linOps] using h j o ho'

theorem BuildState.threadOK_openInvoke {st : BuildState n} {i : Fin n} {v : UInt64}
    (h : st.ThreadOK) : (st.openInvoke i v).ThreadOK := by
  refine ⟨?_, ?_, ?_⟩
  · intro j o ho
    by_cases hj : j = i
    · subst hj
      simp only [BuildState.openInvoke_phase, setFun_same] at ho
      cases ho
    · have ho' : st.phase j = .linearized o := by
        simpa [BuildState.openInvoke_phase, setFun_of_ne _ _ hj] using ho
      exact h.1 j o ho'
  · intro j p hp
    by_cases hj : j = i
    · subst hj
      simp only [BuildState.openInvoke_phase, setFun_same] at hp
      cases hp
      rfl
    · have hp' : st.phase j = .invoked p := by
        simpa [BuildState.openInvoke_phase, setFun_of_ne _ _ hj] using hp
      exact h.2.1 j p hp'
  · intro j o ho
    by_cases hj : j = i
    · subst hj
      simp only [BuildState.openInvoke_phase, setFun_same] at ho
      cases ho
    · have ho' : st.phase j = .linearized o := by
        simpa [BuildState.openInvoke_phase, setFun_of_ne _ _ hj] using ho
      exact h.2.2 j o ho'

theorem BuildState.linMem_linearize {st : BuildState n} {i : Fin n} {p : PendingOp n}
    {outcome : OpOutcome} {hinv : p.inv < st.pos} (h : st.LinMem)
    (hth : st.ThreadOK) (hp : st.phase i = .invoked p) :
    (st.linearize i p outcome hinv).LinMem := by
  intro j o ho
  by_cases hj : j = i
  · subst hj
    simp only [BuildState.linearize_phase, setFun_same] at ho
    cases ho
    simp only [BuildState.linearize_linOps]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  · have ho' : st.phase j = .linearized o := by
      simpa [BuildState.linearize_phase, setFun_of_ne _ _ hj] using ho
    simp only [BuildState.linearize_linOps]
    exact List.mem_append_left _ (h j o ho')

theorem BuildState.threadOK_linearize {st : BuildState n} {i : Fin n} {p : PendingOp n}
    {outcome : OpOutcome} {hinv : p.inv < st.pos} (h : st.ThreadOK)
    (hp : st.phase i = .invoked p) :
    (st.linearize i p outcome hinv).ThreadOK := by
  have hpi := h.2.1 i p hp
  refine ⟨?_, ?_, ?_⟩
  · intro j o ho
    by_cases hj : j = i
    · subst hj
      simp only [BuildState.linearize_phase, setFun_same] at ho
      cases ho
      simpa [BuildState.mkLinOp] using hpi
    · have ho' : st.phase j = .linearized o := by
        simpa [BuildState.linearize_phase, setFun_of_ne _ _ hj] using ho
      exact h.1 j o ho'
  · intro j q hq
    by_cases hj : j = i
    · subst hj
      simp only [BuildState.linearize_phase, setFun_same] at hq
      cases hq
    · have hq' : st.phase j = .invoked q := by
        simpa [BuildState.linearize_phase, setFun_of_ne _ _ hj] using hq
      exact h.2.1 j q hq'
  · intro j o ho
    by_cases hj : j = i
    · subst hj
      simp only [BuildState.linearize_phase, setFun_same] at ho
      cases ho
      rfl
    · have ho' : st.phase j = .linearized o := by
        simpa [BuildState.linearize_phase, setFun_of_ne _ _ hj] using ho
      exact h.2.2 j o ho'

theorem closeLin_mem_of_ne {id : OpId n} {ret : Nat} {l : List (LinOp n)} {a : LinOp n}
    (hid : a.id ≠ id) (ha : a ∈ l) : a ∈ closeLin id ret l := by
  induction l with
  | nil => simp at ha
  | cons b bs ih =>
      by_cases hb : b.id = id
      · simp only [closeLin, hb, ↓reduceIte]
        rcases List.mem_cons.mp ha with rfl | ha
        · exact absurd hb hid
        · exact List.mem_cons_of_mem _ (ih ha)
      · simp only [closeLin, hb, ↓reduceIte]
        rcases List.mem_cons.mp ha with rfl | ha
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (ih ha)

theorem BuildState.linMem_close {st : BuildState n} {i : Fin n} {o : LinOp n}
    (h : st.LinMem) (hth : st.ThreadOK) (hp : st.phase i = .linearized o) :
    (st.close i o).LinMem := by
  have ho_thread := hth.1 i o hp
  intro j q hq
  by_cases hj : j = i
  · subst hj
    simp only [BuildState.close_phase, setFun_same] at hq
    cases hq
  · have hq' : st.phase j = .linearized q := by
      simpa [BuildState.close_phase, setFun_of_ne _ _ hj] using hq
    have hq_mem := h j q hq'
    have hq_thread := hth.1 j q hq'
    have hne : q.id ≠ o.id := by
      intro heq
      have h1 : q.id.thread = o.id.thread := congrArg OpId.thread heq
      rw [hq_thread, ho_thread] at h1
      exact hj h1
    simp only [BuildState.close_linOps]
    exact closeLin_mem_of_ne hne hq_mem

theorem BuildState.threadOK_close {st : BuildState n} {i : Fin n} {o : LinOp n}
    (h : st.ThreadOK) (hp : st.phase i = .linearized o) :
    (st.close i o).ThreadOK := by
  refine ⟨?_, ?_, ?_⟩
  · intro j q hq
    by_cases hj : j = i
    · subst hj
      simp only [BuildState.close_phase, setFun_same] at hq
      cases hq
    · have hq' : st.phase j = .linearized q := by
        simpa [BuildState.close_phase, setFun_of_ne _ _ hj] using hq
      exact h.1 j q hq'
  · intro j p hq
    by_cases hj : j = i
    · subst hj
      simp only [BuildState.close_phase, setFun_same] at hq
      cases hq
    · have hq' : st.phase j = .invoked p := by
        simpa [BuildState.close_phase, setFun_of_ne _ _ hj] using hq
      exact h.2.1 j p hq'
  · intro j q hq
    by_cases hj : j = i
    · subst hj
      simp only [BuildState.close_phase, setFun_same] at hq
      cases hq
    · have hq' : st.phase j = .linearized q := by
        simpa [BuildState.close_phase, setFun_of_ne _ _ hj] using hq
      exact h.2.2 j q hq'

theorem BuildState.linMem_dropPending {st : BuildState n} {i : Fin n} (h : st.LinMem) :
    (st.dropPending i).LinMem := by
  intro j o ho
  by_cases hj : j = i
  · subst hj
    simp only [BuildState.dropPending_phase, setFun_same] at ho
    cases ho
  · have ho' : st.phase j = .linearized o := by
      simpa [BuildState.dropPending_phase, setFun_of_ne _ _ hj] using ho
    simpa [BuildState.dropPending_linOps] using h j o ho'

theorem BuildState.threadOK_dropPending {st : BuildState n} {i : Fin n} (h : st.ThreadOK) :
    (st.dropPending i).ThreadOK := by
  refine ⟨?_, ?_, ?_⟩
  · intro j o ho
    by_cases hj : j = i
    · subst hj
      simp only [BuildState.dropPending_phase, setFun_same] at ho
      cases ho
    · have ho' : st.phase j = .linearized o := by
        simpa [BuildState.dropPending_phase, setFun_of_ne _ _ hj] using ho
      exact h.1 j o ho'
  · intro j p hp
    by_cases hj : j = i
    · subst hj
      simp only [BuildState.dropPending_phase, setFun_same] at hp
      cases hp
    · have hp' : st.phase j = .invoked p := by
        simpa [BuildState.dropPending_phase, setFun_of_ne _ _ hj] using hp
      exact h.2.1 j p hp'
  · intro j o ho
    by_cases hj : j = i
    · subst hj
      simp only [BuildState.dropPending_phase, setFun_same] at ho
      cases ho
    · have ho' : st.phase j = .linearized o := by
        simpa [BuildState.dropPending_phase, setFun_of_ne _ _ hj] using ho
      exact h.2.2 j o ho'




theorem closeLin_mem_of_closed {n : Nat} {id : OpId n} {ret : Nat}
    {l : List (LinOp n)} {a : LinOp n} (hret : a.ret ≠ none) (ha : a ∈ l) :
    a ∈ closeLin id ret l := by
  induction l with
  | nil => simp at ha
  | cons b bs ih =>
      simp only [closeLin]
      rcases List.mem_cons.mp ha with hba | ha
      · subst a
        rw [if_neg (fun h => hret h.2)]
        exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih ha)

theorem BuildScan.lin_exists {kind : Fin n → Kind} {st st' : BuildState n}
    {l : List (Move n × Fin n × StepTag UInt64)}
    (h : BuildScan kind st l st') :
    ∀ {x : LinOp n}, x ∈ st.linOps →
      ∃ x' ∈ st'.linOps, x'.lin = x.lin ∧ x'.outcome = x.outcome ∧ x'.id = x.id := by
  induction h with
  | nil => intro x hx; exact ⟨x, hx, rfl, rfl, rfl⟩
  | invoke hidle hrec ih =>
      intro x hx
      exact ih (by simpa [BuildState.openInvoke_linOps] using hx)
  | stutterStep hrec ih =>
      intro x hx
      exact ih (by simpa [BuildState.advance_linOps] using hx)
  | helpStep hhelp hrec ih =>
      intro x hx
      exact ih (by simpa [BuildState.advance_linOps] using hx)
  | pushEvent hkind hp hval hinv hrec ih =>
      intro x hx
      exact ih (by simp only [BuildState.linearize_linOps]; exact List.mem_append_left _ hx)
  | popEvent hkind hp hinv hrec ih =>
      intro x hx
      exact ih (by simp only [BuildState.linearize_linOps]; exact List.mem_append_left _ hx)
  | obsEvent hadmit hp hinv hrec ih =>
      intro x hx
      exact ih (by simp only [BuildState.linearize_linOps]; exact List.mem_append_left _ hx)
  | retLin hp hstatus hrec ih =>
      rename_i st0 i0 status0 o0 rest0 st'0
      intro x hx
      obtain ⟨x', hx1, h1, h2, hid1⟩ := BuildState.close_lin_exists (i := i0) (o := o0) hx
      obtain ⟨x'', hx'', h3, h4, hid2⟩ := ih hx1
      exact ⟨x'', hx'', h3.trans h1, h4.trans h2, hid2.trans hid1⟩
  | retPending hp hstatus hrec ih =>
      intro x hx
      exact ih (by simpa [BuildState.dropPending_linOps] using hx)
  | skipIdle hidle hrec ih =>
      intro x hx
      exact ih (by simpa [BuildState.advance_linOps] using hx)

theorem BuildScan.lin_exists_ret {kind : Fin n → Kind} {st st' : BuildState n}
    {l : List (Move n × Fin n × StepTag UInt64)}
    (h : BuildScan kind st l st') :
    ∀ {x : LinOp n}, x ∈ st.linOps → x.ret ≠ none →
      ∃ x' ∈ st'.linOps, x'.lin = x.lin ∧ x'.outcome = x.outcome ∧
        x'.id = x.id ∧ x'.ret = x.ret := by
  induction h with
  | nil => intro x hx _; exact ⟨x, hx, rfl, rfl, rfl, rfl⟩
  | invoke hidle hrec ih =>
      intro x hx hret
      exact ih (by simpa [BuildState.openInvoke_linOps] using hx) hret
  | stutterStep hrec ih =>
      intro x hx hret
      exact ih (by simpa [BuildState.advance_linOps] using hx) hret
  | helpStep hhelp hrec ih =>
      intro x hx hret
      exact ih (by simpa [BuildState.advance_linOps] using hx) hret
  | pushEvent hkind hp hval hinv hrec ih =>
      intro x hx hret
      exact ih (by simp only [BuildState.linearize_linOps]; exact List.mem_append_left _ hx) hret
  | popEvent hkind hp hinv hrec ih =>
      intro x hx hret
      exact ih (by simp only [BuildState.linearize_linOps]; exact List.mem_append_left _ hx) hret
  | obsEvent hadmit hp hinv hrec ih =>
      intro x hx hret
      exact ih (by simp only [BuildState.linearize_linOps]; exact List.mem_append_left _ hx) hret
  | retLin hp hstatus hrec ih =>
      rename_i st0 i0 status0 o0 rest0 st'0
      intro x hx hret
      have hx1 : x ∈ (st0.close i0 o0).linOps := by
        rw [BuildState.close_linOps]
        exact closeLin_mem_of_closed hret hx
      exact ih hx1 hret
  | retPending hp hstatus hrec ih =>
      intro x hx hret
      exact ih (by simpa [BuildState.dropPending_linOps] using hx) hret
  | skipIdle hidle hrec ih =>
      intro x hx hret
      exact ih (by simpa [BuildState.advance_linOps] using hx) hret

theorem BuildScan.inv {kind : Fin n → Kind} {st st' : BuildState n}
    {l : List (Move n × Fin n × StepTag UInt64)}
    (h : BuildScan kind st l st') (hm : st.LinMem) (ht : st.ThreadOK) :
    st'.LinMem ∧ st'.ThreadOK := by
  induction h with
  | nil => exact ⟨hm, ht⟩
  | invoke hidle hrec ih =>
      exact ih (BuildState.linMem_openInvoke hm) (BuildState.threadOK_openInvoke ht)
  | stutterStep hrec ih =>
      exact ih (BuildState.linMem_advance hm) (BuildState.threadOK_advance ht)
  | helpStep hhelp hrec ih =>
      exact ih (BuildState.linMem_advance hm) (BuildState.threadOK_advance ht)
  | pushEvent hkind hp hval hinv hrec ih =>
      exact ih (BuildState.linMem_linearize hm ht hp) (BuildState.threadOK_linearize ht hp)
  | popEvent hkind hp hinv hrec ih =>
      exact ih (BuildState.linMem_linearize hm ht hp) (BuildState.threadOK_linearize ht hp)
  | obsEvent hadmit hp hinv hrec ih =>
      exact ih (BuildState.linMem_linearize hm ht hp) (BuildState.threadOK_linearize ht hp)
  | retLin hp hstatus hrec ih =>
      exact ih (BuildState.linMem_close hm ht hp) (BuildState.threadOK_close ht hp)
  | retPending hp hstatus hrec ih =>
      exact ih (BuildState.linMem_dropPending hm) (BuildState.threadOK_dropPending ht)
  | skipIdle hidle hrec ih =>
      exact ih (BuildState.linMem_advance hm) (BuildState.threadOK_advance ht)

theorem buildScan_step {n C limit : Nat} {kind : Fin n → Kind}
    {g g' : GState n} {i : Fin n} {st : BuildState n} {tag : StepTag UInt64}
    (s : AbsState UInt64) (hi : Inv C limit s) (hg : GRef C limit kind s g)
    (hm : st.LinMem) (ht : st.ThreadOK)
    (halign : Align C limit kind g st)
    (hstep : GStep kind g i g')
    (hclass : StepClass (kind i) C (g.locals i) (g'.locals i) tag) :
    ∃ st', BuildScan kind st [(.step i, i, tag)] st' ∧ Align C limit kind g' st' ∧
      st'.linOps.map (fun o => o.outcome.clientEvent) =
        st.linOps.map (fun o => o.outcome.clientEvent) ++ tag.clientEvents ∧
      ∃ obs : Option (RetObs n),
        (∀ r ∈ obs.toList, r.Fits st.pos i tag) ∧
        (∀ r ∈ obs.toList, ∃ x' ∈ st'.linOps, x'.lin = r.lin ∧ x'.outcome = r.outcome ∧
          x'.id.thread = r.thread ∧ x'.ret = some r.pos) ∧
        (∀ status, tag = .ret status → ∃ r ∈ obs.toList, r.pos = st.pos ∧ r.status = status) ∧
        (∀ r ∈ obs.toList, r.loc = g.locals i) := by
  have hwf := halign.wf
  have hoth := GStep.others hstep
  have hval := GStep.value_eq hstep
  have hth := halign.thread i
  cases hph : st.phase i with
  | idle =>
    simp only [AlignThread, hph] at hth
    rcases hth with ⟨v, hv⟩ | hv
    · simp [GStep, hv] at hstep
    · simp [GStep, hv] at hstep
  | invoked p =>
    simp only [AlignThread, hph] at hth
    obtain ⟨hinput, hinvpos, hstage⟩ := hth
    rcases hclass with ⟨rfl, hst⟩ | ⟨hhelp, hst⟩ | ⟨rfl, hk, _, hst⟩ | ⟨rfl, hk, _, hst⟩ |
      ⟨rfl, hk, _, hst⟩ | ⟨rfl, hk, _, hst⟩ | ⟨hk, v, h, htag, hvv, hlink, _, hst⟩ |
      ⟨hk, h, pv, htag, hlinkH, hlinkP, _, hst⟩ | ⟨hne, htag, hst⟩
    · -- stutter
      refine ⟨st.advance, BuildScan.stutterStep (i := i) (BuildScan.nil _), ?_, ?_, ?_⟩
      refine Align.of_step halign (BuildState.wf_advance hwf) (by simp [BuildState.advance_pos]) (fun j _ => rfl) hoth ?_
      simp only [AlignThread, BuildState.advance_phase, hph]
      refine ⟨?_, ?_, ?_⟩
      · rw [hval]; exact hinput
      · simp only [BuildState.advance_pos]; omega
      · rw [hst]; exact hstage
      · simp [BuildState.advance_linOps, StepTag.clientEvents]
      · exact ⟨none, by simp [RetObs.Fits], by simp, by intro status htag; simp_all, by intro r hr; simp at hr⟩
    · -- help
      rcases hhelp with hhelp | hhelp
      · rw [hhelp]
        refine ⟨st.advance, BuildScan.helpStep (i := i) (Or.inl rfl) (BuildScan.nil _), ?_, ?_, ?_⟩
        refine Align.of_step halign (BuildState.wf_advance hwf) (by simp [BuildState.advance_pos]) (fun j _ => rfl) hoth ?_
        simp only [AlignThread, BuildState.advance_phase, hph]
        refine ⟨?_, ?_, ?_⟩
        · rw [hval]; exact hinput
        · simp only [BuildState.advance_pos]; omega
        · rw [hst]; exact hstage
        · simp [BuildState.advance_linOps, StepTag.clientEvents]
        · exact ⟨none, by simp [RetObs.Fits], by simp, by intro status htag; simp_all, by intro r hr; simp at hr⟩
      · rw [hhelp]
        refine ⟨st.advance, BuildScan.helpStep (i := i) (Or.inr rfl) (BuildScan.nil _), ?_, ?_, ?_⟩
        refine Align.of_step halign (BuildState.wf_advance hwf) (by simp [BuildState.advance_pos]) (fun j _ => rfl) hoth ?_
        simp only [AlignThread, BuildState.advance_phase, hph]
        refine ⟨?_, ?_, ?_⟩
        · rw [hval]; exact hinput
        · simp only [BuildState.advance_pos]; omega
        · rw [hst]; exact hstage
        · simp [BuildState.advance_linOps, StepTag.clientEvents]
        · exact ⟨none, by simp [RetObs.Fits], by simp, by intro status htag; simp_all, by intro r hr; simp at hr⟩
    · -- obs pushFull (push)
      refine ⟨st.linearize i p (.failure .pushFull) hinvpos,
        BuildScan.obsEvent (i := i) (k := .pushFull) (by simp [Kind.admitsFailure, hk]) hph hinvpos
          (BuildScan.nil _), ?_, ?_, ?_⟩
      refine Align.of_step halign (BuildState.wf_linearize hwf) (by simp [BuildState.linearize_pos]) ?_ hoth ?_
      · intro j hj; rw [BuildState.linearize_phase, setFun_of_ne _ _ hj]
      · simp only [AlignThread, BuildState.linearize_phase, setFun_same]
        refine ⟨?_, trivial, trivial⟩
        show threadStage C (kind i) (g'.locals i) = Stage.pushFull
        rw [hk] at hst ⊢; exact hst
      · rw [BuildState.linearize_linOps]
        simp [List.map_append, StepTag.clientEvents, OpOutcome.clientEvent, BuildState.mkLinOp, List.append_assoc]
      · exact ⟨none, by simp [RetObs.Fits], by simp, by intro status htag; simp_all, by intro r hr; simp at hr⟩
    · -- obs popEmpty (pop)
      refine ⟨st.linearize i p (.failure .popEmpty) hinvpos,
        BuildScan.obsEvent (i := i) (k := .popEmpty) (by simp [Kind.admitsFailure, hk]) hph hinvpos
          (BuildScan.nil _), ?_, ?_, ?_⟩
      refine Align.of_step halign (BuildState.wf_linearize hwf) (by simp [BuildState.linearize_pos]) ?_ hoth ?_
      · intro j hj; rw [BuildState.linearize_phase, setFun_of_ne _ _ hj]
      · simp only [AlignThread, BuildState.linearize_phase, setFun_same]
        refine ⟨?_, trivial, trivial⟩
        show threadStage C (kind i) (g'.locals i) = Stage.popEmpty
        rw [hk] at hst ⊢; exact hst
      · rw [BuildState.linearize_linOps]
        simp [List.map_append, StepTag.clientEvents, OpOutcome.clientEvent, BuildState.mkLinOp, List.append_assoc]
      · exact ⟨none, by simp [RetObs.Fits], by simp, by intro status htag; simp_all, by intro r hr; simp at hr⟩
    · -- obs pushExhausted (push)
      refine ⟨st.linearize i p (.failure .pushExhausted) hinvpos,
        BuildScan.obsEvent (i := i) (k := .pushExhausted) (by simp [Kind.admitsFailure, hk]) hph hinvpos
          (BuildScan.nil _), ?_, ?_, ?_⟩
      refine Align.of_step halign (BuildState.wf_linearize hwf) (by simp [BuildState.linearize_pos]) ?_ hoth ?_
      · intro j hj; rw [BuildState.linearize_phase, setFun_of_ne _ _ hj]
      · simp only [AlignThread, BuildState.linearize_phase, setFun_same]
        refine ⟨?_, trivial, trivial⟩
        show threadStage C (kind i) (g'.locals i) = Stage.exhausted
        rw [hk] at hst ⊢; exact hst
      · rw [BuildState.linearize_linOps]
        simp [List.map_append, StepTag.clientEvents, OpOutcome.clientEvent, BuildState.mkLinOp, List.append_assoc]
      · exact ⟨none, by simp [RetObs.Fits], by simp, by intro status htag; simp_all, by intro r hr; simp at hr⟩
    · -- obs popExhausted (pop)
      refine ⟨st.linearize i p (.failure .popExhausted) hinvpos,
        BuildScan.obsEvent (i := i) (k := .popExhausted) (by simp [Kind.admitsFailure, hk]) hph hinvpos
          (BuildScan.nil _), ?_, ?_, ?_⟩
      refine Align.of_step halign (BuildState.wf_linearize hwf) (by simp [BuildState.linearize_pos]) ?_ hoth ?_
      · intro j hj; rw [BuildState.linearize_phase, setFun_of_ne _ _ hj]
      · simp only [AlignThread, BuildState.linearize_phase, setFun_same]
        refine ⟨?_, trivial, trivial⟩
        show threadStage C (kind i) (g'.locals i) = Stage.exhausted
        rw [hk] at hst ⊢; exact hst
      · rw [BuildState.linearize_linOps]
        simp [List.map_append, StepTag.clientEvents, OpOutcome.clientEvent, BuildState.mkLinOp, List.append_assoc]
      · exact ⟨none, by simp [RetObs.Fits], by simp, by intro status htag; simp_all, by intro r hr; simp at hr⟩
    · -- push event
      rw [htag]
      refine ⟨st.linearize i p (.success (.push v) (.pushed h)) hinvpos,
        BuildScan.pushEvent (i := i) (v := v) (r := .pushed h) (p := p) hk hph
          (hinput.trans hvv.symm) hinvpos (BuildScan.nil _), ?_, ?_, ?_⟩
      refine Align.of_step halign (BuildState.wf_linearize hwf) (by simp [BuildState.linearize_pos]) ?_ hoth ?_
      · intro j hj; rw [BuildState.linearize_phase, setFun_of_ne _ _ hj]
      · simp only [AlignThread, BuildState.linearize_phase, setFun_same]
        refine ⟨?_, hk, hlink⟩
        show threadStage C (kind i) (g'.locals i) = Stage.success
        rw [hk] at hst ⊢; exact hst
      · rw [BuildState.linearize_linOps]
        simp [List.map_append, StepTag.clientEvents, OpOutcome.clientEvent, BuildState.mkLinOp, List.append_assoc]
      · exact ⟨none, by simp [RetObs.Fits], by simp, by intro status htag; simp_all, by intro r hr; simp at hr⟩
    · -- pop event
      rw [htag]
      refine ⟨st.linearize i p (.success .pop (.popped h pv)) hinvpos,
        BuildScan.popEvent (i := i) (r := .popped h pv) (p := p) hk hph hinvpos (BuildScan.nil _), ?_, ?_, ?_⟩
      refine Align.of_step halign (BuildState.wf_linearize hwf) (by simp [BuildState.linearize_pos]) ?_ hoth ?_
      · intro j hj; rw [BuildState.linearize_phase, setFun_of_ne _ _ hj]
      · simp only [AlignThread, BuildState.linearize_phase, setFun_same]
        refine ⟨?_, hk, hlinkH, hlinkP⟩
        show threadStage C (kind i) (g'.locals i) = Stage.success
        rw [hk] at hst ⊢; exact hst
      · rw [BuildState.linearize_linOps]
        simp [List.map_append, StepTag.clientEvents, OpOutcome.clientEvent, BuildState.mkLinOp, List.append_assoc]
      · exact ⟨none, by simp [RetObs.Fits], by simp, by intro status htag; simp_all, by intro r hr; simp at hr⟩
    · -- ret: impossible from a pre stage
      exact absurd hstage hne
  | linearized o =>
    simp only [AlignThread, hph] at hth
    obtain ⟨hstageO, hkindO, hregsO⟩ := hth
    have hclass0 := hclass
    rcases hclass with ⟨rfl, hst⟩ | ⟨hhelp, hst⟩ | ⟨rfl, hk, hpre, _⟩ | ⟨rfl, hk, hpre, _⟩ |
      ⟨rfl, hk, hpre, _⟩ | ⟨rfl, hk, hpre, _⟩ | ⟨hk, v, h, htag, _, _, hpre, _⟩ |
      ⟨hk, h, pv, htag, _, _, hpre, _⟩ | ⟨hne, htag, hst⟩
    · -- stutter
      refine ⟨st.advance, BuildScan.stutterStep (i := i) (BuildScan.nil _), ?_, ?_, ?_⟩
      refine Align.of_step halign (BuildState.wf_advance hwf) (by simp [BuildState.advance_pos]) (fun j _ => rfl) hoth ?_
      simp only [AlignThread, BuildState.advance_phase, hph]
      exact ⟨by rw [hst]; exact hstageO, hkindO, OutcomeRegs.step (k := 0) hg hstep hkindO hstageO hregsO⟩
      · simp [BuildState.advance_linOps, StepTag.clientEvents]
      · exact ⟨none, by simp [RetObs.Fits], by simp, by intro status htag; simp_all, by intro r hr; simp at hr⟩
    · -- help
      rcases hhelp with hhelp | hhelp
      · rw [hhelp]
        refine ⟨st.advance, BuildScan.helpStep (i := i) (Or.inl rfl) (BuildScan.nil _), ?_, ?_, ?_⟩
        refine Align.of_step halign (BuildState.wf_advance hwf) (by simp [BuildState.advance_pos]) (fun j _ => rfl) hoth ?_
        simp only [AlignThread, BuildState.advance_phase, hph]
        exact ⟨by rw [hst]; exact hstageO, hkindO, OutcomeRegs.step (k := 0) hg hstep hkindO hstageO hregsO⟩
        · simp [BuildState.advance_linOps, StepTag.clientEvents]
        · exact ⟨none, by simp [RetObs.Fits], by simp, by intro status htag; simp_all, by intro r hr; simp at hr⟩
      · rw [hhelp]
        refine ⟨st.advance, BuildScan.helpStep (i := i) (Or.inr rfl) (BuildScan.nil _), ?_, ?_, ?_⟩
        refine Align.of_step halign (BuildState.wf_advance hwf) (by simp [BuildState.advance_pos]) (fun j _ => rfl) hoth ?_
        simp only [AlignThread, BuildState.advance_phase, hph]
        exact ⟨by rw [hst]; exact hstageO, hkindO, OutcomeRegs.step (k := 0) hg hstep hkindO hstageO hregsO⟩
        · simp [BuildState.advance_linOps, StepTag.clientEvents]
        · exact ⟨none, by simp [RetObs.Fits], by simp, by intro status htag; simp_all, by intro r hr; simp at hr⟩
    · exfalso; rw [hstageO] at hpre; exact stageOfOutcome_ne_pre o.outcome hpre
    · exfalso; rw [hstageO] at hpre; exact stageOfOutcome_ne_pre o.outcome hpre
    · exfalso; rw [hstageO] at hpre; exact stageOfOutcome_ne_pre o.outcome hpre
    · exfalso; rw [hstageO] at hpre; exact stageOfOutcome_ne_pre o.outcome hpre
    · exfalso; rw [hstageO] at hpre; exact stageOfOutcome_ne_pre o.outcome hpre
    · exfalso; rw [hstageO] at hpre; exact stageOfOutcome_ne_pre o.outcome hpre
    · -- ret
      rw [htag]
      refine ⟨st.close i o, BuildScan.retLin (i := i) (o := o)
        (status := (threadStage C (kind i) (g.locals i)).status) hph ?_ (BuildScan.nil _), ?_, ?_, ?_⟩
      · rw [hstageO]; exact stageOfOutcome_accepts o.outcome
      · refine Align.of_step halign (BuildState.wf_close hwf) (by simp [BuildState.close_pos]) ?_ hoth ?_
        · intro j hj; rw [BuildState.close_phase, setFun_of_ne _ _ hj]
        · simp only [AlignThread, BuildState.close_phase, setFun_same]
          obtain ⟨v, hv, _⟩ := hst
          exact Or.inl ⟨v, hv⟩
      · rw [BuildState.close_linOps]
        simp [closeLin_outcomes, StepTag.clientEvents]
      · let robs : RetObs n := {
          pos := st.pos
          lin := o.lin
          thread := i
          status := (threadStage C (kind i) (g.locals i)).status
          outcome := o.outcome
          loc := g.locals i }
        refine ⟨some robs, ?_, ?_, ?_, ?_⟩
        · intro r hr
          simp only [Option.toList_some, List.mem_singleton] at hr
          rw [hr]
          have hsnd := RetObs.sound halign hph (by simpa [htag] using hclass0)
          refine ⟨rfl, rfl, hsnd.1, hsnd.2, ?_, by simp [htag, robs]⟩
          simp only [robs]
          rw [hstageO]
        · intro r hr
          simp only [Option.toList_some, List.mem_singleton] at hr
          rw [hr]
          have horet : o.ret = none := ht.2.2 i o hph
          obtain ⟨x', hx', h1, h2, h3, h4⟩ :=
            BuildState.close_lin_exists_id (i := i) (o := o) rfl horet (hm i o hph)
          refine ⟨x', hx', h1, h2, ?_, h4⟩
          rw [h3]
          exact ht.1 i o hph
        · intro status hstatus
          refine ⟨robs, by simp, rfl, ?_⟩
          simp only [StepTag.ret.injEq] at hstatus
          subst hstatus
          simp only [robs]
        · intro r hr
          simp only [Option.toList_some, List.mem_singleton] at hr
          rw [hr]





theorem finalize_clientEvents {n : Nat} (endPos : Nat) (l : List (LinOp n))
    (h : ∀ o ∈ l, o.Sound endPos) :
    (finalize endPos l h).map TimedObsOp.clientEvent =
      l.map (fun o => o.outcome.clientEvent) := by
  simp only [finalize, List.map_map, Function.comp_def]
  have hmap : l.attach.map
        (fun x : {o // o ∈ l} => TimedObsOp.clientEvent (x.1.toTimed endPos (h x.1 x.2))) =
      l.attach.map (fun x : {o // o ∈ l} => x.1.outcome.clientEvent) := by
    apply List.map_congr_left
    intro x _
    rfl
  rw [hmap]
  simpa using (List.attach_map_val (l := l) (f := fun o : LinOp n => o.outcome.clientEvent))

theorem pairwise_attach {α : Type} {r : α → α → Prop} {l : List α}
    (h : List.Pairwise r l) :
    List.Pairwise (fun x y : {o // o ∈ l} => r x.1 y.1) l.attach := by
  have hp := h.pmap (p := fun x => x ∈ l) (f := fun x hx => (⟨x, hx⟩ : {o // o ∈ l}))
    (fun x hx => hx) (S := fun x y => r x.1 y.1) (fun x _ y _ hxy => hxy)
  simpa [List.attach, List.attachWith] using hp

theorem finalize_sorted {n : Nat} {endPos : Nat} {l : List (LinOp n)}
    (h : l.Pairwise (fun a b => a.lin < b.lin))
    (hs : ∀ o ∈ l, o.Sound endPos) :
    (finalize endPos l hs).Pairwise (fun a b => a.lin < b.lin) := by
  simp only [finalize]
  apply List.Pairwise.map (f := fun x : {o // o ∈ l} => x.1.toTimed endPos (hs x.1 x.2))
  · intro x y hxy; exact hxy
  · exact pairwise_attach h

def mkHistory {n : Nat} (st : BuildState n) (hwf : st.WF) : ObsHistory n where
  ops := finalize st.pos st.linOps hwf.linSound
  lin_sorted := finalize_sorted hwf.sorted hwf.linSound

theorem buildScan_invoke {n C limit : Nat} {kind : Fin n → Kind}
    {g g' : GState n} {i : Fin n} {v : UInt64} {st : BuildState n}
    (halign : Align C limit kind g st) (hinv : GInvoke g i v g') :
    ∃ st', BuildScan kind st [(.invoke i v, i, .stutter)] st' ∧ Align C limit kind g' st' ∧
      st'.linOps = st.linOps := by
  obtain ⟨r, hr, hg'eq⟩ := hinv
  have hth := halign.thread i
  have hidle : st.phase i = .idle := by
    cases hp : st.phase i with
    | idle => rfl
    | invoked p =>
        simp only [AlignThread, hp] at hth
        obtain ⟨_, _, hstage⟩ := hth
        exfalso
        have hdone : threadStage C (kind i) (g.locals i) = .done := by
          cases hk : kind i <;> simp [threadStage, pushStage, popStage, hr]
        rw [hdone] at hstage
        exact absurd hstage (by decide)
    | linearized o =>
        simp only [AlignThread, hp] at hth
        exfalso
        have hdone : threadStage C (kind i) (g.locals i) = .done := by
          cases hk : kind i <;> simp [threadStage, pushStage, popStage, hr]
        rw [hdone] at hth
        cases ho : o.outcome with
        | success a r =>
            rw [ho] at hth
            cases a <;> simpa [stageOfOutcome] using hth
        | failure k =>
            rw [ho] at hth
            cases k <;> simpa [stageOfOutcome] using hth
  let gx : GState n := { g with locals := updLocal g.locals i (invokeLocal (g.locals i) v) }
  have hg'x : g' = gx := hg'eq
  subst hg'x
  refine ⟨st.openInvoke i v, BuildScan.invoke (st := st) (i := i) (v := v) hidle (BuildScan.nil _), ?_, ?_⟩
  refine Align.of_step (i := i) halign (BuildState.wf_openInvoke hidle halign.wf) ?_ ?_ ?_ ?_
  · simp [BuildState.openInvoke_pos]
  · intro j hj; simp [BuildState.openInvoke_phase, setFun_of_ne _ _ hj]
  · intro j hj; simp [gx, updLocal, hj]
  · simp only [AlignThread, BuildState.openInvoke_phase, setFun_same]
    refine ⟨?_, ?_, ?_⟩
    · simp [gx, updLocal, invokeLocal, freshLocal]
    · simp [BuildState.openInvoke_pos]
    · cases hk : kind i <;>
        simp [gx, updLocal, invokeLocal, freshLocal, threadStage, pushStage, popStage]
  · simp [BuildState.openInvoke_linOps]

theorem GPath.buildScanExec {n C limit k : Nat} {kind : Fin n → Kind} {g g' : GState n}
    (hp : GPath kind g g')
    (s : AbsState UInt64) (hi : Inv C limit s) (hg : GRef C limit kind s g)
    (hC : 0 < C) (hpow : C = 2 ^ k) (hCmax : C ≤ 2 ^ 24)
    (hbound : limit < 2 ^ 63) (hlimitC : limit + C ≤ 2 ^ 63)
    {st : BuildState n} (hm : st.LinMem) (ht : st.ThreadOK)
    (halign : Align C limit kind g st) :
    ∃ s' ms tags st' rets,
      Exec kind C limit hC s g ms s' g' tags ∧
      BuildScan kind st (ms.zip tags) st' ∧
      Align C limit kind g' st' ∧
      st'.linOps.map (fun o => o.outcome.clientEvent) =
        st.linOps.map (fun o => o.outcome.clientEvent) ++
          tags.flatMap (fun p => p.2.clientEvents) ∧
      (∀ r : RetObs n, r ∈ (rets : List (RetObs n)) → RetObs.OK r st.pos ms.length tags) ∧
      (∀ r : RetObs n, r ∈ (rets : List (RetObs n)) →
        ∃ x' ∈ st'.linOps, x'.lin = r.lin ∧ x'.outcome = r.outcome ∧
          x'.id.thread = r.thread ∧ x'.ret = some r.pos) ∧
      (∀ (k : Nat) (j : Fin n) (status : UInt64), k < ms.length →
        tags[k]? = some (j, .ret status) → ∃ r ∈ rets, r.pos = st.pos + k ∧ r.status = status) := by
  induction hp generalizing s st with
  | refl g =>
      exact ⟨s, [], [], st, [], Exec.nil, BuildScan.nil st, halign, by simp,
        by intro r hr; simp at hr, by intro r hr; simp at hr,
        by intro k j status hk; simp at hk⟩
  | step i hstep hs ih =>
      obtain ⟨s1, tag, hg1, hi1, heff, hclass⟩ :=
        gstep_tag hi hg hC hpow hCmax hbound hlimitC hstep
      obtain ⟨st1, hscan1, halign1, hevents1, obs, hobs, hprov1, hcover1, hloc1⟩ :=
        buildScan_step s hi hg hm ht halign hstep hclass
      obtain ⟨hm1, ht1⟩ := BuildScan.inv hscan1 hm ht
      obtain ⟨s2, ms, tags, st2, rets, hexec, hscan2, halign2, hevents2, hrets, hprov2, hcover2⟩ :=
        ih s1 hi1 hg1 hm1 ht1 halign1
      have hpos1 : st1.pos = st.pos + 1 := by
        have hp1 := BuildScan.pos_eq hscan1
        simpa using hp1
      refine ⟨s2, Move.step i :: ms, (i, tag) :: tags, st2, obs.toList ++ rets,
        Exec.step hstep heff hexec, ?_, halign2, ?_, ?_, ?_, ?_⟩
      · simpa [List.zip_cons_cons] using BuildScan.append hscan1 hscan2
      · calc st2.linOps.map (fun o => o.outcome.clientEvent)
            = st1.linOps.map (fun o => o.outcome.clientEvent) ++ tags.flatMap (fun p => p.2.clientEvents) := hevents2
          _ = (st.linOps.map (fun o => o.outcome.clientEvent) ++ tag.clientEvents) ++
                tags.flatMap (fun p => p.2.clientEvents) := by rw [hevents1]
          _ = st.linOps.map (fun o => o.outcome.clientEvent) ++
                ((i, tag) :: tags).flatMap (fun p => p.2.clientEvents) := by
                simp [List.flatMap_cons, List.append_assoc]
      · intro r hr
        rcases List.mem_append.mp hr with h | h
        · exact RetObs.fits_ok (hobs r h)
        · have hk := hrets r h
          rw [hpos1] at hk
          exact RetObs.ok_shift hk
      · intro r hr
        rcases List.mem_append.mp hr with h | h
        · obtain ⟨x', hx', hlin, hout, hth, hret⟩ := hprov1 r h
          obtain ⟨x'', hx'', hlin2, hout2, hid2, hret2⟩ :=
            BuildScan.lin_exists_ret hscan2 hx' (by rw [hret]; simp)
          exact ⟨x'', hx'', hlin2.trans hlin, hout2.trans hout,
            by rw [hid2]; exact hth, hret2.trans hret⟩
        · exact hprov2 r h
      · intro k j status hk hget
        cases k with
        | zero =>
            simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hget
            obtain ⟨rfl, rfl⟩ := hget
            obtain ⟨r, hr, hpos, hstat⟩ := hcover1 status rfl
            exact ⟨r, List.mem_append_left _ hr, by simpa using hpos, hstat⟩
        | succ k =>
            simp only [List.getElem?_cons_succ] at hget
            have hk' : k < ms.length := by simpa using hk
            obtain ⟨r, hr, hpos, hstat⟩ := hcover2 k j status hk' hget
            exact ⟨r, List.mem_append_right _ hr, by rw [hpos]; omega, hstat⟩
  | invoke i v hinv hs ih =>
      obtain ⟨st1, hscan1, halign1, hlin1⟩ := buildScan_invoke halign hinv
      obtain ⟨hm1, ht1⟩ := BuildScan.inv hscan1 hm ht
      obtain ⟨s2, ms, tags, st2, rets, hexec, hscan2, halign2, hevents2, hrets, hprov2, hcover2⟩ :=
        ih s hi (GInvoke.gref hg hinv) hm1 ht1 halign1
      have hpos1 : st1.pos = st.pos + 1 := by
        have hp1 := BuildScan.pos_eq hscan1
        simpa using hp1
      have hevents1 : st1.linOps.map (fun o => o.outcome.clientEvent) =
          st.linOps.map (fun o => o.outcome.clientEvent) := by
        rw [hlin1]
      refine ⟨s2, Move.invoke i v :: ms, (i, .stutter) :: tags, st2, rets,
        Exec.invoke hinv (GInvoke.gref hg hinv) (GInvoke.shared_eq hinv)
          (SharedRef.ref hg.hshared) hexec, ?_, halign2, ?_, ?_, ?_, ?_⟩
      · simpa [List.zip_cons_cons] using BuildScan.append hscan1 hscan2
      · calc st2.linOps.map (fun o => o.outcome.clientEvent)
            = st1.linOps.map (fun o => o.outcome.clientEvent) ++ tags.flatMap (fun p => p.2.clientEvents) := hevents2
          _ = st.linOps.map (fun o => o.outcome.clientEvent) ++
                tags.flatMap (fun p => p.2.clientEvents) := by rw [hevents1]
          _ = st.linOps.map (fun o => o.outcome.clientEvent) ++
                ((i, StepTag.stutter) :: tags).flatMap (fun p => p.2.clientEvents) := by
                simp [StepTag.clientEvents, List.append_assoc]
      · intro r hr
        have hk := hrets r hr
        rw [hpos1] at hk
        exact RetObs.ok_shift hk
      · exact hprov2
      · intro k j status hk hget
        cases k with
        | zero => simp at hget
        | succ k =>
            simp only [List.getElem?_cons_succ] at hget
            have hk' : k < ms.length := by simpa using hk
            obtain ⟨r, hr, hpos, hstat⟩ := hcover2 k j status hk' hget
            exact ⟨r, hr, by rw [hpos]; omega, hstat⟩

/-- A record left in `linOps` survives finalization with the same
linearization point and outcome. -/
theorem exists_finalize_of_mem {n : Nat} {endPos : Nat} {l : List (LinOp n)}
    {h : ∀ o ∈ l, o.Sound endPos} {x : LinOp n} (hx : x ∈ l) :
    ∃ op ∈ finalize endPos l h, op.lin = x.lin ∧ op.outcome = x.outcome ∧
      op.id = x.id ∧ op.ret = x.ret.getD endPos := by
  refine ⟨x.toTimed endPos (h x hx), ?_, rfl, rfl, rfl, rfl⟩
  simp only [finalize]
  exact List.mem_map_of_mem
    (f := fun y : {o // o ∈ l} => y.1.toTimed endPos (h y.1 y.2))
    (List.mem_attach l ⟨x, hx⟩)

theorem GPath.buildHistory {n C limit k : Nat} {kind : Fin n → Kind} {g g' : GState n}
    (hp : GPath kind g g')
    (s : AbsState UInt64) (hi : Inv C limit s) (hg : GRef C limit kind s g)
    (hC : 0 < C) (hpow : C = 2 ^ k) (hCmax : C ≤ 2 ^ 24)
    (hbound : limit < 2 ^ 63) (hlimitC : limit + C ≤ 2 ^ 63)
    (hinit : ∀ i, ∃ v, (g.locals i).phase = Phase.returned v) :
    ∃ s' ms tags hist rets,
      Exec kind C limit hC s g ms s' g' tags ∧
      BuildHistory kind ms tags hist ∧
      hist.clientEvents = tags.flatMap (fun p => p.2.clientEvents) ∧
      hist.Linearizes C limit (sync s) (sync s') ∧
      RespectsRealTime hist ∧
      (∀ r : RetObs n, r ∈ (rets : List (RetObs n)) →
        r.pos < ms.length ∧ tags[r.pos]? = some (r.thread, .ret r.status) ∧
        (∀ v h, r.outcome = .success (.push v) (.pushed h) → r.loc.out0 = UInt64.ofNat h) ∧
        (∀ h p, r.outcome = .success .pop (.popped h p) → r.loc.out0 = p ∧ r.loc.out1 = UInt64.ofNat h) ∧
        r.status = (stageOfOutcome r.outcome).status) ∧
      (∀ r : RetObs n, r ∈ (rets : List (RetObs n)) →
        ∃ op ∈ hist.ops, op.id.thread = r.thread ∧ op.lin = r.lin ∧
          op.outcome = r.outcome ∧ op.ret = r.pos) ∧
      (∀ (k : Nat) (j : Fin n) (status : UInt64), k < ms.length →
        tags[k]? = some (j, .ret status) → ∃ r ∈ rets, r.pos = k ∧ r.status = status) := by
  have hinitAlign : Align C limit kind g (BuildState.init n) := by
    refine ⟨BuildState.init_wf n, ?_⟩
    intro i
    simp only [AlignThread, BuildState.init]
    exact Or.inl (hinit i)
  obtain ⟨s', ms, tags, st', rets, hexec, hscan, halign', hevents, hrets, hprov, hcover⟩ :=
    hp.buildScanExec s hi hg hC hpow hCmax hbound hlimitC
      (BuildState.linMem_init (n := n)) (BuildState.threadOK_init (n := n)) hinitAlign
  let hist : ObsHistory n := mkHistory st' halign'.wf
  have hbuild : BuildHistory kind ms tags hist := ⟨st', hscan, halign'.wf, rfl⟩
  have hclient : hist.clientEvents = tags.flatMap (fun p => p.2.clientEvents) := by
    simp only [hist, mkHistory, ObsHistory.clientEvents]
    rw [finalize_clientEvents]
    simpa [BuildState.init] using hevents
  have htrace : ClientTrace C limit (sync s) (tags.flatMap (fun p => p.2.clientEvents)) (sync s') :=
    Exec.clientEvents_trace hexec
  refine ⟨s', ms, tags, hist, rets, hexec, hbuild, hclient, ?_, ObsHistory.real_time hist, ?_, ?_, ?_⟩
  · rw [ObsHistory.Linearizes]
    exact BuildHistory.linearizes_of_clientEvents hbuild ⟨rfl, rfl⟩ htrace hclient
  · intro r hr
    have hk := hrets r hr
    simp only [RetObs.OK, BuildState.init] at hk
    obtain ⟨-, hlt, hget, hs1, hs2, hstat⟩ := hk
    exact ⟨by simpa using hlt, by simpa using hget, hs1, hs2, hstat⟩
  · intro r hr
    obtain ⟨x', hx', hlin, hout, hth, hret⟩ := hprov r hr
    obtain ⟨op, hop, hlin2, hout2, hid2, hret2⟩ :=
      exists_finalize_of_mem (h := halign'.wf.linSound) hx'
    refine ⟨op, hop, by rw [hid2]; exact hth, hlin2.trans hlin, hout2.trans hout, ?_⟩
    rw [hret2, hret]
    rfl
  · intro k j status hk hget
    obtain ⟨r, hr, hpos, hstat⟩ := hcover k j status hk hget
    exact ⟨r, hr, by simpa [BuildState.init] using hpos, hstat⟩

theorem initial_linearizable {n C limit k : Nat} {kind : Fin n → Kind}
    {vals : Fin n → UInt64} {g' : GState n}
    (hp : GPath kind (initialGState C limit vals) g')
    (hC : 0 < C) (hpow : C = 2 ^ k) (hCmax : C ≤ 2 ^ 24)
    (hbound : limit < 2 ^ 63) (hlimitC : limit + C ≤ 2 ^ 63) :
    ∃ s' ms tags hist rets,
      Exec kind C limit hC (initial UInt64) (initialGState C limit vals) ms s' g' tags ∧
      BuildHistory kind ms tags hist ∧
      hist.clientEvents = tags.flatMap (fun p => p.2.clientEvents) ∧
      hist.Linearizes C limit (sync (initial UInt64)) (sync s') ∧
      RespectsRealTime hist ∧
      (∀ r : RetObs n, r ∈ (rets : List (RetObs n)) →
        r.pos < ms.length ∧ tags[r.pos]? = some (r.thread, .ret r.status) ∧
        (∀ v h, r.outcome = .success (.push v) (.pushed h) → r.loc.out0 = UInt64.ofNat h) ∧
        (∀ h p, r.outcome = .success .pop (.popped h p) → r.loc.out0 = p ∧ r.loc.out1 = UInt64.ofNat h) ∧
        r.status = (stageOfOutcome r.outcome).status) ∧
      (∀ r : RetObs n, r ∈ (rets : List (RetObs n)) →
        ∃ op ∈ hist.ops, op.id.thread = r.thread ∧ op.lin = r.lin ∧
          op.outcome = r.outcome ∧ op.ret = r.pos) ∧
      (∀ (k : Nat) (j : Fin n) (status : UInt64), k < ms.length →
        tags[k]? = some (j, .ret status) → ∃ r ∈ rets, r.pos = k ∧ r.status = status) := by
  apply GPath.buildHistory hp (initial UInt64) (initial_inv C limit)
    (initialGRef kind vals hC hCmax hbound) hC hpow hCmax hbound hlimitC
  intro i
  simp [initialGState, startLocal]



/-- The exact return code of a linearized operation: a `.ret status` step of
a thread whose stage is the outcome's stage returns exactly the canonical
status (`0` success, `1` pushFull, `2` popEmpty, `3` exhausted). -/
theorem StepClass.ret_status {n : Nat} {kind : Kind} {C : Nat} {loc loc' : Local}
    {o : LinOp n} {status : UInt64}
    (h : StepClass kind C loc loc' (.ret status))
    (hstage : threadStage C kind loc = stageOfOutcome o.outcome) :
    status = (stageOfOutcome o.outcome).status := by
  rcases h with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _, _, _⟩ | ⟨h, _, _, _⟩ | ⟨h, _, _, _⟩ |
    ⟨h, _, _, _⟩ | ⟨_, _, _, h, _, _, _, _⟩ | ⟨_, _, _, h, _, _, _, _⟩ | ⟨_, h, _⟩
  · cases h
  · rcases h with h | h <;> cases h
  · cases h
  · cases h
  · cases h
  · cases h
  · cases h
  · cases h
  · injection h with h
    rw [hstage] at h
    exact h

/-- At a return step of a thread whose scan record is already linearized,
the kernel status is exactly the outcome's canonical status. -/
theorem buildScan_step_ret_status {n C limit : Nat} {kind : Fin n → Kind}
    {g g' : GState n} {i : Fin n} {st : BuildState n} {status : UInt64}
    (halign : Align C limit kind g st)
    (hclass : StepClass (kind i) C (g.locals i) (g'.locals i) (.ret status))
    {o : LinOp n} (hph : st.phase i = .linearized o) :
    status = (stageOfOutcome o.outcome).status := by
  have hth := halign.thread i
  simp only [AlignThread, hph] at hth
  obtain ⟨hstageO, _, _⟩ := hth
  exact StepClass.ret_status hclass hstageO

/-- A run history has no more operations than schedule moves, and every
linearization point is a real position of the schedule. -/
theorem BuildHistory.positions {n : Nat} {kind : Fin n → Kind} {ms : List (Move n)}
    {tags : List (Fin n × StepTag UInt64)} {h : ObsHistory n}
    (hb : BuildHistory kind ms tags h) :
    h.ops.length ≤ ms.length ∧
      ∀ op ∈ h.ops, op.inv ≤ op.lin ∧ op.lin ≤ op.ret ∧ op.lin < ms.length := by
  refine ⟨BuildHistory.length_le hb, ?_⟩
  intro op hop
  exact ⟨op.inv_le_lin, op.lin_le_ret, BuildHistory.lin_lt_length hb hop⟩



/-- At the return phase of a successful push, the kernel's output register
holds exactly the publication position carried by the stage invariant. -/
theorem push_ret_outputs {C limit : Nat} {s : AbsState UInt64} {sh : Shared} {loc : Local}
    (hinv : PushInv C limit s sh loc (.running 4 3)) :
    ∃ h : Nat, loc.regs rHint = UInt64.ofNat h ∧ loc.out0 = UInt64.ofNat h := by
  cases hinv with
  | hintPath3 h _ hintEq outEq => exact ⟨h, hintEq, by rw [outEq, hintEq]⟩

/-- At the return phase of a successful pop, the kernel's output registers
hold exactly the popped value and its position. -/
theorem pop_ret_outputs {C limit : Nat} {s : AbsState UInt64} {sh : Shared} {loc : Local}
    (hinv : PopInv C limit s sh loc (.running 4 4)) :
    ∃ (h : Nat) (p : UInt64), loc.regs rHint = UInt64.ofNat h ∧
      loc.regs rPayload = p ∧ loc.out0 = p ∧ loc.out1 = UInt64.ofNat h := by
  cases hinv with
  | out4 h _ hintEq out0Eq out1Eq =>
      exact ⟨h, _, hintEq, rfl, by rw [out0Eq], by rw [out1Eq, hintEq]⟩





/-- A finite global run with its explicit move list. -/
inductive GPathTrace {n : Nat} (kind : Fin n → Kind) :
    GState n → List (Move n) → GState n → Prop
  | refl (g : GState n) : GPathTrace kind g [] g
  | step {g g' g'' : GState n} {i : Fin n} {ms : List (Move n)}
      (h : GStep kind g i g') (hs : GPathTrace kind g' ms g'') :
      GPathTrace kind g (Move.step i :: ms) g''
  | invoke {g g' g'' : GState n} {i : Fin n} {v : UInt64} {ms : List (Move n)}
      (h : GInvoke g i v g') (hs : GPathTrace kind g' ms g'') :
      GPathTrace kind g (Move.invoke i v :: ms) g''


namespace GPathTrace

/-- The global state at local index `k` of the trace (the state before the
move at that index). -/
inductive StateAt {n : Nat} {kind : Fin n → Kind} :
    {g : GState n} → {ms : List (Move n)} → {g' : GState n} →
    GPathTrace kind g ms g' → Nat → GState n → Prop
  | zero {g g' : GState n} {ms : List (Move n)} (h : GPathTrace kind g ms g') :
      StateAt h 0 g
  | step {g g' g'' : GState n} {i : Fin n} {ms : List (Move n)}
      {h : GStep kind g i g'} {hs : GPathTrace kind g' ms g''} {k : Nat} {gk : GState n}
      (hk : StateAt hs k gk) : StateAt (GPathTrace.step h hs) (k + 1) gk
  | invoke {g g' g'' : GState n} {i : Fin n} {v : UInt64} {ms : List (Move n)}
      {h : GInvoke g i v g'} {hs : GPathTrace kind g' ms g''} {k : Nat} {gk : GState n}
      (hk : StateAt hs k gk) : StateAt (GPathTrace.invoke h hs) (k + 1) gk

/-- The tags of a trace are its canonical per-step tags: every `GStep` is
classified by a `StepClass` for the same local states, and every invocation is
recorded as a stutter.  This closes the interface between the `Exec` tags and
the actual trace steps. -/
inductive TagsFor {n : Nat} (C : Nat) {kind : Fin n → Kind} :
    {g : GState n} → {ms : List (Move n)} → {g' : GState n} →
    GPathTrace kind g ms g' → List (Fin n × StepTag UInt64) → Prop
  | nil (g : GState n) : TagsFor C (GPathTrace.refl g) []
  | step {g g' g'' : GState n} {i : Fin n} {ms : List (Move n)}
      {h : GStep kind g i g'} {hs : GPathTrace kind g' ms g''}
      {tag : StepTag UInt64} (hclass : StepClass (kind i) C (g.locals i) (g'.locals i) tag)
      (htags : TagsFor C hs tags) :
      TagsFor C (GPathTrace.step h hs) ((i, tag) :: tags)
  | invoke {g g' g'' : GState n} {i : Fin n} {v : UInt64} {ms : List (Move n)}
      {h : GInvoke g i v g'} {hs : GPathTrace kind g' ms g''}
      (htags : TagsFor C hs tags) :
      TagsFor C (GPathTrace.invoke h hs) ((i, .stutter) :: tags)

/-- The start state of a trace (definitionally its first index). -/
def start {n : Nat} {kind : Fin n → Kind} {g g' : GState n} {ms : List (Move n)}
    (_h : GPathTrace kind g ms g') : GState n := g

/-- The trace is a `GPath` once the moves are forgotten. -/
theorem toGPath {kind : Fin n → Kind} {g g' : GState n} {ms : List (Move n)}
    (h : GPathTrace kind g ms g') : GPath kind g g' := by
  induction h with
  | refl g => exact GPath.refl g
  | step h hs ih => exact GPath.step _ h ih
  | invoke h hs ih => exact GPath.invoke _ _ h ih

end GPathTrace



theorem GPathTrace.buildScanExec {n C limit k : Nat} {kind : Fin n → Kind} {g g' : GState n}
    {ms : List (Move n)}
    (hp : GPathTrace kind g ms g')
    (s : AbsState UInt64) (hi : Inv C limit s) (hg : GRef C limit kind s g)
    (hC : 0 < C) (hpow : C = 2 ^ k) (hCmax : C ≤ 2 ^ 24)
    (hbound : limit < 2 ^ 63) (hlimitC : limit + C ≤ 2 ^ 63)
    {st : BuildState n} (hm : st.LinMem) (ht : st.ThreadOK)
    (halign : Align C limit kind g st) :
    ∃ s' tags st' rets,
      Exec kind C limit hC s g ms s' g' tags ∧
      BuildScan kind st (ms.zip tags) st' ∧
      Align C limit kind g' st' ∧
      st'.linOps.map (fun o => o.outcome.clientEvent) =
        st.linOps.map (fun o => o.outcome.clientEvent) ++
          tags.flatMap (fun p => p.2.clientEvents) ∧
      (∀ r : RetObs n, r ∈ (rets : List (RetObs n)) → RetObs.OK r st.pos ms.length tags) ∧
      (∀ r : RetObs n, r ∈ (rets : List (RetObs n)) →
        ∃ x' ∈ st'.linOps, x'.lin = r.lin ∧ x'.outcome = r.outcome ∧
          x'.id.thread = r.thread ∧ x'.ret = some r.pos) ∧
      (∀ (k : Nat) (j : Fin n) (status : UInt64), k < ms.length →
        tags[k]? = some (j, .ret status) → ∃ r ∈ rets, r.pos = st.pos + k ∧ r.status = status) ∧
      (∀ r : RetObs n, r ∈ (rets : List (RetObs n)) →
        ∃ gk, GPathTrace.StateAt hp (r.pos - st.pos) gk ∧ r.loc = gk.locals r.thread) ∧
      GPathTrace.TagsFor C hp tags := by
  induction hp generalizing s st with
  | refl g =>
      exact ⟨s, [], st, [], Exec.nil, BuildScan.nil st, halign, by simp,
        by intro r hr; simp at hr, by intro r hr; simp at hr,
        by intro k j status hk; simp at hk, by intro r hr; simp at hr,
        GPathTrace.TagsFor.nil g⟩
  | step hstep hs ih =>
      rename_i g0 g1 i0 ms0
      obtain ⟨s1, tag, hg1, hi1, heff, hclass⟩ :=
        gstep_tag hi hg hC hpow hCmax hbound hlimitC hstep
      obtain ⟨st1, hscan1, halign1, hevents1, obs, hobs, hprov1, hcover1, hloc1⟩ :=
        buildScan_step s hi hg hm ht halign hstep hclass
      obtain ⟨hm1, ht1⟩ := BuildScan.inv hscan1 hm ht
      obtain ⟨s2, tags, st2, rets, hexec, hscan2, halign2, hevents2, hrets, hprov2, hcover2, hloc2, htags⟩ :=
        ih s1 hi1 hg1 hm1 ht1 halign1
      have hpos1 : st1.pos = st.pos + 1 := by
        have hp1 := BuildScan.pos_eq hscan1
        simpa using hp1
      refine ⟨s2, (i0, tag) :: tags, st2, obs.toList ++ rets,
        Exec.step hstep heff hexec, ?_, halign2, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simpa [List.zip_cons_cons] using BuildScan.append hscan1 hscan2
      · calc st2.linOps.map (fun o => o.outcome.clientEvent)
            = st1.linOps.map (fun o => o.outcome.clientEvent) ++ tags.flatMap (fun p => p.2.clientEvents) := hevents2
          _ = (st.linOps.map (fun o => o.outcome.clientEvent) ++ tag.clientEvents) ++
                tags.flatMap (fun p => p.2.clientEvents) := by rw [hevents1]
          _ = st.linOps.map (fun o => o.outcome.clientEvent) ++
                ((i0, tag) :: tags).flatMap (fun p => p.2.clientEvents) := by
                simp [List.flatMap_cons, List.append_assoc]
      · intro r hr
        rcases List.mem_append.mp hr with h | h
        · exact RetObs.fits_ok (hobs r h)
        · have hk := hrets r h
          rw [hpos1] at hk
          exact RetObs.ok_shift hk
      · intro r hr
        rcases List.mem_append.mp hr with h | h
        · obtain ⟨x', hx', hlin, hout, hth, hret⟩ := hprov1 r h
          obtain ⟨x'', hx'', hlin2, hout2, hid2, hret2⟩ :=
            BuildScan.lin_exists_ret hscan2 hx' (by rw [hret]; simp)
          exact ⟨x'', hx'', hlin2.trans hlin, hout2.trans hout,
            by rw [hid2]; exact hth, hret2.trans hret⟩
        · exact hprov2 r h
      · intro k j status hk hget
        cases k with
        | zero =>
            simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hget
            obtain ⟨rfl, rfl⟩ := hget
            obtain ⟨r, hr, hpos, hstat⟩ := hcover1 status rfl
            exact ⟨r, List.mem_append_left _ hr, by simpa using hpos, hstat⟩
        | succ k =>
            simp only [List.getElem?_cons_succ] at hget
            have hk' : k < ms0.length := by simpa using hk
            obtain ⟨r, hr, hpos, hstat⟩ := hcover2 k j status hk' hget
            exact ⟨r, List.mem_append_right _ hr, by rw [hpos]; omega, hstat⟩
      · intro r hr
        rcases List.mem_append.mp hr with h | h
        · have hfit := hobs r h
          have hpos : r.pos = st.pos := hfit.1
          have hthread : r.thread = i0 := hfit.2.1
          have hzero : r.pos - st.pos = 0 := by omega
          refine ⟨GPathTrace.start (GPathTrace.step hstep hs), ?_, ?_⟩
          · change GPathTrace.StateAt (GPathTrace.step hstep hs) (r.pos - st.pos) _
            rw [hzero]
            exact GPathTrace.StateAt.zero _
          · rw [hthread]
            exact hloc1 r h
        · obtain ⟨gk, hk, hloc⟩ := hloc2 r h
          have hkpos : st1.pos ≤ r.pos := (hrets r h).1
          have hidx : r.pos - st.pos = (r.pos - st1.pos) + 1 := by omega
          refine ⟨gk, ?_, hloc⟩
          rw [hidx]
          exact GPathTrace.StateAt.step (h := hstep) hk
      · exact GPathTrace.TagsFor.step (h := hstep) (hs := hs) hclass htags
  | invoke hinv hs ih =>
      rename_i g0 g1 i0 v0 ms0
      obtain ⟨st1, hscan1, halign1, hlin1⟩ := buildScan_invoke halign hinv
      obtain ⟨hm1, ht1⟩ := BuildScan.inv hscan1 hm ht
      obtain ⟨s2, tags, st2, rets, hexec, hscan2, halign2, hevents2, hrets, hprov2, hcover2, hloc2, htags⟩ :=
        ih s hi (GInvoke.gref hg hinv) hm1 ht1 halign1
      have hpos1 : st1.pos = st.pos + 1 := by
        have hp1 := BuildScan.pos_eq hscan1
        simpa using hp1
      have hevents1 : st1.linOps.map (fun o => o.outcome.clientEvent) =
          st.linOps.map (fun o => o.outcome.clientEvent) := by
        rw [hlin1]
      refine ⟨s2, (i0, .stutter) :: tags, st2, rets,
        Exec.invoke hinv (GInvoke.gref hg hinv) (GInvoke.shared_eq hinv)
          (SharedRef.ref hg.hshared) hexec, ?_, halign2, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simpa [List.zip_cons_cons] using BuildScan.append hscan1 hscan2
      · calc st2.linOps.map (fun o => o.outcome.clientEvent)
            = st1.linOps.map (fun o => o.outcome.clientEvent) ++ tags.flatMap (fun p => p.2.clientEvents) := hevents2
          _ = st.linOps.map (fun o => o.outcome.clientEvent) ++
                tags.flatMap (fun p => p.2.clientEvents) := by rw [hevents1]
          _ = st.linOps.map (fun o => o.outcome.clientEvent) ++
                ((i0, StepTag.stutter) :: tags).flatMap (fun p => p.2.clientEvents) := by
                simp [StepTag.clientEvents, List.append_assoc]
      · intro r hr
        have hk := hrets r hr
        rw [hpos1] at hk
        exact RetObs.ok_shift hk
      · exact hprov2
      · intro k j status hk hget
        cases k with
        | zero => simp at hget
        | succ k =>
            simp only [List.getElem?_cons_succ] at hget
            have hk' : k < ms0.length := by simpa using hk
            obtain ⟨r, hr, hpos, hstat⟩ := hcover2 k j status hk' hget
            exact ⟨r, hr, by rw [hpos]; omega, hstat⟩
      · intro r hr
        obtain ⟨gk, hk, hloc⟩ := hloc2 r hr
        have hkpos : st1.pos ≤ r.pos := (hrets r hr).1
        have hidx : r.pos - st.pos = (r.pos - st1.pos) + 1 := by omega
        refine ⟨gk, ?_, hloc⟩
        rw [hidx]
        exact GPathTrace.StateAt.invoke (h := hinv) hk
      · exact GPathTrace.TagsFor.invoke (h := hinv) (hs := hs) htags

theorem GPathTrace.buildHistory {n C limit k : Nat} {kind : Fin n → Kind} {g g' : GState n}
    {ms : List (Move n)}
    (hp : GPathTrace kind g ms g')
    (s : AbsState UInt64) (hi : Inv C limit s) (hg : GRef C limit kind s g)
    (hC : 0 < C) (hpow : C = 2 ^ k) (hCmax : C ≤ 2 ^ 24)
    (hbound : limit < 2 ^ 63) (hlimitC : limit + C ≤ 2 ^ 63)
    (hinit : ∀ i, ∃ v, (g.locals i).phase = Phase.returned v) :
    ∃ s' tags hist rets,
      Exec kind C limit hC s g ms s' g' tags ∧
      BuildHistory kind ms tags hist ∧
      hist.clientEvents = tags.flatMap (fun p => p.2.clientEvents) ∧
      hist.Linearizes C limit (sync s) (sync s') ∧
      RespectsRealTime hist ∧
      (∀ r : RetObs n, r ∈ (rets : List (RetObs n)) →
        r.pos < ms.length ∧ tags[r.pos]? = some (r.thread, .ret r.status) ∧
        (∀ v h, r.outcome = .success (.push v) (.pushed h) → r.loc.out0 = UInt64.ofNat h) ∧
        (∀ h p, r.outcome = .success .pop (.popped h p) → r.loc.out0 = p ∧ r.loc.out1 = UInt64.ofNat h) ∧
        r.status = (stageOfOutcome r.outcome).status) ∧
      (∀ r : RetObs n, r ∈ (rets : List (RetObs n)) →
        ∃ op ∈ hist.ops, op.id.thread = r.thread ∧ op.lin = r.lin ∧
          op.outcome = r.outcome ∧ op.ret = r.pos) ∧
      (∀ (k : Nat) (j : Fin n) (status : UInt64), k < ms.length →
        tags[k]? = some (j, .ret status) → ∃ r ∈ rets, r.pos = k ∧ r.status = status) ∧
      (∀ r : RetObs n, r ∈ (rets : List (RetObs n)) →
        ∃ gk, GPathTrace.StateAt hp r.pos gk ∧ r.loc = gk.locals r.thread) ∧
      GPathTrace.TagsFor C hp tags := by
  have hinitAlign : Align C limit kind g (BuildState.init n) := by
    refine ⟨BuildState.init_wf n, ?_⟩
    intro i
    simp only [AlignThread, BuildState.init]
    exact Or.inl (hinit i)
  obtain ⟨s', tags, st', rets, hexec, hscan, halign', hevents, hrets, hprov, hcover, hloc, htags⟩ :=
    hp.buildScanExec s hi hg hC hpow hCmax hbound hlimitC
      (BuildState.linMem_init (n := n)) (BuildState.threadOK_init (n := n)) hinitAlign
  let hist : ObsHistory n := mkHistory st' halign'.wf
  have hbuild : BuildHistory kind ms tags hist := ⟨st', hscan, halign'.wf, rfl⟩
  have hclient : hist.clientEvents = tags.flatMap (fun p => p.2.clientEvents) := by
    simp only [hist, mkHistory, ObsHistory.clientEvents]
    rw [finalize_clientEvents]
    simpa [BuildState.init] using hevents
  have htrace : ClientTrace C limit (sync s) (tags.flatMap (fun p => p.2.clientEvents)) (sync s') :=
    Exec.clientEvents_trace hexec
  refine ⟨s', tags, hist, rets, hexec, hbuild, hclient, ?_, ObsHistory.real_time hist, ?_, ?_, ?_, ?_, htags⟩
  · rw [ObsHistory.Linearizes]
    exact BuildHistory.linearizes_of_clientEvents hbuild ⟨rfl, rfl⟩ htrace hclient
  · intro r hr
    have hk := hrets r hr
    simp only [RetObs.OK, BuildState.init] at hk
    obtain ⟨-, hlt, hget, hs1, hs2, hstat⟩ := hk
    exact ⟨by simpa using hlt, by simpa using hget, hs1, hs2, hstat⟩
  · intro r hr
    obtain ⟨x', hx', hlin, hout, hth, hret⟩ := hprov r hr
    obtain ⟨op, hop, hlin2, hout2, hid2, hret2⟩ :=
      exists_finalize_of_mem (h := halign'.wf.linSound) hx'
    refine ⟨op, hop, by rw [hid2]; exact hth, hlin2.trans hlin, hout2.trans hout, ?_⟩
    rw [hret2, hret]
    rfl
  · intro k j status hk hget
    obtain ⟨r, hr, hpos, hstat⟩ := hcover k j status hk hget
    exact ⟨r, hr, by simpa [BuildState.init] using hpos, hstat⟩
  · intro r hr
    obtain ⟨gk, hk, hloc⟩ := hloc r hr
    exact ⟨gk, by simpa [BuildState.init] using hk, hloc⟩

theorem trace_linearizable {n C limit k : Nat} {kind : Fin n → Kind}
    {vals : Fin n → UInt64} {g' : GState n} {ms : List (Move n)}
    (hp : GPathTrace kind (initialGState C limit vals) ms g')
    (hC : 0 < C) (hpow : C = 2 ^ k) (hCmax : C ≤ 2 ^ 24)
    (hbound : limit < 2 ^ 63) (hlimitC : limit + C ≤ 2 ^ 63) :
    ∃ s' tags hist rets,
      Exec kind C limit hC (initial UInt64) (initialGState C limit vals) ms s' g' tags ∧
      BuildHistory kind ms tags hist ∧
      hist.clientEvents = tags.flatMap (fun p => p.2.clientEvents) ∧
      hist.Linearizes C limit (sync (initial UInt64)) (sync s') ∧
      RespectsRealTime hist ∧
      (∀ r : RetObs n, r ∈ (rets : List (RetObs n)) →
        r.pos < ms.length ∧ tags[r.pos]? = some (r.thread, .ret r.status) ∧
        (∀ v h, r.outcome = .success (.push v) (.pushed h) → r.loc.out0 = UInt64.ofNat h) ∧
        (∀ h p, r.outcome = .success .pop (.popped h p) → r.loc.out0 = p ∧ r.loc.out1 = UInt64.ofNat h) ∧
        r.status = (stageOfOutcome r.outcome).status) ∧
      (∀ r : RetObs n, r ∈ (rets : List (RetObs n)) →
        ∃ op ∈ hist.ops, op.id.thread = r.thread ∧ op.lin = r.lin ∧
          op.outcome = r.outcome ∧ op.ret = r.pos) ∧
      (∀ (k : Nat) (j : Fin n) (status : UInt64), k < ms.length →
        tags[k]? = some (j, .ret status) → ∃ r ∈ rets, r.pos = k ∧ r.status = status) ∧
      (∀ r : RetObs n, r ∈ (rets : List (RetObs n)) →
        ∃ gk, GPathTrace.StateAt hp r.pos gk ∧ r.loc = gk.locals r.thread) ∧
      GPathTrace.TagsFor C hp tags := by
  apply GPathTrace.buildHistory hp (initial UInt64) (initial_inv C limit)
    (initialGRef kind vals hC hCmax hbound) hC hpow hCmax hbound hlimitC
  intro i
  simp [initialGState, startLocal]


end Mpmc
