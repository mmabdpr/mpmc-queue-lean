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
  Observed real-time histories.

  `Mpmc.History` packages a real-time history as `TimedOp` values whose
  linearization points are supplied by the caller.  This file builds the
  corresponding layer *from a tagged kernel schedule* (`Move` plus
  `StepTag`): a scan of the schedule opens a record at `Move.invoke`,
  selects one push/pop event or one legal failure observation as the
  linearization point, and closes the record at the kernel return.

  The scan is data-level (syntactic): `BuildHistory` is a
  relation between the schedule and the history.  It does not by itself
  claim that the selected events are legal; the separate `Linearizes`
  relation checks that against the abstract queue semantics.  The
  connection from a tagged kernel path to a `BuildHistory` scan that
  `Linearizes` is proved in `Mpmc.KernelBuild` (`GPath.buildHistory`,
  `initial_linearizable`).

  All positions (`inv`, `lin`, `ret`) are indices into the zipped schedule
  `ms.zip tags`, i.e. counts of moves.  The scan may consume only the
  common prefix when `tags` is shorter than `ms`; it never invents schedule
  positions.
-/

import Mpmc.KernelEffect
import Mpmc.KernelLinearize

namespace Mpmc

open Mpmc.Kernel

variable {n : Nat}

/-! ## Identifiers, outcomes, and timed operations -/

/-- Name of one operation: the thread and its per-thread invocation
generation.  A thread can be reused after its operation returns, and the
generation distinguishes the successive invocations. -/
structure OpId (n : Nat) where
  thread : Fin n
  generation : Nat
  deriving DecidableEq, Repr

/-- The observable result of an operation: a successful abstract step, or a
legal failed observation. -/
inductive OpOutcome where
  /-- The operation linearized as an abstract push/pop with this result. -/
  | success (a : Action UInt64) (r : Result UInt64)
  /-- The operation failed with a legal observation. -/
  | failure (k : ObsKind)

/-- One completed (or synthetically completed) operation with its real-time
interval and its linearization outcome. -/
structure TimedObsOp (n : Nat) where
  id : OpId n
  /-- The value passed at invocation. -/
  input : UInt64
  inv : Nat
  lin : Nat
  ret : Nat
  outcome : OpOutcome
  inv_le_lin : inv ≤ lin
  lin_le_ret : lin ≤ ret

/-- A real-time history: operations listed in linearization order. -/
structure ObsHistory (n : Nat) where
  ops : List (TimedObsOp n)
  lin_sorted : ops.Pairwise (fun a b => a.lin < b.lin)

/-! ## Projections -/

/-- The action of a successful outcome, if any. -/
def OpOutcome.action? : OpOutcome → Option (Action UInt64)
  | .success a _ => some a
  | .failure _ => none

/-- The result of a successful outcome, if any. -/
def OpOutcome.result? : OpOutcome → Option (Result UInt64)
  | .success _ r => some r
  | .failure _ => none

/-- Whether the outcome is a successful abstract step. -/
def OpOutcome.isSuccess : OpOutcome → Bool
  | .success _ _ => true
  | .failure _ => false

/-- The kernel status code an outcome must have at return.  Successful
operations return `0`; failed operations return a nonzero status. -/
def OpOutcome.acceptsStatus : OpOutcome → UInt64 → Prop
  | .success _ _, status => status = 0
  | .failure _, status => status ≠ 0

/-- The action labels of a history, in linearization order.  Failed
operations contribute no abstract action. -/
def ObsHistory.actions (h : ObsHistory n) : List (Action UInt64) :=
  h.ops.filterMap (fun op => op.outcome.action?)

/-- The result labels of a history, in linearization order. -/
def ObsHistory.results (h : ObsHistory n) : List (Result UInt64) :=
  h.ops.filterMap (fun op => op.outcome.result?)

/-! ## Real-time order -/

/-- A history respects real time: if `a` returns before `b` is invoked, then
`a` linearizes before `b`. -/
def RespectsRealTime (h : ObsHistory n) : Prop :=
  ∀ a ∈ h.ops, ∀ b ∈ h.ops, a.ret < b.inv → a.lin < b.lin

/-- `inv ≤ lin ≤ ret` already forces real-time order. -/
theorem ObsHistory.real_time (h : ObsHistory n) : RespectsRealTime h := by
  intro a _ b _ hlt
  have h1 := a.inv_le_lin
  have h2 := a.lin_le_ret
  have h3 := b.inv_le_lin
  omega

/-- In particular, every history built at a later stage respects real time. -/
theorem RespectsRealTime.of_history (h : ObsHistory n) : RespectsRealTime h :=
  ObsHistory.real_time h

/-! ## Linearization against the abstract queue

A linearization scan walks the history in linearization order.  It tracks
the current abstract state: a successful operation must be a
`Step`, and a failed operation must satisfy its `ObsGuard` *at that point*
and leaves the state unchanged.  This is the precise statement of
linearizability for this history format: the guard of a failure is checked
at its linearization position, not at an arbitrary later state. -/

/-- The queue-level event of a recorded outcome. -/
def TimedObsOp.clientEvent (o : TimedObsOp n) : ClientEvent UInt64 :=
  match o.outcome with
  | .success a r => .step a r
  | .failure k => .obs k

/-- The queue-level event sequence of a history, in linearization order. -/
def ObsHistory.clientEvents (h : ObsHistory n) : List (ClientEvent UInt64) :=
  h.ops.map TimedObsOp.clientEvent

/-- The canonical abstract action trace of a history (with the internal
helps inserted). -/
def ObsHistory.canonicalActions (h : ObsHistory n) : List (Action UInt64) :=
  ClientScan.actions h.clientEvents

/-- The canonical abstract result trace of a history. -/
def ObsHistory.canonicalResults (h : ObsHistory n) : List (Result UInt64) :=
  ClientScan.results h.clientEvents

/-- A history is linearizable when its queue-level events replay against the
hint-free queue scan from `s₀` to `s'`.  Failed operations are legal
guard-preserving stutters at their linearization positions. -/
def ObsHistory.Linearizes (h : ObsHistory n) (C limit : Nat)
    (s₀ s' : AbsState UInt64) : Prop :=
  ClientScan C limit s₀ h.clientEvents s'

/-- A linearized history yields an abstract `Steps` trace with the
canonical helps inserted. -/
theorem ObsHistory.Linearizes.steps {h : ObsHistory n} {C limit : Nat}
    {s₀ s' : AbsState UInt64} (hl : h.Linearizes C limit s₀ s') :
    Steps C limit s₀ h.canonicalActions s' h.canonicalResults := by
  simpa [ObsHistory.Linearizes, ObsHistory.canonicalActions,
    ObsHistory.canonicalResults, ObsHistory.clientEvents]
    using ClientScan.steps hl

/-- Linearization preserves the abstract invariant. -/
theorem ObsHistory.Linearizes.inv {h : ObsHistory n} {C limit : Nat}
    {s₀ s' : AbsState UInt64} (hl : h.Linearizes C limit s₀ s')
    (hi : Inv C limit s₀) : Inv C limit s' :=
  Steps.inv hi (ObsHistory.Linearizes.steps hl)

/-! ## The data-level scan

`BuildState` is the state of a single left-to-right pass over the zipped
schedule `ms.zip tags`:

* `pos` is the number of moves consumed (the next position);
* `gens i` is the next generation of thread `i`;
* `phase i` says whether thread `i` is idle, has an open invocation, or has
  already linearized its current operation;
* `linOps` accumulates linearized operations in selection order, which is
  increasing `lin` order.
-/

/-- The number of the next generation of each thread. -/
abbrev Gens (n : Nat) := Fin n → Nat

/-- An invoked operation that has not selected its linearization point. -/
structure PendingOp (n : Nat) where
  id : OpId n
  input : UInt64
  inv : Nat

/-- A linearized operation whose kernel return may still be ahead.
`ret = none` means the schedule ended (or the operation has not returned
yet), in which case the scan uses the end index as a synthetic response. -/
structure LinOp (n : Nat) where
  id : OpId n
  input : UInt64
  inv : Nat
  lin : Nat
  ret : Option Nat
  outcome : OpOutcome
  inv_lt_lin : inv < lin

/-- `o` is usable at position `pos`: its linearization point is before
`pos`, and if it already has a recorded return, that return is after the
linearization point. -/
def LinOp.Sound (o : LinOp n) (pos : Nat) : Prop :=
  o.lin < pos ∧ ∀ r, o.ret = some r → o.lin < r

/-- The per-thread phase of the scan. -/
inductive ThreadPhase (n : Nat) where
  | idle
  | invoked (p : PendingOp n)
  | linearized (o : LinOp n)

/-- The state of the schedule scan. -/
structure BuildState (n : Nat) where
  pos : Nat
  gens : Gens n
  phase : Fin n → ThreadPhase n
  linOps : List (LinOp n)

/-- The initial scan state: empty, at position `0`, every thread idle with
generation `0`. -/
def BuildState.init (n : Nat) : BuildState n where
  pos := 0
  gens := fun _ => 0
  phase := fun _ => .idle
  linOps := []

/-- Point update of a finite function. -/
def setFun {α : Type} {n : Nat} (f : Fin n → α) (i : Fin n) (a : α) :
    Fin n → α :=
  fun j => if j = i then a else f j

@[simp] theorem setFun_same {α : Type} {n : Nat} (f : Fin n → α) (i : Fin n)
    (a : α) : setFun f i a i = a := by
  simp [setFun]

theorem setFun_of_ne {α : Type} {n : Nat} (f : Fin n → α) {i j : Fin n}
    (a : α) (h : j ≠ i) : setFun f i a j = f j := by
  simp [setFun, h]

/-- Consume one move without changing any operation record. -/
def BuildState.advance (st : BuildState n) : BuildState n :=
  { st with pos := st.pos + 1 }

/-- Open a fresh invocation of thread `i`.  Generation `st.gens i` is used
and then incremented. -/
def BuildState.openInvoke (st : BuildState n) (i : Fin n) (v : UInt64) :
    BuildState n :=
  { st with
    pos := st.pos + 1
    gens := setFun st.gens i (st.gens i + 1)
    phase := setFun st.phase i
      (.invoked { id := ⟨i, st.gens i⟩, input := v, inv := st.pos }) }

/-- The `LinOp` produced when linearizing the pending operation `p` at the
current position. -/
def BuildState.mkLinOp (st : BuildState n) (p : PendingOp n)
    (outcome : OpOutcome) (hinv : p.inv < st.pos) : LinOp n :=
  { id := p.id
    input := p.input
    inv := p.inv
    lin := st.pos
    ret := none
    outcome := outcome
    inv_lt_lin := hinv }

/-- Linearize the pending operation `p` of thread `i` at the current
position.  `hinv` records that the invocation came earlier in the scan. -/
def BuildState.linearize (st : BuildState n) (i : Fin n) (p : PendingOp n)
    (outcome : OpOutcome) (hinv : p.inv < st.pos) : BuildState n :=
  { st with
    pos := st.pos + 1
    phase := setFun st.phase i (.linearized (st.mkLinOp p outcome hinv))
    linOps := st.linOps ++ [st.mkLinOp p outcome hinv] }

/-- Replace the recorded response of `id` by `ret`.  Linearization points
are untouched, so the linearization order is preserved. -/
def closeLin (id : OpId n) (ret : Nat) : List (LinOp n) → List (LinOp n)
  | [] => []
  | o :: os =>
      (if o.id = id ∧ o.ret = none then { o with ret := some ret } else o) :: closeLin id ret os

theorem closeLin_length (id : OpId n) (ret : Nat) (l : List (LinOp n)) :
    (closeLin id ret l).length = l.length := by
  induction l with
  | nil => rfl
  | cons a as ih =>
      simp only [closeLin]
      by_cases hid : a.id = id <;> simp [hid, ih]

/-- Close the linearized operation `o` of thread `i` at the current
position. -/
def BuildState.close (st : BuildState n) (i : Fin n) (o : LinOp n) :
    BuildState n :=
  { st with
    pos := st.pos + 1
    phase := setFun st.phase i .idle
    linOps := closeLin o.id st.pos st.linOps }

/-- Drop a pending, never-linearized invocation of thread `i` at its return
(this is how failed operations without a selected observation are treated). -/
def BuildState.dropPending (st : BuildState n) (i : Fin n) : BuildState n :=
  { st with
    pos := st.pos + 1
    phase := setFun st.phase i .idle }

/-! ### Projection lemmas for the scan-state operations -/

@[simp] theorem BuildState.advance_pos (st : BuildState n) :
    st.advance.pos = st.pos + 1 := rfl

@[simp] theorem BuildState.advance_gens (st : BuildState n) :
    st.advance.gens = st.gens := rfl

@[simp] theorem BuildState.advance_phase (st : BuildState n) :
    st.advance.phase = st.phase := rfl

@[simp] theorem BuildState.advance_linOps (st : BuildState n) :
    st.advance.linOps = st.linOps := rfl

@[simp] theorem BuildState.openInvoke_pos (st : BuildState n) (i : Fin n)
    (v : UInt64) : (st.openInvoke i v).pos = st.pos + 1 := rfl

@[simp] theorem BuildState.openInvoke_gens (st : BuildState n) (i : Fin n)
    (v : UInt64) : (st.openInvoke i v).gens = setFun st.gens i (st.gens i + 1) :=
  rfl

@[simp] theorem BuildState.openInvoke_phase (st : BuildState n) (i : Fin n)
    (v : UInt64) :
    (st.openInvoke i v).phase =
      setFun st.phase i
        (.invoked { id := ⟨i, st.gens i⟩, input := v, inv := st.pos }) := rfl

@[simp] theorem BuildState.openInvoke_linOps (st : BuildState n) (i : Fin n)
    (v : UInt64) : (st.openInvoke i v).linOps = st.linOps := rfl

@[simp] theorem BuildState.linearize_pos (st : BuildState n) (i : Fin n)
    (p : PendingOp n) (outcome : OpOutcome) (hinv : p.inv < st.pos) :
    (st.linearize i p outcome hinv).pos = st.pos + 1 := rfl

@[simp] theorem BuildState.linearize_gens (st : BuildState n) (i : Fin n)
    (p : PendingOp n) (outcome : OpOutcome) (hinv : p.inv < st.pos) :
    (st.linearize i p outcome hinv).gens = st.gens := rfl

@[simp] theorem BuildState.linearize_phase (st : BuildState n) (i : Fin n)
    (p : PendingOp n) (outcome : OpOutcome) (hinv : p.inv < st.pos) :
    (st.linearize i p outcome hinv).phase =
      setFun st.phase i (.linearized (st.mkLinOp p outcome hinv)) := rfl

@[simp] theorem BuildState.linearize_linOps (st : BuildState n) (i : Fin n)
    (p : PendingOp n) (outcome : OpOutcome) (hinv : p.inv < st.pos) :
    (st.linearize i p outcome hinv).linOps =
      st.linOps ++ [st.mkLinOp p outcome hinv] := rfl

@[simp] theorem BuildState.mkLinOp_lin (st : BuildState n) (p : PendingOp n)
    (outcome : OpOutcome) (hinv : p.inv < st.pos) :
    (st.mkLinOp p outcome hinv).lin = st.pos := rfl

@[simp] theorem BuildState.mkLinOp_inv (st : BuildState n) (p : PendingOp n)
    (outcome : OpOutcome) (hinv : p.inv < st.pos) :
    (st.mkLinOp p outcome hinv).inv = p.inv := rfl

@[simp] theorem BuildState.mkLinOp_ret (st : BuildState n) (p : PendingOp n)
    (outcome : OpOutcome) (hinv : p.inv < st.pos) :
    (st.mkLinOp p outcome hinv).ret = none := rfl

@[simp] theorem BuildState.close_pos (st : BuildState n) (i : Fin n) (o : LinOp n) :
    (st.close i o).pos = st.pos + 1 := rfl

@[simp] theorem BuildState.close_gens (st : BuildState n) (i : Fin n) (o : LinOp n) :
    (st.close i o).gens = st.gens := rfl

@[simp] theorem BuildState.close_linOps (st : BuildState n) (i : Fin n) (o : LinOp n) :
    (st.close i o).linOps = closeLin o.id st.pos st.linOps := rfl

@[simp] theorem BuildState.close_phase (st : BuildState n) (i : Fin n) (o : LinOp n) :
    (st.close i o).phase = setFun st.phase i .idle := rfl

@[simp] theorem BuildState.dropPending_pos (st : BuildState n) (i : Fin n) :
    (st.dropPending i).pos = st.pos + 1 := rfl

@[simp] theorem BuildState.dropPending_gens (st : BuildState n) (i : Fin n) :
    (st.dropPending i).gens = st.gens := rfl

@[simp] theorem BuildState.dropPending_phase (st : BuildState n) (i : Fin n) :
    (st.dropPending i).phase = setFun st.phase i .idle := rfl

@[simp] theorem BuildState.dropPending_linOps (st : BuildState n) (i : Fin n) :
    (st.dropPending i).linOps = st.linOps := rfl

/-! ### Well-formedness of a scan state

These invariants are preserved by every scan step and are needed to turn
the accumulated `LinOp`s into `TimedObsOp`s at the end. -/

/-- The scan-state invariant. -/
structure BuildState.WF (st : BuildState n) : Prop where
  /-- Linearized operations are listed in strictly increasing `lin` order. -/
  sorted : st.linOps.Pairwise (fun a b => a.lin < b.lin)
  /-- Every accumulated operation is sound at the current position. -/
  linSound : ∀ o ∈ st.linOps, o.Sound st.pos
  /-- Every pending invocation started strictly before the current position. -/
  invSound : ∀ i p, st.phase i = .invoked p → p.inv < st.pos
  /-- Every linearized-but-unclosed phase is sound at the current position. -/
  phaseSound : ∀ i o, st.phase i = .linearized o → o.Sound st.pos

theorem BuildState.init_wf (n : Nat) : (BuildState.init n).WF where
  sorted := List.Pairwise.nil
  linSound := by intro o ho; simp [BuildState.init] at ho
  invSound := by intro i p h; simp [BuildState.init] at h
  phaseSound := by intro i o h; simp [BuildState.init] at h

namespace BuildState

theorem wf_advance {st : BuildState n} (h : st.WF) : st.advance.WF where
  sorted := by simpa only [advance_linOps] using h.sorted
  linSound := by
    intro o ho
    simp only [advance_linOps] at ho
    have hs := h.linSound o ho
    have h1 := hs.1
    refine ⟨?_, fun r hr => hs.2 r hr⟩
    simp only [advance_pos]
    omega
  invSound := by
    intro i p hp
    simp only [advance_phase] at hp
    have hs := h.invSound i p hp
    simp only [advance_pos]
    omega
  phaseSound := by
    intro i o ho
    simp only [advance_phase] at ho
    have hs := h.phaseSound i o ho
    have h1 := hs.1
    refine ⟨?_, fun r hr => hs.2 r hr⟩
    simp only [advance_pos]
    omega

theorem wf_openInvoke {st : BuildState n} {i : Fin n} {v : UInt64}
    (hidle : st.phase i = .idle) (h : st.WF) : (st.openInvoke i v).WF where
  sorted := by simpa only [openInvoke_linOps] using h.sorted
  linSound := by
    intro o ho
    simp only [openInvoke_linOps] at ho
    have hs := h.linSound o ho
    have h1 := hs.1
    refine ⟨?_, fun r hr => hs.2 r hr⟩
    simp only [openInvoke_pos]
    omega
  invSound := by
    intro j p hp
    by_cases hj : j = i
    · subst hj
      simp only [openInvoke_phase, setFun_same] at hp
      cases hp
      simp [openInvoke_pos]
    · have hp' : st.phase j = .invoked p := by
        simpa [openInvoke_phase, setFun_of_ne _ _ hj] using hp
      have hs := h.invSound j p hp'
      simp only [openInvoke_pos]
      omega
  phaseSound := by
    intro j o ho
    by_cases hj : j = i
    · subst hj
      simp only [openInvoke_phase, setFun_same] at ho
      cases ho
    · have ho' : st.phase j = .linearized o := by
        simpa [openInvoke_phase, setFun_of_ne _ _ hj] using ho
      have hs := h.phaseSound j o ho'
      have h1 := hs.1
      refine ⟨?_, fun r hr => hs.2 r hr⟩
      simp only [openInvoke_pos]
      omega

theorem sorted_append {l : List (LinOp n)} {o : LinOp n}
    (hs : l.Pairwise (fun a b => a.lin < b.lin))
    (ho : ∀ a ∈ l, a.lin < o.lin) :
    (l ++ [o]).Pairwise (fun a b => a.lin < b.lin) := by
  rw [List.pairwise_append]
  refine ⟨hs, by simp, ?_⟩
  intro a ha b hb
  simp only [List.mem_singleton] at hb
  subst hb
  exact ho a ha

theorem wf_linearize {st : BuildState n} {i : Fin n} {p : PendingOp n}
    {outcome : OpOutcome} {hinv : p.inv < st.pos} (h : st.WF) :
    (st.linearize i p outcome hinv).WF where
  sorted := by
    simp only [linearize_linOps]
    exact sorted_append h.sorted (fun a ha => (h.linSound a ha).1)
  linSound := by
    intro o ho
    simp only [linearize_linOps] at ho
    rcases List.mem_append.mp ho with ho | ho
    · have hs := h.linSound o ho
      have h1 := hs.1
      refine ⟨?_, fun r hr => hs.2 r hr⟩
      simp only [linearize_pos]
      omega
    · simp only [List.mem_singleton] at ho
      subst ho
      simp only [linearize_pos]
      refine ⟨?_, ?_⟩
      · simp only [mkLinOp_lin]
        omega
      · intro r hr
        simp only [mkLinOp_ret] at hr
        simp at hr
  invSound := by
    intro j q hq
    by_cases hj : j = i
    · subst hj
      simp only [linearize_phase, setFun_same] at hq
      cases hq
    · have hq' : st.phase j = .invoked q := by
        simpa [linearize_phase, setFun_of_ne _ _ hj] using hq
      have hs := h.invSound j q hq'
      simp only [linearize_pos]
      omega
  phaseSound := by
    intro j o ho
    by_cases hj : j = i
    · subst hj
      simp only [linearize_phase, setFun_same] at ho
      cases ho
      simp only [linearize_pos]
      refine ⟨?_, ?_⟩
      · simp only [mkLinOp_lin]
        omega
      · intro r hr
        simp only [mkLinOp_ret] at hr
        simp at hr
    · have ho' : st.phase j = .linearized o := by
        simpa [linearize_phase, setFun_of_ne _ _ hj] using ho
      have hs := h.phaseSound j o ho'
      have h1 := hs.1
      refine ⟨?_, fun r hr => hs.2 r hr⟩
      simp only [linearize_pos]
      omega

/-- Closing a record only replaces its response; it never changes the
linearization point or the position of any other record. -/
theorem closeLin_mem {id : OpId n} {ret : Nat} {l : List (LinOp n)} {b : LinOp n}
    (hb : b ∈ closeLin id ret l) : ∃ b0 ∈ l, b.lin = b0.lin := by
  induction l with
  | nil => simp [closeLin] at hb
  | cons a as ih =>
      simp only [closeLin] at hb
      rcases List.mem_cons.mp hb with hba | hbas
      · subst b
        refine ⟨a, List.mem_cons_self, ?_⟩
        by_cases hc : a.id = id ∧ a.ret = none <;> simp [hc]
      · obtain ⟨b0, hb0, hlin⟩ := ih hbas
        exact ⟨b0, List.mem_cons_of_mem _ hb0, hlin⟩

theorem closeLin_sound {l : List (LinOp n)} {pos : Nat}
    (h : ∀ o ∈ l, o.Sound pos) (id : OpId n) :
    ∀ o ∈ closeLin id pos l, o.Sound (pos + 1) := by
  induction l with
  | nil => intro o ho; simp [closeLin] at ho
  | cons a as ih =>
      intro o ho
      simp only [closeLin] at ho
      rcases List.mem_cons.mp ho with hoa | hoas
      · subst o
        by_cases hc : a.id = id ∧ a.ret = none
        · simp only [if_pos hc]
          have ha := h a List.mem_cons_self
          have h1 := ha.1
          refine ⟨Nat.lt_succ_of_lt h1, ?_⟩
          intro r hr
          simp only [Option.some.injEq] at hr
          subst hr
          exact h1
        · simp only [if_neg hc]
          have ha := h a List.mem_cons_self
          exact ⟨Nat.lt_succ_of_lt ha.1, fun r hr => ha.2 r hr⟩
      · exact ih (fun x hx => h x (List.mem_cons_of_mem _ hx)) o hoas

theorem closeLin_sorted {l : List (LinOp n)}
    (h : l.Pairwise (fun a b => a.lin < b.lin)) (id : OpId n) (ret : Nat) :
    (closeLin id ret l).Pairwise (fun a b => a.lin < b.lin) := by
  induction l with
  | nil => simp [closeLin]
  | cons a as ih =>
      rw [List.pairwise_cons] at h
      simp only [closeLin]
      rw [List.pairwise_cons]
      refine ⟨?_, ?_⟩
      · intro b hb
        obtain ⟨b0, hb0, hlin⟩ := closeLin_mem hb
        rw [hlin]
        by_cases hc : a.id = id ∧ a.ret = none <;> simpa [hc] using h.1 b0 hb0
      · exact ih h.2

theorem wf_close {st : BuildState n} {i : Fin n} {o : LinOp n}
    (h : st.WF) : (st.close i o).WF where
  sorted := by
    simp only [close_linOps]
    exact closeLin_sorted h.sorted o.id st.pos
  linSound := by
    intro a ha
    simp only [close_linOps] at ha
    have hs := closeLin_sound h.linSound o.id a ha
    simpa [LinOp.Sound, close_pos] using hs
  invSound := by
    intro j p hp
    by_cases hj : j = i
    · subst hj
      simp only [close_phase, setFun_same] at hp
      cases hp
    · have hp' : st.phase j = .invoked p := by
        simpa [close_phase, setFun_of_ne _ _ hj] using hp
      have hs := h.invSound j p hp'
      simp only [close_pos]
      omega
  phaseSound := by
    intro j q hq
    by_cases hj : j = i
    · subst hj
      simp only [close_phase, setFun_same] at hq
      cases hq
    · have hq' : st.phase j = .linearized q := by
        simpa [close_phase, setFun_of_ne _ _ hj] using hq
      have hs := h.phaseSound j q hq'
      have h1 := hs.1
      refine ⟨?_, fun r hr => hs.2 r hr⟩
      simp only [close_pos]
      omega

theorem wf_dropPending {st : BuildState n} {i : Fin n} (h : st.WF) :
    (st.dropPending i).WF where
  sorted := by simpa only [dropPending_linOps] using h.sorted
  linSound := by
    intro o ho
    simp only [dropPending_linOps] at ho
    have hs := h.linSound o ho
    have h1 := hs.1
    refine ⟨?_, fun r hr => hs.2 r hr⟩
    simp only [dropPending_pos]
    omega
  invSound := by
    intro j p hp
    by_cases hj : j = i
    · subst hj
      simp only [dropPending_phase, setFun_same] at hp
      cases hp
    · have hp' : st.phase j = .invoked p := by
        simpa [dropPending_phase, setFun_of_ne _ _ hj] using hp
      have hs := h.invSound j p hp'
      simp only [dropPending_pos]
      omega
  phaseSound := by
    intro j o ho
    by_cases hj : j = i
    · subst hj
      simp only [dropPending_phase, setFun_same] at ho
      cases ho
    · have ho' : st.phase j = .linearized o := by
        simpa [dropPending_phase, setFun_of_ne _ _ hj] using ho
      have hs := h.phaseSound j o ho'
      have h1 := hs.1
      refine ⟨?_, fun r hr => hs.2 r hr⟩
      simp only [dropPending_pos]
      omega

end BuildState

/-! ### Legal failure kinds for each thread kind -/

/-- A push thread can only fail with a full-queue or publication-horizon
observation; a pop thread with an empty-queue or consumption-horizon
observation. -/
def Kind.admitsFailure : Kind → ObsKind → Prop
  | .push, .pushFull => True
  | .push, .pushExhausted => True
  | .pop, .popEmpty => True
  | .pop, .popExhausted => True
  | _, _ => False

/-! ### The scan relation -/

/-- A left-to-right scan of a zipped schedule.  Each constructor consumes
exactly one schedule entry; the `pos` field advances by one per entry. -/
inductive BuildScan (kind : Fin n → Kind) :
    BuildState n → List (Move n × Fin n × StepTag UInt64) → BuildState n → Prop
  | nil (st : BuildState n) : BuildScan kind st [] st
  /-- An invocation opens a fresh operation for an idle thread. -/
  | invoke {st : BuildState n} {i : Fin n} {v : UInt64}
      {rest : List (Move n × Fin n × StepTag UInt64)} {st' : BuildState n}
      (hidle : st.phase i = .idle)
      (h : BuildScan kind (st.openInvoke i v) rest st') :
      BuildScan kind st ((.invoke i v, i, .stutter) :: rest) st'
  /-- A kernel stutter is invisible to the history. -/
  | stutterStep {st : BuildState n} {i : Fin n}
      {rest : List (Move n × Fin n × StepTag UInt64)} {st' : BuildState n}
      (h : BuildScan kind st.advance rest st') :
      BuildScan kind st ((.step i, i, .stutter) :: rest) st'
  /-- A help event is an internal abstract step, not an operation
  linearization. -/
  | helpStep {st : BuildState n} {i : Fin n} {a : Action UInt64} {r : Result UInt64}
      {rest : List (Move n × Fin n × StepTag UInt64)} {st' : BuildState n}
      (hhelp : a = .helpW ∨ a = .helpR)
      (h : BuildScan kind st.advance rest st') :
      BuildScan kind st ((.step i, i, .event a r) :: rest) st'
  /-- A push event of a push thread whose pending value matches linearizes
  the operation as a successful push. -/
  | pushEvent {st : BuildState n} {i : Fin n} {v : UInt64}
      {r : Result UInt64} {p : PendingOp n}
      {rest : List (Move n × Fin n × StepTag UInt64)} {st' : BuildState n}
      (hkind : kind i = .push)
      (hp : st.phase i = .invoked p)
      (hval : p.input = v)
      (hinv : p.inv < st.pos)
      (h : BuildScan kind (st.linearize i p (.success (.push v) r) hinv) rest st') :
      BuildScan kind st ((.step i, i, .event (.push v) r) :: rest) st'
  /-- A pop event of a pop thread linearizes the operation as a successful
  pop. -/
  | popEvent {st : BuildState n} {i : Fin n} {r : Result UInt64}
      {p : PendingOp n}
      {rest : List (Move n × Fin n × StepTag UInt64)} {st' : BuildState n}
      (hkind : kind i = .pop)
      (hp : st.phase i = .invoked p)
      (hinv : p.inv < st.pos)
      (h : BuildScan kind (st.linearize i p (.success .pop r) hinv) rest st') :
      BuildScan kind st ((.step i, i, .event .pop r) :: rest) st'
  /-- A legal failure observation linearizes the operation as a failure. -/
  | obsEvent {st : BuildState n} {i : Fin n} {k : ObsKind}
      {p : PendingOp n}
      {rest : List (Move n × Fin n × StepTag UInt64)} {st' : BuildState n}
      (hadmit : (kind i).admitsFailure k)
      (hp : st.phase i = .invoked p)
      (hinv : p.inv < st.pos)
      (h : BuildScan kind (st.linearize i p (.failure k) hinv) rest st') :
      BuildScan kind st ((.step i, i, .obs k) :: rest) st'
  /-- A return after linearization closes the operation.  The status must
  agree with the outcome (`0` for success, nonzero for failure). -/
  | retLin {st : BuildState n} {i : Fin n} {status : UInt64} {o : LinOp n}
      {rest : List (Move n × Fin n × StepTag UInt64)} {st' : BuildState n}
      (hp : st.phase i = .linearized o)
      (hstatus : o.outcome.acceptsStatus status)
      (h : BuildScan kind (st.close i o) rest st') :
      BuildScan kind st ((.step i, i, .ret status) :: rest) st'
  /-- A return of a pending operation with a nonzero status is a failure
  whose observation was not selected; the scan drops it. -/
  | retPending {st : BuildState n} {i : Fin n} {status : UInt64}
      {p : PendingOp n}
      {rest : List (Move n × Fin n × StepTag UInt64)} {st' : BuildState n}
      (hp : st.phase i = .invoked p)
      (hstatus : status ≠ 0)
      (h : BuildScan kind (st.dropPending i) rest st') :
      BuildScan kind st ((.step i, i, .ret status) :: rest) st'
  /-- Any event for an idle thread (a pre-existing invocation outside the
  scanned prefix, or an unrelated step) is ignored. -/
  | skipIdle {st : BuildState n} {i : Fin n} {tag : StepTag UInt64}
      {rest : List (Move n × Fin n × StepTag UInt64)} {st' : BuildState n}
      (hidle : st.phase i = .idle)
      (h : BuildScan kind st.advance rest st') :
      BuildScan kind st ((.step i, i, tag) :: rest) st'

/-! ### Basic scan invariants -/

/-- The scan consumes exactly the length of its schedule. -/
theorem BuildScan.pos_eq {kind : Fin n → Kind} {st st' : BuildState n}
    {l : List (Move n × Fin n × StepTag UInt64)}
    (h : BuildScan kind st l st') : st'.pos = st.pos + l.length := by
  induction h with
  | nil => simp
  | invoke _ _ ih =>
      simp only [BuildState.openInvoke_pos] at ih
      simp only [List.length_cons]
      omega
  | stutterStep _ ih =>
      simp only [BuildState.advance_pos] at ih
      simp only [List.length_cons]
      omega
  | helpStep _ _ ih =>
      simp only [BuildState.advance_pos] at ih
      simp only [List.length_cons]
      omega
  | pushEvent _ _ _ _ _ ih =>
      simp only [BuildState.linearize_pos] at ih
      simp only [List.length_cons]
      omega
  | popEvent _ _ _ _ ih =>
      simp only [BuildState.linearize_pos] at ih
      simp only [List.length_cons]
      omega
  | obsEvent _ _ _ _ ih =>
      simp only [BuildState.linearize_pos] at ih
      simp only [List.length_cons]
      omega
  | retLin _ _ _ ih =>
      simp only [BuildState.close_pos] at ih
      simp only [List.length_cons]
      omega
  | retPending _ _ _ ih =>
      simp only [BuildState.dropPending_pos] at ih
      simp only [List.length_cons]
      omega
  | skipIdle _ _ ih =>
      simp only [BuildState.advance_pos] at ih
      simp only [List.length_cons]
      omega

/-- The number of accumulated linearized operations never exceeds the
number of consumed moves. -/
theorem BuildScan.linOps_length_le_pos {kind : Fin n → Kind} {st st' : BuildState n}
    {l : List (Move n × Fin n × StepTag UInt64)}
    (h : BuildScan kind st l st') (h0 : st.linOps.length ≤ st.pos) :
    st'.linOps.length ≤ st'.pos := by
  induction h with
  | nil => exact h0
  | invoke _ _ ih =>
      apply ih
      simp only [BuildState.openInvoke_linOps, BuildState.openInvoke_pos]
      omega
  | stutterStep _ ih =>
      apply ih
      simp only [BuildState.advance_linOps, BuildState.advance_pos]
      omega
  | helpStep _ _ ih =>
      apply ih
      simp only [BuildState.advance_linOps, BuildState.advance_pos]
      omega
  | pushEvent _ _ _ _ _ ih =>
      apply ih
      simp only [BuildState.linearize_linOps, BuildState.linearize_pos,
        List.length_append, List.length_singleton]
      omega
  | popEvent _ _ _ _ ih =>
      apply ih
      simp only [BuildState.linearize_linOps, BuildState.linearize_pos,
        List.length_append, List.length_singleton]
      omega
  | obsEvent _ _ _ _ ih =>
      apply ih
      simp only [BuildState.linearize_linOps, BuildState.linearize_pos,
        List.length_append, List.length_singleton]
      omega
  | retLin _ _ _ ih =>
      apply ih
      simp only [BuildState.close_linOps, BuildState.close_pos]
      rw [closeLin_length]
      omega
  | retPending _ _ _ ih =>
      apply ih
      simp only [BuildState.dropPending_linOps, BuildState.dropPending_pos]
      omega
  | skipIdle _ _ ih =>
      apply ih
      simp only [BuildState.advance_linOps, BuildState.advance_pos]
      omega

/-- Every scan step preserves well-formedness. -/
theorem BuildScan.wf {kind : Fin n → Kind} {st st' : BuildState n}
    {l : List (Move n × Fin n × StepTag UInt64)}
    (h : BuildScan kind st l st') : st.WF → st'.WF := by
  induction h with
  | nil => exact id
  | invoke hidle _ ih => exact fun hwf => ih (BuildState.wf_openInvoke hidle hwf)
  | stutterStep _ ih => exact fun hwf => ih (BuildState.wf_advance hwf)
  | helpStep _ _ ih => exact fun hwf => ih (BuildState.wf_advance hwf)
  | pushEvent _ _ _ _ _ ih => exact fun hwf => ih (BuildState.wf_linearize hwf)
  | popEvent _ _ _ _ ih => exact fun hwf => ih (BuildState.wf_linearize hwf)
  | obsEvent _ _ _ _ ih => exact fun hwf => ih (BuildState.wf_linearize hwf)
  | retLin _ _ _ ih => exact fun hwf => ih (BuildState.wf_close hwf)
  | retPending _ _ _ ih => exact fun hwf => ih (BuildState.wf_dropPending hwf)
  | skipIdle _ _ ih => exact fun hwf => ih (BuildState.wf_advance hwf)

/-! ### Finalization: `LinOp` to `TimedObsOp` -/

/-- Close a linearized record with `endPos` as a synthetic response when no
kernel return was seen.  `Sound endPos` supplies both proofs. -/
def LinOp.toTimed (endPos : Nat) (o : LinOp n) (h : o.Sound endPos) :
    TimedObsOp n where
  id := o.id
  input := o.input
  inv := o.inv
  lin := o.lin
  ret := o.ret.getD endPos
  outcome := o.outcome
  inv_le_lin := Nat.le_of_lt o.inv_lt_lin
  lin_le_ret := by
    cases hr : o.ret with
    | none =>
        simp only [Option.getD_none]
        exact Nat.le_of_lt h.1
    | some r =>
        have hs := h.2 r hr
        simp only [hr, Option.getD_some]
        exact Nat.le_of_lt hs

/-- Finalize a list of linearized records at the end position. -/
def finalize (endPos : Nat) (l : List (LinOp n))
    (h : ∀ o ∈ l, o.Sound endPos) : List (TimedObsOp n) :=
  l.attach.map (fun x => x.1.toTimed endPos (h x.1 x.2))

theorem finalize_length (endPos : Nat) (l : List (LinOp n))
    (h : ∀ o ∈ l, o.Sound endPos) : (finalize endPos l h).length = l.length := by
  simp [finalize]

/-- Every finalized operation comes from a record with the same invocation
and linearization positions. -/
theorem mem_finalize {endPos : Nat} {l : List (LinOp n)}
    {h : ∀ o ∈ l, o.Sound endPos} {op : TimedObsOp n}
    (hm : op ∈ finalize endPos l h) :
    ∃ o ∈ l, op.inv = o.inv ∧ op.lin = o.lin := by
  simp only [finalize, List.mem_map] at hm
  obtain ⟨x, hx, rfl⟩ := hm
  exact ⟨x.1, x.2, rfl, rfl⟩

/-! ### Histories built from a schedule -/

/-- `BuildHistory kind ms tags h` holds when a left-to-right scan of the
zipped schedule parses `h`.  The scan:

* opens a record on `Move.invoke i v`;
* linearizes a push operation on a matching `.event (.push v)` tag, a pop
  operation on `.event .pop`, and a failure on `.obs k` when the failure
  kind is legal for the thread's role;
* ignores `.stutter` tags and help events;
* closes a linearized record on `.ret status` when `status` agrees with the
  outcome (`0` for success, nonzero for failure);
* drops pending records that return with a nonzero status or are never
  linearized;
* gives every still-open linearized record a synthetic response at the end
  of the scan.

A history position is therefore always a real schedule position, and the
scan never invents an operation that was not invoked in the schedule. -/
def BuildHistory (kind : Fin n → Kind) (ms : List (Move n))
    (tags : List (Fin n × StepTag UInt64)) (h : ObsHistory n) : Prop :=
  ∃ st' : BuildState n,
    BuildScan kind (BuildState.init n) (ms.zip tags) st' ∧
    ∃ hwf : st'.WF, h.ops = finalize st'.pos st'.linOps hwf.linSound

/-- The number of selected operations is bounded by the number of schedule
moves. -/
theorem BuildHistory.length_le {kind : Fin n → Kind} {ms : List (Move n)}
    {tags : List (Fin n × StepTag UInt64)} {h : ObsHistory n}
    (hb : BuildHistory kind ms tags h) : h.ops.length ≤ ms.length := by
  obtain ⟨st', hscan, hwf, hops⟩ := hb
  rw [hops, finalize_length]
  have hpos := BuildScan.pos_eq (st := BuildState.init n) hscan
  have h0 : (BuildState.init n).linOps.length ≤ (BuildState.init n).pos := by
    simp [BuildState.init]
  have hlen := BuildScan.linOps_length_le_pos hscan h0
  have hzip : (ms.zip tags).length ≤ ms.length := by
    rw [List.length_zip]
    exact Nat.min_le_left _ _
  simp [BuildState.init] at hpos
  omega

/-- Every history position is a position of the scanned schedule. -/
theorem BuildHistory.lin_lt_length {kind : Fin n → Kind} {ms : List (Move n)}
    {tags : List (Fin n × StepTag UInt64)} {h : ObsHistory n}
    (hb : BuildHistory kind ms tags h) {op : TimedObsOp n}
    (ho : op ∈ h.ops) : op.lin < ms.length := by
  obtain ⟨st', hscan, hwf, hops⟩ := hb
  rw [hops] at ho
  obtain ⟨o, ho', -, hlin⟩ := mem_finalize ho
  have hsound := hwf.linSound o ho'
  have hpos := BuildScan.pos_eq (st := BuildState.init n) hscan
  have hzip : (ms.zip tags).length ≤ ms.length := by
    rw [List.length_zip]
    exact Nat.min_le_left _ _
  have hpos' : st'.pos = (ms.zip tags).length := by
    simpa [BuildState.init] using hpos
  rw [hlin]
  have hlt : o.lin < st'.pos := hsound.1
  omega

/-- Every operation selected by the scan is invoked strictly before it
linearizes. -/
theorem BuildHistory.inv_lt_lin {kind : Fin n → Kind} {ms : List (Move n)}
    {tags : List (Fin n × StepTag UInt64)} {h : ObsHistory n}
    (hb : BuildHistory kind ms tags h) {op : TimedObsOp n}
    (ho : op ∈ h.ops) : op.inv < op.lin := by
  obtain ⟨st', hscan, hwf, hops⟩ := hb
  rw [hops] at ho
  obtain ⟨o, ho', hinv, hlin⟩ := mem_finalize ho
  rw [hinv, hlin]
  exact o.inv_lt_lin

/-- Every selected operation completes strictly after it linearizes.  An
operation that is still open at the end of the scan gets the end position
as its synthetic response. -/
theorem BuildHistory.lin_lt_ret {kind : Fin n → Kind} {ms : List (Move n)}
    {tags : List (Fin n × StepTag UInt64)} {h : ObsHistory n}
    (hb : BuildHistory kind ms tags h) {op : TimedObsOp n}
    (ho : op ∈ h.ops) : op.lin < op.ret := by
  obtain ⟨st', hscan, hwf, hops⟩ := hb
  rw [hops] at ho
  -- Recover the source record and the exact finalized value.
  simp only [finalize, List.mem_map] at ho
  obtain ⟨x, hx, hop⟩ := ho
  have hsound := hwf.linSound x.1 x.2
  rw [← hop]
  simp only [LinOp.toTimed]
  cases hr : x.1.ret with
  | none =>
      simp only [hr, Option.getD_none]
      exact hsound.1
  | some r =>
      simp only [hr, Option.getD_some]
      exact hsound.2 r hr

/-- Histories built by the scan respect real time. -/
theorem BuildHistory.real_time {kind : Fin n → Kind} {ms : List (Move n)}
    {tags : List (Fin n × StepTag UInt64)} {h : ObsHistory n}
    (hb : BuildHistory kind ms tags h) : RespectsRealTime h :=
  ObsHistory.real_time h

/-! ## Relation to the kernel alignment

`BuildHistory` is a combinatorial scan: it recovers *which* tagged step
linearizes each operation and proves real-time/position bounds.  The
semantic linearization of the same events is proved separately in
`KernelLinearize`: `ClientTrace.toClientScan` turns every tagged run into a
hint-free `ClientScan`, and `Exec.exists_obs_history` packages it as an
`ObsHistory` that satisfies `ObsHistory.Linearizes`.

The per-invocation bridge is completed in `Mpmc.KernelBuild`.  There,
`gstep_tag` certifies the canonical tag of every kernel step and its
`StepClass`, `buildScan_step` extends the scan by one schedule entry while
preserving the `Align` relation, and `GPath.buildScanExec` /
`GPath.buildHistory` / `initial_linearizable` prove that the scan's
operation records have exactly the run's client events, in order, with the
exact return code (`StepClass.ret_status`).  This file's scan remains the
combinatorial half; no unfinished proof or extra assumption is used in either half.
-/

/-! ## A linearizable history from a client replay -/

/-- The queue outcome of a client event. -/
def ClientEvent.outcome : ClientEvent UInt64 → OpOutcome
  | .step a r => .success a r
  | .obs k => .failure k

/-- The invocation operand of a client event (`0` for pop/failure). -/
def ClientEvent.input : ClientEvent UInt64 → UInt64
  | .step (.push v) _ => v
  | _ => 0

/-- Turn a client-event list into history records at consecutive positions.
Positions here are event positions; the invocation/response packaging of a
full schedule is the `BuildHistory` scan. -/
def ClientTrace.toOps {n : Nat} (id : OpId n) (pos : Nat) :
    List (ClientEvent UInt64) → List (TimedObsOp n)
  | [] => []
  | e :: es =>
      { id := id
        input := e.input
        inv := pos
        lin := pos
        ret := pos + 1
        outcome := e.outcome
        inv_le_lin := Nat.le_refl _
        lin_le_ret := Nat.le_succ _ } ::
      ClientTrace.toOps id (pos + 1) es

theorem ClientTrace.toOps_length {n : Nat} (id : OpId n) (pos : Nat)
    (evs : List (ClientEvent UInt64)) :
    (ClientTrace.toOps id pos evs).length = evs.length := by
  induction evs generalizing pos with
  | nil => rfl
  | cons e es ih => simp [ClientTrace.toOps, ih]

theorem ClientTrace.toOps_lin_ge {n : Nat} (id : OpId n) (pos : Nat)
    (evs : List (ClientEvent UInt64)) {o : TimedObsOp n}
    (ho : o ∈ ClientTrace.toOps id pos evs) : pos ≤ o.lin := by
  induction evs generalizing pos with
  | nil => simp [ClientTrace.toOps] at ho
  | cons e es ih =>
      simp only [ClientTrace.toOps, List.mem_cons] at ho
      rcases ho with rfl | ho
      · exact Nat.le_refl _
      · exact Nat.le_trans (Nat.le_succ pos) (ih (pos + 1) ho)

theorem ClientTrace.toOps_sorted {n : Nat} (id : OpId n) (pos : Nat)
    (evs : List (ClientEvent UInt64)) :
    (ClientTrace.toOps id pos evs).Pairwise (fun a b => a.lin < b.lin) := by
  induction evs generalizing pos with
  | nil => exact List.Pairwise.nil
  | cons e es ih =>
      refine List.pairwise_cons.mpr ⟨?_, ih (pos + 1)⟩
      intro o ho
      have hge := ClientTrace.toOps_lin_ge id (pos + 1) es ho
      simp [ClientTrace.toOps]
      omega

/-- A client replay packaged as a real-time history. -/
def ClientTrace.toHistory {n : Nat} (id : OpId n) (pos : Nat)
    (evs : List (ClientEvent UInt64)) : ObsHistory n :=
  { ops := ClientTrace.toOps id pos evs
    lin_sorted := ClientTrace.toOps_sorted id pos evs }

theorem ClientTrace.toHistory_clientEvents {n : Nat} (id : OpId n) (pos : Nat)
    (evs : List (ClientEvent UInt64)) :
    (ClientTrace.toHistory id pos evs).clientEvents = evs := by
  induction evs generalizing pos with
  | nil => rfl
  | cons e es ih =>
      cases e with
      | step a r =>
          cases a <;> cases r <;>
            simpa [ClientTrace.toHistory, ObsHistory.clientEvents,
              ClientTrace.toOps, TimedObsOp.clientEvent, ClientEvent.outcome]
              using ih (pos + 1)
      | obs k =>
          simpa [ClientTrace.toHistory, ObsHistory.clientEvents,
            ClientTrace.toOps, TimedObsOp.clientEvent, ClientEvent.outcome]
            using ih (pos + 1)

/-- The history obtained from a client replay is linearizable. -/
theorem ClientTrace.toHistory_linearizes {n C limit : Nat}
    {s0 s' : AbsState UInt64} {evs : List (ClientEvent UInt64)}
    (hc : Canonical s0) (ht : ClientTrace C limit s0 evs s')
    (id : OpId n) (pos : Nat) :
    (ClientTrace.toHistory id pos evs).Linearizes C limit s0 s' := by
  rw [ObsHistory.Linearizes, ClientTrace.toHistory_clientEvents]
  exact ClientTrace.toClientScan hc ht

/-- **`Exec` to a linearizable observed history.**  Every finite tagged
kernel execution yields an `ObsHistory` whose operations linearize at the
queue level, with real-time order, and whose length is bounded by the number
of schedule moves. -/
theorem Exec.exists_obs_history {n C limit : Nat} {hC : 0 < C}
    {kind : Fin n → Kind} {s : AbsState UInt64} {g : GState n}
    {ms : List (Move n)} {s' : AbsState UInt64} {g' : GState n}
    {tags : List (Fin n × StepTag UInt64)}
    (hn : 0 < n)
    (h : Exec kind C limit hC s g ms s' g' tags) :
    ∃ hist : ObsHistory n,
      hist.ops.length ≤ tags.length ∧
      hist.Linearizes C limit (sync s) (sync s') ∧
      RespectsRealTime hist := by
  obtain ⟨evs, htrace, hlen⟩ := Exec.client_trace h
  let id : OpId n := ⟨⟨0, hn⟩, 0⟩
  let hist : ObsHistory n := ClientTrace.toHistory id 0 evs
  refine ⟨hist, ?_, ?_, ?_⟩
  · have h1 : hist.ops.length = evs.length := by
      simp [hist, ClientTrace.toHistory, ClientTrace.toOps_length]
    omega
  · exact ClientTrace.toHistory_linearizes ⟨rfl, rfl⟩ htrace id 0
  · exact ObsHistory.real_time hist


end Mpmc
