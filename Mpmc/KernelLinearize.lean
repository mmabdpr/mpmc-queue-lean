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
  Client-level linearization of a tagged kernel run.

  The abstract machine of `Mpmc.Abstract` carries two hint counters `w` and
  `r` in addition to the queue counters `W` and `R`.  Hints are an
  implementation device: a successful push/pop leaves its hint one step
  behind, and a later `help` catches it up.  At the queue level such a
  transition is a single push/pop.

  This file makes that statement precise.  `sync s` is the canonical
  representative of `s` with both hints current.  A successful push at any
  state, followed immediately by `helpW`, is exactly a canonical push; a
  successful pop followed by `helpR` is exactly a canonical pop.  Failure
  observations (`FULL`, `EMPTY`, `EXHAUSTED`) depend only on `W` and `R`, so
  they are unchanged by `sync`.

  `ClientTrace` is a replay of the queue-level events of a tagged run
  (successful pushes/pops and legal failures) from canonical states.  It is
  the help-erased linearization order: helps are not client operations, but
  they are present internally as the canonical `helpW`/`helpR` steps.
-/

import Mpmc.KernelEffect

namespace Mpmc

open Mpmc.Kernel

variable {V : Type}

/-! ## Canonical (hint-current) states -/

/-- The canonical representative of an abstract state: both hints current. -/
def sync (s : AbsState V) : AbsState V :=
  { s with w := s.W, r := s.R }

@[simp] theorem sync_W (s : AbsState V) : (sync s).W = s.W := rfl
@[simp] theorem sync_R (s : AbsState V) : (sync s).R = s.R := rfl
@[simp] theorem sync_w (s : AbsState V) : (sync s).w = s.W := rfl
@[simp] theorem sync_r (s : AbsState V) : (sync s).r = s.R := rfl
@[simp] theorem sync_val (s : AbsState V) : (sync s).val = s.val := rfl

/-- A help step changes only a hint, so it does not move the canonical
representative. -/
theorem sync_helpW (s : AbsState V) :
    sync ({ s with w := s.w + 1 }) = sync s := by
  cases s
  rfl

theorem sync_helpR (s : AbsState V) :
    sync ({ s with r := s.r + 1 }) = sync s := by
  cases s
  rfl

/-- Failure guards mention only the queue counters, so they are invariant
under `sync`. -/
theorem ObsGuard.sync {C limit : Nat} {s : AbsState V} {k : ObsKind}
    (h : ObsGuard C limit s k) : ObsGuard C limit (sync s) k := by
  cases k <;> simpa [ObsGuard] using h

/-! ## Canonical push and pop -/

/-- A successful push, followed by the help that advances its hint, is a
canonical push from the synced state to the synced post-state. -/
theorem Step.push_sync_help {C limit : Nat} {s s' : AbsState V} {v : V} {h : Nat}
    (hs : Step C limit s (.push v) s' (.pushed h)) :
    ∃ s1 : AbsState V,
      Step C limit (sync s) (.push v) s1 (.pushed h) ∧
      Step C limit s1 .helpW (sync s') .helped := by
  cases hs with
  | push hw hocc hlim =>
      let nv : Nat → Option V := fun i => if i = s.W then some v else s.val i
      refine ⟨{ s with W := s.W + 1, w := s.W, r := s.R, val := nv }, ?_, ?_⟩
      · exact Step.push (s := sync s) rfl hocc hlim
      · apply Step.helpW
        rfl

/-- A successful pop, followed by the help that advances its hint, is a
canonical pop from the synced state to the synced post-state. -/
theorem Step.pop_sync_help {C limit : Nat} {s s' : AbsState V} {v : V} {h : Nat}
    (hs : Step C limit s .pop s' (.popped h v)) :
    ∃ s1 : AbsState V,
      Step C limit (sync s) .pop s1 (.popped h v) ∧
      Step C limit s1 .helpR (sync s') .helped := by
  cases hs with
  | pop hr hne hval =>
      refine ⟨{ s with R := s.R + 1, w := s.W, r := s.R }, ?_, ?_⟩
      · exact Step.pop (s := sync s) rfl hne (by simpa using hval)
      · apply Step.helpR
        rfl

/-! ## Client events and replays -/

/-- One queue-level event: a successful push/pop or a legal failure. -/
inductive ClientEvent (V : Type) where
  | step (a : Action V) (r : Result V)
  | obs (k : ObsKind)

/-- Replay a sequence of queue-level events from canonical states.  A
successful push/pop expands internally to the canonical push/pop plus its
help; a failure is a guard-preserving stutter. -/
inductive ClientTrace (C limit : Nat) :
    AbsState V → List (ClientEvent V) → AbsState V → Prop
  | nil (s : AbsState V) : ClientTrace C limit s [] s
  | push {s s1 s2 sEnd : AbsState V} {v : V} {h : Nat}
      {evs : List (ClientEvent V)}
      (hstep : Step C limit s (.push v) s1 (.pushed h))
      (hhelp : Step C limit s1 .helpW s2 .helped)
      (hrest : ClientTrace C limit s2 evs sEnd) :
      ClientTrace C limit s (.step (.push v) (.pushed h) :: evs) sEnd
  | pop {s s1 s2 sEnd : AbsState V} {v : V} {h : Nat}
      {evs : List (ClientEvent V)}
      (hstep : Step C limit s .pop s1 (.popped h v))
      (hhelp : Step C limit s1 .helpR s2 .helped)
      (hrest : ClientTrace C limit s2 evs sEnd) :
      ClientTrace C limit s (.step .pop (.popped h v) :: evs) sEnd
  | obs {s sEnd : AbsState V} {k : ObsKind} {evs : List (ClientEvent V)}
      (hguard : ObsGuard C limit s k)
      (hrest : ClientTrace C limit s evs sEnd) :
      ClientTrace C limit s (.obs k :: evs) sEnd

/-- Concatenation of client replays. -/
theorem ClientTrace.append {C limit : Nat} {s0 s1 s2 : AbsState V}
    {evs1 evs2 : List (ClientEvent V)}
    (h1 : ClientTrace C limit s0 evs1 s1)
    (h2 : ClientTrace C limit s1 evs2 s2) :
    ClientTrace C limit s0 (evs1 ++ evs2) s2 := by
  induction h1 with
  | nil => exact h2
  | push hstep hhelp _ ih => exact ClientTrace.push hstep hhelp (ih h2)
  | pop hstep hhelp _ ih => exact ClientTrace.pop hstep hhelp (ih h2)
  | obs hguard _ ih => exact ClientTrace.obs hguard (ih h2)

/-- The abstract action trace generated by a client replay, with the
internal help steps included. -/
def ClientTrace.actions : List (ClientEvent V) → List (Action V)
  | [] => []
  | .step (.push v) _ :: evs => .push v :: .helpW :: actions evs
  | .step .pop _ :: evs => .pop :: .helpR :: actions evs
  | _ :: evs => actions evs

/-- The abstract result trace generated by a client replay. -/
def ClientTrace.results : List (ClientEvent V) → List (Result V)
  | [] => []
  | .step (.push _) (.pushed h) :: evs => .pushed h :: .helped :: results evs
  | .step .pop (.popped h v) :: evs => .popped h v :: .helped :: results evs
  | _ :: evs => results evs

/-- A client replay is an abstract `Steps` trace once the internal
helps are inserted. -/
theorem ClientTrace.steps {C limit : Nat} {s0 s' : AbsState V}
    {evs : List (ClientEvent V)}
    (h : ClientTrace C limit s0 evs s') :
    Steps C limit s0 (ClientTrace.actions evs) s'
      (ClientTrace.results evs) := by
  induction h with
  | nil => exact Steps.nil
  | push hstep hhelp _ ih => exact Steps.cons hstep (Steps.cons hhelp ih)
  | pop hstep hhelp _ ih => exact Steps.cons hstep (Steps.cons hhelp ih)
  | obs _ _ ih => exact ih

/-! ## One kernel step at the client level -/

/-- Every tagged effect is one client event (or nothing) between canonical
states. -/
theorem Effect.client_step {z : V} {C limit : Nat} {hC : 0 < C}
    {s m s' m' : _} {tag : StepTag V} (h : Effect z C limit hC s m s' m' tag) :
    ∃ evs : List (ClientEvent V),
      ClientTrace C limit (sync s) evs (sync s') ∧ evs.length ≤ 1 := by
  cases h with
  | stutter hm hs hmem =>
      cases hs; cases hmem
      exact ⟨[], ClientTrace.nil _, by simp⟩
  | event a r hev =>
      cases hev with
      | push hi hm hprov hlim hcell v =>
          obtain ⟨s1, hstep, hhelp⟩ :=
            Step.push_sync_help (EventStep.step (z := z) (hC := hC)
              (EventStep.push (hC := hC) hi hm hprov hlim hcell v))
          exact ⟨[.step (.push v) (.pushed _)],
            ClientTrace.push hstep hhelp (ClientTrace.nil _), by simp⟩
      | pop hi hm hprov hlim p hcell =>
          obtain ⟨s1, hstep, hhelp⟩ :=
            Step.pop_sync_help (EventStep.step (z := z) (hC := hC)
              (EventStep.pop (hC := hC) hi hm hprov hlim p hcell))
          exact ⟨[.step .pop (.popped _ p)],
            ClientTrace.pop hstep hhelp (ClientTrace.nil _), by simp⟩
      | helpW hi hm hw hW =>
          refine ⟨[], ?_, by simp⟩
          rw [sync_helpW]
          exact ClientTrace.nil _
      | helpR hi hm hr hR =>
          refine ⟨[], ?_, by simp⟩
          rw [sync_helpR]
          exact ClientTrace.nil _
  | obs k hm guard hs hmem =>
      cases hs; cases hmem
      exact ⟨[.obs k], ClientTrace.obs (ObsGuard.sync guard) (ClientTrace.nil _), by simp⟩
  | ret status hm hs hmem =>
      cases hs; cases hmem
      exact ⟨[], ClientTrace.nil _, by simp⟩

/-- A whole tagged execution projects to a client replay, in trace order. -/
theorem Exec.client_trace {n C limit : Nat} {hC : 0 < C} {kind : Fin n → Kind}
    {s : AbsState UInt64} {g : GState n} {ms : List (Move n)}
    {s' : AbsState UInt64} {g' : GState n}
    {tags : List (Fin n × StepTag UInt64)}
    (h : Exec kind C limit hC s g ms s' g' tags) :
    ∃ evs : List (ClientEvent UInt64),
      ClientTrace C limit (sync s) evs (sync s') ∧
      evs.length ≤ tags.length := by
  induction h with
  | nil => exact ⟨[], ClientTrace.nil _, by simp⟩
  | step hstep heff hs ih =>
      obtain ⟨evs1, htrace1, hlen1⟩ := Effect.client_step (z := (0 : UInt64)) heff
      obtain ⟨evs2, htrace2, hlen2⟩ := ih
      refine ⟨evs1 ++ evs2, ClientTrace.append htrace1 htrace2, ?_⟩
      simp only [List.length_append, List.length_cons]
      omega
  | invoke h hg' hshared href hs ih =>
      obtain ⟨evs, htrace, hlen⟩ := ih
      refine ⟨evs, ?_, ?_⟩
      · simpa [hshared] using htrace
      · simp only [List.length_cons]
        omega

/-- **Help-erased linearization.**  Every finite tagged kernel execution has
a queue-level replay from the canonical initial state to the canonical final
state, in the order of its push/pop/observation events.  Internal helps are
retained as canonical `helpW`/`helpR` steps, so this is sound in the
hint-carrying abstract machine. -/
theorem Exec.exists_client_trace {n C limit : Nat} {hC : 0 < C}
    {kind : Fin n → Kind} {s : AbsState UInt64} {g : GState n}
    {ms : List (Move n)} {s' : AbsState UInt64} {g' : GState n}
    {tags : List (Fin n × StepTag UInt64)}
    (h : Exec kind C limit hC s g ms s' g' tags) :
    ∃ evs : List (ClientEvent UInt64),
      ClientTrace C limit (sync s) evs (sync s') ∧
      evs.length ≤ tags.length :=
  Exec.client_trace h

/-! ## The queue-level scan -/

/-- A canonical state: both hints are current. -/
def Canonical (s : AbsState V) : Prop := s.w = s.W ∧ s.r = s.R

/-- Queue-level linearization of a client event list.  This is the
hint-free specification: a push/pop changes only `W`/`R` and the value map,
and a failure is a guard-preserving stutter. -/
inductive ClientScan (C limit : Nat) :
    AbsState V → List (ClientEvent V) → AbsState V → Prop
  | nil (s : AbsState V) : ClientScan C limit s [] s
  | push {s sEnd : AbsState V} {v : V} {evs : List (ClientEvent V)}
      (hc : Canonical s) (hocc : s.W - s.R < C) (hlim : s.W < limit)
      (hrest : ClientScan C limit (sync (pushState s v)) evs sEnd) :
      ClientScan C limit s (.step (.push v) (.pushed s.W) :: evs) sEnd
  | pop {s sEnd : AbsState V} {v : V} {evs : List (ClientEvent V)}
      (hc : Canonical s) (hne : s.R < s.W) (hval : s.val s.R = some v)
      (hrest : ClientScan C limit (sync (popState s)) evs sEnd) :
      ClientScan C limit s (.step .pop (.popped s.R v) :: evs) sEnd
  | obs {s sEnd : AbsState V} {k : ObsKind} {evs : List (ClientEvent V)}
      (hguard : ObsGuard C limit s k)
      (hrest : ClientScan C limit s evs sEnd) :
      ClientScan C limit s (.obs k :: evs) sEnd

/-- Concatenation of queue-level scans. -/
theorem ClientScan.append {C limit : Nat} {s0 s1 s2 : AbsState V}
    {evs1 evs2 : List (ClientEvent V)}
    (h1 : ClientScan C limit s0 evs1 s1)
    (h2 : ClientScan C limit s1 evs2 s2) :
    ClientScan C limit s0 (evs1 ++ evs2) s2 := by
  induction h1 with
  | nil => exact h2
  | push hc hocc hlim _ ih => exact ClientScan.push hc hocc hlim (ih h2)
  | pop hc hne hval _ ih => exact ClientScan.pop hc hne hval (ih h2)
  | obs hguard _ ih => exact ClientScan.obs hguard (ih h2)

/-- The canonical abstract action trace of a client event list. -/
def ClientScan.actions : List (ClientEvent V) → List (Action V)
  | [] => []
  | .step (.push v) _ :: evs => .push v :: .helpW :: actions evs
  | .step .pop _ :: evs => .pop :: .helpR :: actions evs
  | _ :: evs => actions evs

/-- The canonical abstract result trace of a client event list. -/
def ClientScan.results : List (ClientEvent V) → List (Result V)
  | [] => []
  | .step (.push _) (.pushed h) :: evs => .pushed h :: .helped :: results evs
  | .step .pop (.popped h v) :: evs => .popped h v :: .helped :: results evs
  | _ :: evs => results evs

/-- A queue-level scan is an abstract `Steps` trace with the
canonical helps inserted. -/
theorem ClientScan.steps {C limit : Nat} {s0 s' : AbsState V}
    {evs : List (ClientEvent V)}
    (h : ClientScan C limit s0 evs s') :
    Steps C limit s0 (ClientScan.actions evs) s'
      (ClientScan.results evs) := by
  induction h with
  | nil => exact Steps.nil
  | push hc hocc hlim hrest ih =>
      rename_i s sEnd v evs
      have hw : s.w = s.W := hc.1
      have hstep : Step C limit s (.push v) (pushState s v) (.pushed s.W) :=
        Step.push hw hocc hlim
      have hEq : ({ pushState s v with w := (pushState s v).w + 1 } : AbsState V) =
          sync (pushState s v) := by
        simp [sync, pushState, hw, hc.2]
      have hhelp : Step C limit (pushState s v) .helpW
          (sync (pushState s v)) .helped := by
        rw [← hEq]
        exact Step.helpW (s := pushState s v) (by simp [pushState, hw])
      exact Steps.cons hstep (Steps.cons hhelp ih)
  | pop hc hne hval hrest ih =>
      rename_i s sEnd v evs
      have hr : s.r = s.R := hc.2
      have hstep : Step C limit s .pop (popState s) (.popped s.R v) :=
        Step.pop hr hne hval
      have hEq : ({ popState s with r := (popState s).r + 1 } : AbsState V) =
          sync (popState s) := by
        simp [sync, popState, hr, hc.1]
      have hhelp : Step C limit (popState s) .helpR
          (sync (popState s)) .helped := by
        rw [← hEq]
        exact Step.helpR (s := popState s) (by simp [popState, hr])
      exact Steps.cons hstep (Steps.cons hhelp ih)
  | obs hguard hrest ih => exact ih

/-- A client replay is a queue-level scan. -/
theorem ClientTrace.toClientScan {C limit : Nat} {s0 s' : AbsState V}
    {evs : List (ClientEvent V)}
    (hc : Canonical s0) (h : ClientTrace C limit s0 evs s') :
    ClientScan C limit s0 evs s' := by
  induction h with
  | nil => exact ClientScan.nil _
  | push hstep hhelp hrest ih =>
      rename_i s s1 s2 sEnd v h evs
      cases hstep with
      | push hw hocc hlim =>
          have hcanon : s2 = sync (pushState s v) := by
            cases hhelp
            simp [sync, pushState, hw, hc.2]
          cases hcanon
          exact ClientScan.push hc hocc hlim (ih ⟨rfl, rfl⟩)
  | pop hstep hhelp hrest ih =>
      rename_i s s1 s2 sEnd v h evs
      cases hstep with
      | pop hr hne hval =>
          have hcanon : s2 = sync (popState s) := by
            cases hhelp
            simp [sync, popState, hr, hc.1]
          cases hcanon
          exact ClientScan.pop hc hne hval (ih ⟨rfl, rfl⟩)
  | obs hguard hrest ih =>
      rename_i s sEnd k evs
      exact ClientScan.obs hguard (ih hc)

end Mpmc
