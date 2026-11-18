/-
  Copyright (c) 2026 Mohammad Mahdi Abdollahpour.
  The contents of this file are subject to the Common Public Attribution
  License Version 1.0 (the "License"); you may not use this file except in
  compliance with the License. You may obtain a copy of the License at
  https://opensource.org/license/cpal-1-0.
  The Original Code is mpmc-lean. The Initial Developer is Mohammad Mahdi
  Abdollahpour. See LICENSE and NOTICE.
-/
import Mpmc.Concurrent

namespace Mpmc

variable {V : Type}

/-- The progress potential of an abstract queue state.  A push increases `W`,
a pop increases `R`, and a help step increases one of the hints. -/
def psi (s : AbsState V) : Nat := s.W + s.R + s.w + s.r

@[simp] theorem psi_pushState (s : AbsState V) (v : V) :
    psi (pushState s v) = psi s + 1 := by
  simp [psi, pushState]
  omega

@[simp] theorem psi_popState (s : AbsState V) :
    psi (popState s) = psi s + 1 := by
  simp [psi, popState]
  omega

/-- Every non-stuttering event strictly increases the potential. -/
theorem EventStep.psi_lt {z : V} {C limit : Nat} {hC : 0 < C}
    {s m s' m' : _} {a : Action V} {r : Result V}
    (h : EventStep z C limit hC s m (some a) (some r) s' m') :
    psi s < psi s' := by
  cases h with
  | push => simp [psi, pushState]
  | pop => simp [psi, popState]
  | helpW => simp [psi]
  | helpR => simp [psi]

/-- Every event is weakly monotone in the potential. -/
theorem EventStep.psi_mono {z : V} {C limit : Nat} {hC : 0 < C}
    {s m s' m' : _} {a : Option (Action V)} {r : Option (Result V)}
    (h : EventStep z C limit hC s m a r s' m') : psi s ≤ psi s' := by
  cases h with
  | stutter => exact Nat.le_refl _
  | push => simp [psi, pushState]
  | pop => simp [psi, popState]
  | helpW => simp [psi]
  | helpR => simp [psi]

/-- Every event leaves the write counter at least as large as before. -/
theorem EventStep.W_mono {z : V} {C limit : Nat} {hC : 0 < C}
    {s m s' m' : _} {a : Option (Action V)} {r : Option (Result V)}
    (h : EventStep z C limit hC s m a r s' m') : s.W ≤ s'.W := by
  cases h with
  | stutter => exact Nat.le_refl _
  | push => simp [pushState]
  | pop => simp [popState]
  | helpW => simp
  | helpR => simp

/-- Every event leaves the read counter at least as large as before. -/
theorem EventStep.R_mono {z : V} {C limit : Nat} {hC : 0 < C}
    {s m s' m' : _} {a : Option (Action V)} {r : Option (Result V)}
    (h : EventStep z C limit hC s m a r s' m') : s.R ≤ s'.R := by
  cases h with
  | stutter => exact Nat.le_refl _
  | push => simp [pushState]
  | pop => simp [popState]
  | helpW => simp
  | helpR => simp

/-- A trace is weakly monotone in the potential. -/
theorem EventSteps.psi_mono {z : V} {C limit : Nat} {hC : 0 < C}
    {s m s' m' : _} {as : List (Action V)} {rs : List (Result V)}
    (h : EventSteps z C limit hC s m as rs s' m') : psi s ≤ psi s' := by
  induction h with
  | nil => exact Nat.le_refl _
  | stutter hstep _ ih => exact Nat.le_trans (EventStep.psi_mono hstep) ih
  | step hstep _ ih => exact Nat.le_trans (EventStep.psi_mono hstep) ih

/-- A nonempty event trace strictly increases the potential. -/
theorem EventSteps.psi_lt {z : V} {C limit : Nat} {hC : 0 < C}
    {s m s' m' : _} {as : List (Action V)} {rs : List (Result V)}
    (h : EventSteps z C limit hC s m as rs s' m') (hne : as ≠ []) :
    psi s < psi s' := by
  induction h with
  | nil => contradiction
  | stutter hstep _ ih =>
      exact Nat.lt_of_le_of_lt (EventStep.psi_mono hstep) (ih hne)
  | step hstep hs _ =>
      have h1 := EventStep.psi_lt hstep
      have h2 := EventSteps.psi_mono hs
      exact Nat.lt_of_lt_of_le h1 h2

/-- The number of non-stuttering events plus the initial potential is at
most the final potential. -/
theorem EventSteps.length_add_psi_le {z : V} {C limit : Nat} {hC : 0 < C}
    {s m s' m' : _} {as : List (Action V)} {rs : List (Result V)}
    (h : EventSteps z C limit hC s m as rs s' m') :
    as.length + psi s ≤ psi s' := by
  induction h with
  | nil => simp
  | stutter hstep _ ih =>
      have hmono := EventStep.psi_mono hstep
      omega
  | step hstep _ ih =>
      have hlt := EventStep.psi_lt hstep
      simp only [List.length_cons]
      omega

/-- The number of non-stuttering events is bounded by the increase in the
progress potential. -/
theorem EventSteps.length_le_psi {z : V} {C limit : Nat} {hC : 0 < C}
    {s m s' m' : _} {as : List (Action V)} {rs : List (Result V)}
    (h : EventSteps z C limit hC s m as rs s' m') :
    as.length ≤ psi s' - psi s := by
  have h := EventSteps.length_add_psi_le h
  omega

/-- A trace is weakly monotone in the write counter. -/
theorem EventSteps.W_mono {z : V} {C limit : Nat} {hC : 0 < C}
    {s m s' m' : _} {as : List (Action V)} {rs : List (Result V)}
    (h : EventSteps z C limit hC s m as rs s' m') : s.W ≤ s'.W := by
  induction h with
  | nil => exact Nat.le_refl _
  | stutter hstep _ ih => exact Nat.le_trans (EventStep.W_mono hstep) ih
  | step hstep _ ih => exact Nat.le_trans (EventStep.W_mono hstep) ih

/-- A trace is weakly monotone in the read counter. -/
theorem EventSteps.R_mono {z : V} {C limit : Nat} {hC : 0 < C}
    {s m s' m' : _} {as : List (Action V)} {rs : List (Result V)}
    (h : EventSteps z C limit hC s m as rs s' m') : s.R ≤ s'.R := by
  induction h with
  | nil => exact Nat.le_refl _
  | stutter hstep _ ih => exact Nat.le_trans (EventStep.R_mono hstep) ih
  | step hstep _ ih => exact Nat.le_trans (EventStep.R_mono hstep) ih

end Mpmc
