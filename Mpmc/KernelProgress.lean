/-
  Copyright (c) 2026 Mohammad Mahdi Abdollahpour.
  The contents of this file are subject to the Common Public Attribution
  License Version 1.0 (the "License"); you may not use this file except in
  compliance with the License. You may obtain a copy of the License at
  https://opensource.org/license/cpal-1-0.
  The Original Code is mpmc-lean. The Initial Developer is Mohammad Mahdi
  Abdollahpour. See LICENSE and NOTICE.
-/
import Mpmc.Potential
import Mpmc.KernelConcurrent

namespace Mpmc

variable {V : Type}

/-- The number of successful cell operations is `W + R`: every push raises
`W`, every pop raises `R`, and hint help leaves both unchanged. -/
def cellClock (s : AbsState V) : Nat := s.W + s.R

/-- The cell clock is monotone under every event. -/
theorem EventStep.cellClock_mono {z : V} {C limit : Nat} {hC : 0 < C}
    {s m s' m' : _} {a b : _}
    (h : EventStep z C limit hC s m a b s' m') :
    cellClock s ≤ cellClock s' := by
  cases h with
  | stutter => exact Nat.le_refl _
  | push => simp [cellClock, pushState]
  | pop => simp [cellClock, popState]
  | helpW => exact Nat.le_refl _
  | helpR => exact Nat.le_refl _

/-- A successful cell operation strictly raises the cell clock. -/
theorem EventStep.cellClock_lt_of_cell_marker_lt {z : V} {C limit : Nat} {hC : 0 < C}
    {s m s' m' : _} {a r : _}
    (h : EventStep z C limit hC s m a r s' m')
    {j : Nat} (hlt : (m.cells j).marker < (m'.cells j).marker) :
    cellClock s < cellClock s' := by
  cases h with
  | stutter => simp at hlt
  | push => simp [cellClock, pushState]
  | pop => simp [cellClock, popState]
  | helpW => simp at hlt
  | helpR => simp at hlt

/-- A finite event trace preserves the cell-clock lower bound. -/
theorem EventSteps.cellClock_mono {z : V} {C limit : Nat} {hC : 0 < C}
    {s m s' m' : _} {as rs : _}
    (h : EventSteps z C limit hC s m as rs s' m') :
    cellClock s ≤ cellClock s' := by
  induction h with
  | nil => exact Nat.le_refl _
  | stutter hstep _ ih =>
      exact Nat.le_trans (EventStep.cellClock_mono hstep) ih
  | step hstep _ ih =>
      exact Nat.le_trans (EventStep.cellClock_mono hstep) ih

end Mpmc
