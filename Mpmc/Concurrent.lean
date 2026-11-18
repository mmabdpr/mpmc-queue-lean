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
  Concurrent refinement: the shared-memory event layer.

  The kernel's shared mutations are whole-cell compare-exchanges and
  hint compare-exchanges.  This file isolates that layer from control
  flow.  An `EventStep` is one admissible atomic event (or a stutter), and
  a list of events is proved to refine an abstract `Steps` trace.  The
  control-flow-to-event mapping is mechanized in `Mpmc/KernelSim.lean`
  (local stages and the `GStep` simulation) and `Mpmc/KernelTrace.lean`
  (finite global schedules); see `docs/proof.md`.
-/

import Mpmc.Protocol

namespace Mpmc

variable {V : Type}

/-- At slot `h % C`, an empty cell for `h` is the push-ready cell exactly
when `h` is the publication counter and the queue has space. -/
theorem viewCell_empty_self {C limit : Nat} {s : AbsState V} (z : V)
    (hi : Inv C limit s) (hC : 0 < C) {h : Nat} (hle : h ≤ s.W) :
    viewCell z C s (h % C) = emptyCell z h ↔
      h = s.W ∧ s.W - s.R < C := by
  constructor
  · intro hview
    have hpos : slotPos s.R (h % C) C = h := by
      have hc := congrArg cellPos hview
      rw [viewCell_pos] at hc
      simpa [cellPos, emptyCell] using hc
    have hnot : ¬ slotPos s.R (h % C) C < s.W := by
      intro hlt
      have hcell := viewCell_ready_cell z C s (h % C) hlt
      rw [hview] at hcell
      have hc := congrArg Cell.marker hcell
      simp [emptyCell, fullCell] at hc
      omega
    have hW : h = s.W := by omega
    refine ⟨hW, ?_⟩
    by_cases hfull : s.W - s.R = C
    · have hsp : slotPos s.R (s.W % C) C = s.W - C :=
        slotPos_push_full hi hfull hC
      rw [hW, hsp] at hpos
      omega
    · have hocc := hi.hocc
      omega
  · rintro ⟨hW, hocc⟩
    subst h
    have hpos : slotPos s.R (s.W % C) C = s.W := by
      apply (slotPos_unique hC (Nat.mod_lt _ hC)
        (R := s.R) (j := s.W % C) (p := s.W) ?_ ?_ rfl).symm
      · exact hi.hR_le_W
      · omega
    rw [viewCell, hpos]
    simp

/-- At slot `h % C`, a full cell for `h` is the pop-ready cell exactly
when `h` is the consumed counter and a value is published. -/
theorem viewCell_full_self {C limit : Nat} {s : AbsState V} (z : V)
    (hi : Inv C limit s) (hC : 0 < C) {h : Nat} (hle : h ≤ s.R) {p : V} :
    viewCell z C s (h % C) = fullCell h p ↔
      h = s.R ∧ s.R < s.W ∧ p = (s.val s.R).getD z := by
  constructor
  · intro hview
    have hpos : slotPos s.R (h % C) C = h := by
      have hc := congrArg cellPos hview
      rw [viewCell_pos] at hc
      simp [cellPos, fullCell] at hc
      omega
    have hR : h = s.R := by
      have hge := slotPos_ge (R := s.R) (j := h % C) (C := C) hC
      omega
    have hready : cellReady (viewCell z C s (h % C)) = true := by
      rw [hview]
      exact cellReady_full h p
    have hlt0 := (viewCell_ready z C s (h % C)).mp hready
    have hlt : s.R < s.W := by
      rw [hpos] at hlt0
      omega
    refine ⟨hR, hlt, ?_⟩
    have hcell := viewCell_ready_cell z C s (h % C) hlt0
    rw [hview] at hcell
    have hp := congrArg Cell.payload hcell
    simp [fullCell] at hp
    rw [hp, hpos, hR]
  · rintro ⟨hR, hlt, hp⟩
    subst h
    rw [hp]
    rw [viewCell_ready_cell z C s (s.R % C) (by
      rw [slotPos_self hC]
      exact hlt)]
    simp [slotPos_self hC]

/-! ## Atomic shared-memory events -/

/-- A failed operation that is legal at the linearization point, but does not
change the abstract queue state.  These events are kept outside `Action` and
`Result`, so the FIFO trace theorems are unchanged. -/
inductive ObsKind where
  | pushFull
  | popEmpty
  | pushExhausted
  | popExhausted
  deriving DecidableEq, Repr

/-- The state guard for a legal failed operation. -/
def ObsGuard (C limit : Nat) (s : AbsState V) : ObsKind → Prop
  | .pushFull => s.W - s.R = C
  | .popEmpty => s.R = s.W
  | .pushExhausted => s.W = limit
  | .popExhausted => s.R = limit

/-- One admissible atomic shared event, or a stutter.

`h` is the local hint that the kernel used for the event.  For a push,
`h` is at most the current shared write hint; for a pop, at most the
current shared read hint.  Those provenance facts are exactly what the
CAS-success style arguments need. -/
inductive EventStep (z : V) (C limit : Nat) (hC : 0 < C) :
    AbsState V → Mem V → Option (Action V) → Option (Result V) →
      AbsState V → Mem V → Prop
  | stutter {s : AbsState V} {m : Mem V} (hm : Ref z C s m) :
      EventStep z C limit hC s m none none s m
  | push {s : AbsState V} {m : Mem V} (hi : Inv C limit s) (hm : Ref z C s m)
      {h : Nat} (hprov : h ≤ s.w) (hlim : h < limit)
      (hcell : m.cells (h % C) = emptyCell z h) (v : V) :
      EventStep z C limit hC s m (some (.push v)) (some (.pushed h))
        (pushState s v) (m.setCell (h % C) (fullCell h v))
  | pop {s : AbsState V} {m : Mem V} (hi : Inv C limit s) (hm : Ref z C s m)
      {h : Nat} (hprov : h ≤ s.r) (hlim : h < limit)
      (p : V) (hcell : m.cells (h % C) = fullCell h p) :
      EventStep z C limit hC s m (some .pop) (some (.popped h p))
        (popState s) (m.setCell (h % C) (emptyCell z (h + C)))
  | helpW {s : AbsState V} {m : Mem V} (hi : Inv C limit s) (hm : Ref z C s m)
      {h : Nat} (hw : m.w = h) (hW : s.W = h + 1) :
      EventStep z C limit hC s m (some .helpW) (some .helped)
        { s with w := s.w + 1 } { m with w := h + 1 }
  | helpR {s : AbsState V} {m : Mem V} (hi : Inv C limit s) (hm : Ref z C s m)
      {h : Nat} (hr : m.r = h) (hR : s.R = h + 1) :
      EventStep z C limit hC s m (some .helpR) (some .helped)
        { s with r := s.r + 1 } { m with r := h + 1 }
/-- The cell part of the memory refinement, with no constraint on hints.
This is the only part of `Ref` used to justify a successful whole-cell
compare-exchange: stale relaxed hints cannot make a cell CAS unsafe. -/
def CellRef (z : V) (C : Nat) (s : AbsState V) (m : Mem V) : Prop :=
  ∀ j, j < C → m.cells j = viewCell z C s j

/-- A non-stutter event is exactly one abstract transition. -/
theorem EventStep.step {z : V} {C limit : Nat} {hC : 0 < C}
    {s m s' m' : _} {a : Action V} {r : Result V}
    (h : EventStep z C limit hC s m (some a) (some r) s' m') :
    Step C limit s a s' r := by
  cases h with
  | push hi hm hprov hlim hcell v =>
      rename_i h
      have hcell' := hcell
      rw [hm.2.2 (h % C) (Nat.mod_lt h hC)] at hcell'
      have hle : h ≤ s.W := Nat.le_trans hprov hi.hw_le
      obtain ⟨hW, hocc⟩ := (viewCell_empty_self z hi hC hle).mp hcell'
      subst h
      have hwle := hi.hw_le
      have hw : s.w = s.W := by omega
      exact Step.push hw hocc hlim
  | pop hi hm hprov hlim p hcell =>
      rename_i h
      have hcell' := hcell
      rw [hm.2.2 (h % C) (Nat.mod_lt h hC)] at hcell'
      have hle : h ≤ s.R := Nat.le_trans hprov hi.hr_le
      obtain ⟨hR, hlt, hp⟩ := (viewCell_full_self z hi hC hle).mp hcell'
      subst h
      have hrle := hi.hr_le
      have hr : s.r = s.R := by omega
      have hval : s.val s.R = some p := by
        obtain ⟨v, hv⟩ := hi.hval_some s.R hlt
        rw [hv] at hp
        simp at hp
        subst p
        exact hv
      exact Step.pop hr hlt hval
  | helpW hi hm hw hW =>
      rename_i h
      have hmw := hm.1
      have hsw : s.w = h := by omega
      have hstep : s.W = s.w + 1 := by omega
      exact Step.helpW hstep
  | helpR hi hm hr hR =>
      rename_i h
      have hmr := hm.2.1
      have hsr : s.r = h := by omega
      have hstep : s.R = s.r + 1 := by omega
      exact Step.helpR hstep

/-- A successful push cell CAS is an abstract push even if the hint fields
of the local memory snapshot are stale. -/
theorem EventStep.push_of_cellRef {z : V} {C limit : Nat} {hC : 0 < C}
    {s : AbsState V} {m : Mem V} (hi : Inv C limit s) (hm : CellRef z C s m)
    {h : Nat} (hprov : h ≤ s.w) (hlim : h < limit)
    (hcell : m.cells (h % C) = emptyCell z h) (v : V) :
    Step C limit s (.push v) (pushState s v) (.pushed h) := by
  let m' : Mem V := { m with w := s.w, r := s.r }
  have hm' : Ref z C s m' := ⟨rfl, rfl, hm⟩
  have hcell' : m'.cells (h % C) = emptyCell z h := by simpa [m'] using hcell
  exact EventStep.step (z := z) (hC := hC) (EventStep.push hi hm' hprov hlim hcell' v)

/-- A successful pop cell CAS is an abstract pop even if the hint fields of
the local memory snapshot are stale. -/
theorem EventStep.pop_of_cellRef {z : V} {C limit : Nat} {hC : 0 < C}
    {s : AbsState V} {m : Mem V} (hi : Inv C limit s) (hm : CellRef z C s m)
    {h : Nat} (hprov : h ≤ s.r) (hlim : h < limit)
    (p : V) (hcell : m.cells (h % C) = fullCell h p) :
    Step C limit s .pop (popState s) (.popped h p) := by
  let m' : Mem V := { m with w := s.w, r := s.r }
  have hm' : Ref z C s m' := ⟨rfl, rfl, hm⟩
  have hcell' : m'.cells (h % C) = fullCell h p := by simpa [m'] using hcell
  exact EventStep.step (z := z) (hC := hC) (EventStep.pop hi hm' hprov hlim p hcell')

/-- Every event preserves the memory refinement. -/
theorem EventStep.ref {z : V} {C limit : Nat} {hC : 0 < C}
    {s m s' m' : _} {a : Option (Action V)} {r : Option (Result V)}
    (h : EventStep z C limit hC s m a r s' m') : Ref z C s' m' := by
  cases h with
  | stutter hm => exact hm
  | push hi hm hprov hlim hcell v =>
      rename_i h
      have hcell' := hcell
      rw [hm.2.2 (h % C) (Nat.mod_lt h hC)] at hcell'
      have hle : h ≤ s.W := Nat.le_trans hprov hi.hw_le
      obtain ⟨hW, hocc⟩ := (viewCell_empty_self z hi hC hle).mp hcell'
      subst h
      have hwle := hi.hw_le
      have hw : s.w = s.W := by omega
      exact push_ref hi hw hocc hC m hm v
  | pop hi hm hprov hlim p hcell =>
      rename_i h
      have hcell' := hcell
      rw [hm.2.2 (h % C) (Nat.mod_lt h hC)] at hcell'
      have hle : h ≤ s.R := Nat.le_trans hprov hi.hr_le
      obtain ⟨hR, hlt, hp⟩ := (viewCell_full_self z hi hC hle).mp hcell'
      subst h
      exact pop_ref hi hC m hm
  | helpW hi hm hw hW =>
      rename_i h
      have hmw : m.w = s.w := hm.1
      have hsw : h = s.w := by omega
      subst h
      rw [hmw]
      exact helpW_ref (limit := limit) (z := z) (s := s) (m := m) hm
  | helpR hi hm hr hR =>
      rename_i h
      have hmr : m.r = s.r := hm.2.1
      have hsr : h = s.r := by omega
      subst h
      rw [hmr]
      exact helpR_ref (limit := limit) (z := z) (s := s) (m := m) hm

/-- Every event leaves every cell marker at least as large as before. -/
theorem EventStep.cell_marker_mono {z : V} {C limit : Nat} {hC : 0 < C}
    {s m s' m' : _} {a : Option (Action V)} {r : Option (Result V)}
    (h : EventStep z C limit hC s m a r s' m') :
    ∀ j, (m.cells j).marker ≤ (m'.cells j).marker := by
  cases h with
  | stutter => intro j; exact Nat.le_refl _
  | push hi hm hprov hlim hcell v =>
      rename_i h
      intro j
      by_cases hj : j = h % C
      · subst j
        rw [hcell]
        simp [Mem.setCell, fullCell, emptyCell]
      · simp [Mem.setCell, hj]
  | pop hi hm hprov hlim p hcell =>
      rename_i h
      intro j
      by_cases hj : j = h % C
      · subst j
        rw [hcell]
        simp [Mem.setCell, fullCell, emptyCell]
        omega
      · simp [Mem.setCell, hj]
  | helpW => intro j; exact Nat.le_refl _
  | helpR => intro j; exact Nat.le_refl _

/-- Every event leaves the write hint at least as large as before. -/
theorem EventStep.w_mono {z : V} {C limit : Nat} {hC : 0 < C}
    {s m s' m' : _} {a : Option (Action V)} {r : Option (Result V)}
    (h : EventStep z C limit hC s m a r s' m') : s.w ≤ s'.w := by
  cases h with
  | stutter => exact Nat.le_refl _
  | push => exact Nat.le_refl _
  | pop => exact Nat.le_refl _
  | helpW => exact Nat.le_succ _
  | helpR => exact Nat.le_refl _

/-- Every event leaves the read hint at least as large as before. -/
theorem EventStep.r_mono {z : V} {C limit : Nat} {hC : 0 < C}
    {s m s' m' : _} {a : Option (Action V)} {r : Option (Result V)}
    (h : EventStep z C limit hC s m a r s' m') : s.r ≤ s'.r := by
  cases h with
  | stutter => exact Nat.le_refl _
  | push => exact Nat.le_refl _
  | pop => exact Nat.le_refl _
  | helpW => exact Nat.le_refl _
  | helpR => exact Nat.le_succ _

/-- A finite list of admissible events with its abstract action/result trace. -/
inductive EventSteps (z : V) (C limit : Nat) (hC : 0 < C) :
    AbsState V → Mem V → List (Action V) → List (Result V) →
      AbsState V → Mem V → Prop
  | nil {s : AbsState V} {m : Mem V} :
      EventSteps z C limit hC s m [] [] s m
  | stutter {s : AbsState V} {m : Mem V} {s' : AbsState V} {m' : Mem V}
      {as : List (Action V)} {rs : List (Result V)} {s'' : AbsState V} {m'' : Mem V}
      (h : EventStep z C limit hC s m none none s' m')
      (hs : EventSteps z C limit hC s' m' as rs s'' m'') :
      EventSteps z C limit hC s m as rs s'' m''
  | step {s : AbsState V} {m : Mem V} {s' : AbsState V} {m' : Mem V}
      {a : Action V} {r : Result V} {as : List (Action V)} {rs : List (Result V)}
      {s'' : AbsState V} {m'' : Mem V}
      (h : EventStep z C limit hC s m (some a) (some r) s' m')
      (hs : EventSteps z C limit hC s' m' as rs s'' m'') :
      EventSteps z C limit hC s m (a :: as) (r :: rs) s'' m''

/-- A changed cell marker certifies that a trace contains at least one
non-stutter event.  This is the formal witness used by the retry-charge
argument: a failed cell CAS that observes a changed marker is charged to
another thread's successful event. -/
theorem EventSteps.event_of_cell_change {z : V} {C limit : Nat} {hC : 0 < C}
    {s m s' m' : _} {as : List (Action V)} {rs : List (Result V)}
    (hs : EventSteps z C limit hC s m as rs s' m') {j : Nat}
    (hchange : (m.cells j).marker ≠ (m'.cells j).marker) :
    as ≠ [] := by
  induction hs with
  | nil => exact absurd rfl hchange
  | stutter hstep _ ih =>
      cases hstep
      exact ih hchange
  | step hstep _ _ =>
      simp

/-- Every event leaves every cell marker at least as large as before. -/
theorem EventSteps.cell_marker_mono {z : V} {C limit : Nat} {hC : 0 < C}
    {s m s' m' : _} {as : List (Action V)} {rs : List (Result V)}
    (hs : EventSteps z C limit hC s m as rs s' m') :
    ∀ j, (m.cells j).marker ≤ (m'.cells j).marker := by
  induction hs with
  | nil => intro j; exact Nat.le_refl _
  | stutter h _ ih =>
      intro j
      exact Nat.le_trans (EventStep.cell_marker_mono h j) (ih j)
  | step h _ ih =>
      intro j
      exact Nat.le_trans (EventStep.cell_marker_mono h j) (ih j)

/-- Every event sequence leaves the write hint at least as large as before. -/
theorem EventSteps.w_mono {z : V} {C limit : Nat} {hC : 0 < C}
    {s m s' m' : _} {as : List (Action V)} {rs : List (Result V)}
    (hs : EventSteps z C limit hC s m as rs s' m') : s.w ≤ s'.w := by
  induction hs with
  | nil => exact Nat.le_refl _
  | stutter h _ ih => exact Nat.le_trans (EventStep.w_mono h) ih
  | step h _ ih => exact Nat.le_trans (EventStep.w_mono h) ih

/-- Every event sequence leaves the read hint at least as large as before. -/
theorem EventSteps.r_mono {z : V} {C limit : Nat} {hC : 0 < C}
    {s m s' m' : _} {as : List (Action V)} {rs : List (Result V)}
    (hs : EventSteps z C limit hC s m as rs s' m') : s.r ≤ s'.r := by
  induction hs with
  | nil => exact Nat.le_refl _
  | stutter h _ ih => exact Nat.le_trans (EventStep.r_mono h) ih
  | step h _ ih => exact Nat.le_trans (EventStep.r_mono h) ih

/-- The event trace refines the abstract transition trace. -/
theorem EventSteps.steps {z : V} {C limit : Nat} {hC : 0 < C}
    {s m s' m' : _} {as : List (Action V)} {rs : List (Result V)}
    (hs : EventSteps z C limit hC s m as rs s' m') :
    Steps C limit s as s' rs := by
  induction hs with
  | nil => exact Steps.nil
  | stutter h _ ih =>
      cases h; exact ih
  | step h _ ih => exact Steps.cons (EventStep.step h) ih

/-- The event trace preserves the memory refinement. -/
theorem EventSteps.ref {z : V} {C limit : Nat} {hC : 0 < C}
    {s m s' m' : _} {as : List (Action V)} {rs : List (Result V)}
    (hm : Ref z C s m) (hs : EventSteps z C limit hC s m as rs s' m') :
    Ref z C s' m' := by
  revert hm
  induction hs with
  | nil => intro hm; exact hm
  | stutter h _ ih =>
      intro hm
      exact ih (EventStep.ref h)
  | step h _ ih =>
      intro hm
      exact ih (EventStep.ref h)

end Mpmc
