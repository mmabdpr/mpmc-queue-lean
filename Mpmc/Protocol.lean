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
  Cell protocol.

  The concrete queue is `C` cells plus two 64-bit hints.  A cell holds a
  marker `2 * position + ready` and a payload word.  This file proves that
  the cell in slot `j` is a pure function of `(W, R)`:

    * its position is the unique `p` in `[R, R+C)` with `p % C = j`;
    * it is ready exactly when `p < W`;
    * its payload is `val p` when ready, and the zero word otherwise.

  The transition lemmas at the bottom are the refinement steps: a
  successful cell CAS performs exactly one abstract transition, and a
  hint CAS performs one help transition.
-/

import Mpmc.View

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Mpmc

/-- A concrete cell: a 64-bit marker and a 64-bit payload word. -/
structure Cell (V : Type) where
  marker : Nat
  payload : V

/-- An empty cell for position `p`.  The payload is the zero word. -/
def emptyCell (z : V) (p : Nat) : Cell V :=
  ⟨2 * p, z⟩

/-- A published cell for position `p`. -/
def fullCell (p : Nat) (v : V) : Cell V :=
  ⟨2 * p + 1, v⟩

/-- Position named by a marker. -/
def cellPos (c : Cell V) : Nat :=
  c.marker / 2

/-- Whether a marker names a published cell. -/
def cellReady (c : Cell V) : Bool :=
  c.marker % 2 == 1

@[simp] theorem cellPos_empty (z : V) (p : Nat) :
    cellPos (emptyCell z p) = p := by
  simp [cellPos, emptyCell]

@[simp] theorem cellPos_full (p : Nat) (v : V) :
    cellPos (fullCell p v) = p := by
  simp [cellPos, fullCell]
  omega

@[simp] theorem cellReady_empty (z : V) (p : Nat) :
    cellReady (emptyCell z p) = false := by
  unfold cellReady emptyCell
  have h : (2 * p) % 2 = 0 := by omega
  simp [h]

@[simp] theorem cellReady_full (p : Nat) (v : V) :
    cellReady (fullCell p v) = true := by
  unfold cellReady fullCell
  have h : (2 * p + 1) % 2 = 1 := by omega
  simp [h]

/-- The cell that slot `j` must contain in abstract state `s`.

`z` is the zero payload word; it is used only for cells that are not
ready, because the implementation zeroes the payload when it consumes. -/
def viewCell (z : V) (C : Nat) (s : AbsState V) (j : Nat) : Cell V :=
  if slotPos s.R j C < s.W then
    fullCell (slotPos s.R j C) ((s.val (slotPos s.R j C)).getD z)
  else
    emptyCell z (slotPos s.R j C)

theorem viewCell_pos (z : V) (C : Nat) (s : AbsState V) (j : Nat) :
    cellPos (viewCell z C s j) = slotPos s.R j C := by
  unfold viewCell
  split <;> simp

theorem viewCell_ready (z : V) (C : Nat) (s : AbsState V) (j : Nat) :
    cellReady (viewCell z C s j) = true ↔ slotPos s.R j C < s.W := by
  unfold viewCell
  split <;> simp_all

theorem viewCell_not_ready (z : V) (C : Nat) (s : AbsState V) (j : Nat)
    (h : ¬ slotPos s.R j C < s.W) :
    viewCell z C s j = emptyCell z (slotPos s.R j C) := by
  unfold viewCell
  simp [h]

theorem viewCell_ready_cell (z : V) (C : Nat) (s : AbsState V) (j : Nat)
    (h : slotPos s.R j C < s.W) :
    viewCell z C s j =
      fullCell (slotPos s.R j C) ((s.val (slotPos s.R j C)).getD z) := by
  unfold viewCell
  simp [h]

/-- Concrete shared memory: two hints and the cell array. -/
structure Mem (V : Type) where
  w : Nat
  r : Nat
  cells : Nat → Cell V

/-- Replace one slot. -/
def Mem.setCell (m : Mem V) (j : Nat) (c : Cell V) : Mem V :=
  { m with cells := fun k => if k = j then c else m.cells k }

/-- The refinement relation: the hints agree and every slot is the view. -/
def Ref (z : V) (C : Nat) (s : AbsState V) (m : Mem V) : Prop :=
  m.w = s.w ∧ m.r = s.r ∧ ∀ j, j < C → m.cells j = viewCell z C s j

/-! ## Slot positions -/

theorem slotPos_self {R C : Nat} (hC : 0 < C) :
    slotPos R (R % C) C = R := by
  exact (slotPos_unique hC (Nat.mod_lt _ hC) (Nat.le_refl _) (by omega) rfl).symm

theorem slotPos_succ_self {R C : Nat} (hC : 0 < C) :
    slotPos (R + 1) (R % C) C = R + C := by
  apply (slotPos_unique hC (Nat.mod_lt _ hC)
    (R := R + 1) (j := R % C) (p := R + C) ?_ ?_ ?_).symm
  · omega
  · omega
  · have h := Nat.add_mul_mod_self_left R C 1
    simp

theorem slotPos_push {C limit : Nat} {s : AbsState V} (h : Inv C limit s)
    (hw : s.w = s.W) (hocc : s.W - s.R < C) (hC : 0 < C) :
    slotPos s.R (s.W % C) C = s.W := by
  apply (slotPos_unique hC (Nat.mod_lt _ hC)
    (R := s.R) (j := s.W % C) (p := s.W) ?_ ?_ rfl).symm
  · exact h.hR_le_W
  · omega

theorem slotPos_push_full {C limit : Nat} {s : AbsState V} (h : Inv C limit s)
    (hfull : s.W - s.R = C) (hC : 0 < C) :
    slotPos s.R (s.W % C) C = s.W - C := by
  apply (slotPos_unique hC (Nat.mod_lt _ hC)
    (R := s.R) (j := s.W % C) (p := s.W - C) ?_ ?_ ?_).symm
  · omega
  · omega
  · have hWgeC : C ≤ s.W := by omega
    have hmod : s.W % C = (s.W - C) % C := Nat.mod_eq_sub_mod hWgeC
    exact hmod.symm

/-! ## Cell views under the abstract transitions -/

/-- State after a successful push. -/
def pushState (s : AbsState V) (v : V) : AbsState V :=
  { s with W := s.W + 1, val := fun i => if i = s.W then some v else s.val i }

/-- State after a successful pop. -/
def popState (s : AbsState V) : AbsState V :=
  { s with R := s.R + 1 }

theorem viewCell_push_self {C limit : Nat} {s : AbsState V} (h : Inv C limit s)
    (hw : s.w = s.W) (hocc : s.W - s.R < C) (hC : 0 < C) (v : V) :
    viewCell z C (pushState s v) (s.W % C) = fullCell s.W v := by
  have hpos : slotPos s.R (s.W % C) C = s.W := slotPos_push h hw hocc hC
  unfold viewCell pushState
  rw [hpos]
  simp

theorem viewCell_push_other {C limit : Nat} {s : AbsState V} (h : Inv C limit s)
    (hw : s.w = s.W) (hocc : s.W - s.R < C) (hC : 0 < C) (v : V)
    {j : Nat} (hjC : j < C) (hj : j ≠ s.W % C) :
    viewCell z C (pushState s v) j = viewCell z C s j := by
  have hpos : slotPos s.R j C ≠ s.W := by
    intro hp
    have hmod := slotPos_mod (R := s.R) (j := j) (C := C) hjC
    rw [hp] at hmod
    exact hj hmod.symm
  unfold viewCell pushState
  by_cases hp : slotPos s.R j C < s.W
  · have hp' : slotPos s.R j C < s.W + 1 := by omega
    simp [hp, hp', hpos]
  · have hp' : ¬ slotPos s.R j C < s.W + 1 := by omega
    simp [hp, hp', hpos]

theorem viewCell_pop_self {C limit : Nat} {s : AbsState V} (h : Inv C limit s)
    (hC : 0 < C) :
    viewCell z C (popState s) (s.R % C) = emptyCell z (s.R + C) := by
  have hocc := h.hocc
  have hpos : slotPos (s.R + 1) (s.R % C) C = s.R + C := slotPos_succ_self hC
  unfold viewCell popState
  rw [hpos]
  have hnot : ¬ s.R + C < s.W := by omega
  simp [hnot]

theorem viewCell_pop_other {C limit : Nat} {s : AbsState V} (h : Inv C limit s)
    (hC : 0 < C) {j : Nat} (hjC : j < C) (hj : j ≠ s.R % C) :
    viewCell z C (popState s) j = viewCell z C s j := by
  have hmod := slotPos_mod (R := s.R) (j := j) (C := C) hjC
  have hpne : slotPos s.R j C ≠ s.R := by
    intro hp
    apply hj
    rw [← hp, hmod]
  have hpos : slotPos (s.R + 1) j C = slotPos s.R j C := by
    apply (slotPos_unique hC hjC
      (R := s.R + 1) (j := j) (p := slotPos s.R j C) ?_ ?_ hmod).symm
    · have hge := slotPos_ge (R := s.R) (j := j) (C := C) hC
      omega
    · have hlt := slotPos_lt (R := s.R) (j := j) (C := C) hjC
      omega
  unfold viewCell popState
  rw [hpos]

/-- At a lagging write hint the slot is either the full cell for `w` or
the empty cell for `w+C`. -/
theorem helpW_cell {C limit : Nat} {s : AbsState V} (h : Inv C limit s)
    (hW : s.W = s.w + 1) (hC : 0 < C) :
    viewCell z C s (s.w % C) = fullCell s.w ((s.val s.w).getD z) ∨
    viewCell z C s (s.w % C) = emptyCell z (s.w + C) := by
  by_cases hR : s.R ≤ s.w
  · left
    have hpos : slotPos s.R (s.w % C) C = s.w := by
      apply (slotPos_unique hC (Nat.mod_lt _ hC)
        (R := s.R) (j := s.w % C) (p := s.w) ?_ ?_ rfl).symm
      · exact hR
      · have hocc := h.hocc
        omega
    unfold viewCell
    rw [hpos]
    have : s.w < s.W := by omega
    simp [this]
  · right
    have hRW := h.hR_le_W
    have hR' : s.R = s.w + 1 := by omega
    have hpos : slotPos s.R (s.w % C) C = s.w + C := by
      rw [hR']
      exact slotPos_succ_self hC
    unfold viewCell
    rw [hpos]
    have : ¬ s.w + C < s.W := by omega
    simp [this]

/-- At a lagging read hint the slot is either the empty or the full cell
for `r+C`. -/
theorem helpR_cell {C limit : Nat} {s : AbsState V} (h : Inv C limit s)
    (hR : s.R = s.r + 1) (hC : 0 < C) :
    viewCell z C s (s.r % C) = fullCell (s.r + C) ((s.val (s.r + C)).getD z) ∨
    viewCell z C s (s.r % C) = emptyCell z (s.r + C) := by
  have hpos : slotPos s.R (s.r % C) C = s.r + C := by
    rw [hR]
    exact slotPos_succ_self hC
  unfold viewCell
  rw [hpos]
  by_cases hlt : s.r + C < s.W
  · left; simp [hlt]
  · right; simp [hlt]

/-! ## Refinement steps -/

/-- A cell marker strictly above `2*h` at the write-hint slot forces the
write hint to be behind the publication counter.  This is the stale-snapshot
witness used by the push help path. -/
theorem helpW_of_marker_gt {C limit : Nat} {s : AbsState V} (hi : Inv C limit s)
    (hC : 0 < C) {hint : Nat} (hle : hint ≤ s.w)
    (hmark : 2 * hint < (viewCell z C s (hint % C)).marker) :
    hint < s.W := by
  by_cases hlt : hint < s.W
  · exact hlt
  · have hWle : s.W ≤ hint := by omega
    have hhW : hint ≤ s.W := Nat.le_trans hle hi.hw_le
    have hWeq : s.W = hint := Nat.le_antisymm hWle hhW
    let p := slotPos s.R (hint % C) C
    have hpge : s.R ≤ p := slotPos_ge (R := s.R) (j := hint % C) (C := C) hC
    have hplt : p < s.R + C := slotPos_lt (R := s.R) (j := hint % C) (C := C)
      (Nat.mod_lt _ hC)
    have hpmod : p % C = hint % C := slotPos_mod (R := s.R) (j := hint % C) (C := C)
      (Nat.mod_lt _ hC)
    unfold viewCell at hmark
    by_cases hready : p < s.W
    · rw [if_pos hready] at hmark
      simp [fullCell] at hmark
      omega
    · rw [if_neg hready] at hmark
      simp [emptyCell] at hmark
      have hpgt : hint < p := by omega
      have hhlt : hint < s.R + C := by omega
      have hRleW : s.R ≤ s.W := hi.hR_le_W
      have hpeq : p = hint := by
        apply (slotPos_unique hC (Nat.mod_lt _ hC) (R := s.R) (j := hint % C)
          (p := hint) (by omega) hhlt rfl).symm
      omega

/-- A cell marker strictly above `2*h+1` at the read-hint slot forces the
read hint to be behind the consumption counter.  This is the stale-snapshot
witness used by the pop help path. -/
theorem helpR_of_marker_gt {C limit : Nat} {s : AbsState V} (hi : Inv C limit s)
    (hC : 0 < C) {hint : Nat} (hle : hint ≤ s.r)
    (hmark : 2 * hint + 1 < (viewCell z C s (hint % C)).marker) :
    hint < s.R := by
  by_cases hlt : hint < s.R
  · exact hlt
  · have hRle : s.R ≤ hint := by omega
    have hhR : hint ≤ s.R := Nat.le_trans hle hi.hr_le
    have hReq : s.R = hint := Nat.le_antisymm hRle hhR
    let p := slotPos s.R (hint % C) C
    have hpge : s.R ≤ p := slotPos_ge (R := s.R) (j := hint % C) (C := C) hC
    have hplt : p < s.R + C := slotPos_lt (R := s.R) (j := hint % C) (C := C)
      (Nat.mod_lt _ hC)
    have hpmod : p % C = hint % C := slotPos_mod (R := s.R) (j := hint % C) (C := C)
      (Nat.mod_lt _ hC)
    unfold viewCell at hmark
    by_cases hready : p < s.W
    · rw [if_pos hready] at hmark
      simp [fullCell] at hmark
      have hpgt : hint < p := by omega
      have hhlt : hint < s.R + C := by omega
      have hpeq : p = hint := by
        apply (slotPos_unique hC (Nat.mod_lt _ hC) (R := s.R) (j := hint % C)
          (p := hint) hRle hhlt rfl).symm
      omega
    · rw [if_neg hready] at hmark
      simp [emptyCell] at hmark
      have hpgt : hint < p := by omega
      have hhlt : hint < s.R + C := by omega
      have hpeq : p = hint := by
        apply (slotPos_unique hC (Nat.mod_lt _ hC) (R := s.R) (j := hint % C)
          (p := hint) hRle hhlt rfl).symm
      omega

theorem push_ref {C limit : Nat} {s : AbsState V} (h : Inv C limit s)
    (hw : s.w = s.W) (hocc : s.W - s.R < C) (hC : 0 < C)
    (m : Mem V) (hm : Ref z C s m) (v : V) :
    Ref z C (pushState s v) (m.setCell (s.W % C) (fullCell s.W v)) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [pushState, Mem.setCell] using hm.1
  · simpa [pushState, Mem.setCell] using hm.2.1
  · intro j hjC
    by_cases hj : j = s.W % C
    · subst j
      simp [Mem.setCell, viewCell_push_self h hw hocc hC v]
    · simp [Mem.setCell, hj, hm.2.2 j hjC]
      exact (viewCell_push_other h hw hocc hC v hjC hj).symm

theorem pop_ref {C limit : Nat} {s : AbsState V} (h : Inv C limit s)
    (hC : 0 < C) (m : Mem V) (hm : Ref z C s m) :
    Ref z C (popState s) (m.setCell (s.R % C) (emptyCell z (s.R + C))) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [popState, Mem.setCell] using hm.1
  · simpa [popState, Mem.setCell] using hm.2.1
  · intro j hjC
    by_cases hj : j = s.R % C
    · subst j
      simp [Mem.setCell, viewCell_pop_self h hC]
    · simp [Mem.setCell, hj, hm.2.2 j hjC]
      exact (viewCell_pop_other h hC hjC hj).symm

theorem helpW_ref {C limit : Nat} {s : AbsState V} (m : Mem V) (hm : Ref z C s m) :
    Ref z C { s with w := s.w + 1 } { m with w := s.w + 1 } := by
  refine ⟨?_, ?_, ?_⟩
  · simp [hm.1]
  · simp [hm.2.1]
  · intro j hjC
    simpa [viewCell] using hm.2.2 j hjC

theorem helpR_ref {C limit : Nat} {s : AbsState V} (m : Mem V) (hm : Ref z C s m) :
    Ref z C { s with r := s.r + 1 } { m with r := s.r + 1 } := by
  refine ⟨?_, ?_, ?_⟩
  · simp [hm.1]
  · simp [hm.2.1]
  · intro j hjC
    simpa [viewCell] using hm.2.2 j hjC

end Mpmc
