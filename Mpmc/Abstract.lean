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
  Abstract model of the MPMC queue.

  The real implementation is a ring of `C` cells.  Each cell carries a
  position marker `(position << 1) | ready`.  A push publishes at the
  position named by the write hint; a pop consumes at the position named
  by the read hint.  Both hints may lag their authoritative counters by
  one, and any participant may help advance a lagging hint.

  This file isolates the algorithm from the cell protocol.  The two
  counters `W` (published) and `R` (consumed) plus the hint pair `w`, `r`
  are the whole abstract state.  `Mpmc.View` proves that the real cells
  are a function of `(W, R, C)`, and `Mpmc.Protocol` proves that a
  successful cell CAS performs exactly one transition below.  `Mpmc.Kernel`
  is the executable kernel; its generated C is differentially tested
  against the Lean interpreter, with the printer and C compiler as trusted
  components (see `docs/proof.md`).
-/

namespace Mpmc

/-- Abstract queue state.

`W` positions `[0, W)` have been published, `R` positions `[0, R)` have
been consumed.  `w` and `r` are the published index hints, which may lag
`W` and `R` by at most one.  `val i` is the payload at live position `i`.
-/
structure AbsState (V : Type) where
  W : Nat
  R : Nat
  w : Nat
  r : Nat
  val : Nat → Option V

variable {V : Type}

/-- The abstract safety invariant.

`limit` is the publication horizon: positions `>= limit` must never be
published, which keeps the marker encoding inside 64 bits.
-/
structure Inv (C limit : Nat) (s : AbsState V) : Prop where
  hR_le_W : s.R ≤ s.W
  hocc : s.W - s.R ≤ C
  hw_le : s.w ≤ s.W
  hW_le_w : s.W ≤ s.w + 1
  hr_le : s.r ≤ s.R
  hR_le_r : s.R ≤ s.r + 1
  hlimit : s.W ≤ limit
  hval_some : ∀ i, i < s.W → ∃ v, s.val i = some v
  hval_none : ∀ i, s.W ≤ i → s.val i = none

/-- Abstract actions.  `pop` returns the value at `R`, so the action
itself needs no payload argument. -/
inductive Action (V : Type) where
  | push (v : V)
  | pop
  | helpW
  | helpR

/-- Results of an abstract action.  A push returns the position it
published at, a pop returns the position and value it consumed. -/
inductive Result (V : Type) where
  | pushed (seq : Nat)
  | popped (seq : Nat) (v : V)
  | helped

/-- One abstract transition.

A successful push requires the write hint to be current (`w = W`), space
(`W - R < C`), and a position below the horizon.  It appends a value at
`W` and advances `W`.  A successful pop requires the read hint to be
current and a published value; it advances `R`.  Help transitions move
a lagging hint forward one step.
-/
inductive Step (C limit : Nat) : AbsState V → Action V → AbsState V → Result V → Prop
  | push {s : AbsState V} {v : V}
      (hw : s.w = s.W)
      (hocc : s.W - s.R < C)
      (hlim : s.W < limit) :
      Step C limit s (.push v)
        { s with W := s.W + 1,
                 val := fun i => if i = s.W then some v else s.val i }
        (.pushed s.W)
  | pop {s : AbsState V} {v : V}
      (hr : s.r = s.R)
      (hne : s.R < s.W)
      (hval : s.val s.R = some v) :
      Step C limit s .pop { s with R := s.R + 1 } (.popped s.R v)
  | helpW {s : AbsState V}
      (h : s.W = s.w + 1) :
      Step C limit s .helpW { s with w := s.w + 1 } .helped
  | helpR {s : AbsState V}
      (h : s.R = s.r + 1) :
      Step C limit s .helpR { s with r := s.r + 1 } .helped

/-- Initial state: empty, both hints at zero. -/
def initial (V : Type) : AbsState V :=
  { W := 0, R := 0, w := 0, r := 0, val := fun _ => none }

theorem initial_inv (C limit : Nat) : Inv C limit (initial V) where
  hR_le_W := Nat.zero_le _
  hocc := by simp [initial]
  hw_le := Nat.zero_le _
  hW_le_w := Nat.zero_le _
  hr_le := Nat.zero_le _
  hR_le_r := Nat.zero_le _
  hlimit := Nat.zero_le _
  hval_some := by intro i hi; simp [initial] at hi
  hval_none := by intro i hi; simp [initial]

/-- Every abstract transition preserves the invariant. -/
theorem Inv.step {C limit : Nat} {s s' : AbsState V} {a : Action V} {r : Result V}
    (h : Inv C limit s) (hs : Step C limit s a s' r) : Inv C limit s' := by
  have hR_le_W := h.hR_le_W
  have hocc0 := h.hocc
  have hw_le := h.hw_le
  have hW_le_w := h.hW_le_w
  have hr_le := h.hr_le
  have hR_le_r := h.hR_le_r
  have hlimit := h.hlimit
  have hval_some := h.hval_some
  have hval_none := h.hval_none
  cases hs with
  | push hw hocc hlim =>
      rename_i v
      -- `s' = { s with W := s.W + 1, val := ... }`
      refine
        { hR_le_W := by dsimp; omega
          hocc := by dsimp; omega
          hw_le := by dsimp; omega
          hW_le_w := by dsimp; omega
          hr_le := by dsimp; omega
          hR_le_r := by dsimp; omega
          hlimit := by dsimp; omega
          hval_some := ?_
          hval_none := ?_ }
      · intro i hi
        dsimp at hi
        by_cases hWi : i = s.W
        · exact ⟨v, by simp [hWi]⟩
        · have hi' : i < s.W := by omega
          obtain ⟨w, hwv⟩ := hval_some i hi'
          exact ⟨w, by simp [hWi, hwv]⟩
      · intro i hi
        dsimp at hi
        have hi' : s.W ≤ i := by omega
        have hWi : i ≠ s.W := by omega
        simpa [hWi] using hval_none i hi'
  | pop hr hne hval =>
      refine
        { hR_le_W := by dsimp; omega
          hocc := by dsimp; omega
          hw_le := by dsimp; omega
          hW_le_w := by dsimp; omega
          hr_le := by dsimp; omega
          hR_le_r := by dsimp; omega
          hlimit := by dsimp; omega
          hval_some := by dsimp; exact h.hval_some
          hval_none := by dsimp; exact h.hval_none }
  | helpW _ =>
      refine
        { hR_le_W := by dsimp; exact hR_le_W
          hocc := by dsimp; exact hocc0
          hw_le := by dsimp; omega
          hW_le_w := by dsimp; omega
          hr_le := by dsimp; exact hr_le
          hR_le_r := by dsimp; exact hR_le_r
          hlimit := by dsimp; exact hlimit
          hval_some := by dsimp; exact hval_some
          hval_none := by dsimp; exact hval_none }
  | helpR _ =>
      refine
        { hR_le_W := by dsimp; exact hR_le_W
          hocc := by dsimp; exact hocc0
          hw_le := by dsimp; exact hw_le
          hW_le_w := by dsimp; exact hW_le_w
          hr_le := by dsimp; omega
          hR_le_r := by dsimp; omega
          hlimit := by dsimp; exact hlimit
          hval_some := by dsimp; exact hval_some
          hval_none := by dsimp; exact hval_none }

/-- A finite sequence of abstract transitions. -/
inductive Steps (C limit : Nat) : AbsState V → List (Action V) → AbsState V → List (Result V) → Prop
  | nil {s : AbsState V} : Steps C limit s [] s []
  | cons {s s' s'' : AbsState V} {a : Action V} {r : Result V}
      {as : List (Action V)} {rs : List (Result V)}
      (h : Step C limit s a s' r) (hs : Steps C limit s' as s'' rs) :
      Steps C limit s (a :: as) s'' (r :: rs)

theorem Steps.inv {C limit : Nat} {s s' : AbsState V} {as : List (Action V)}
    {rs : List (Result V)} (h : Inv C limit s) (hs : Steps C limit s as s' rs) :
    Inv C limit s' := by
  induction hs with
  | nil => exact h
  | cons hstep _ ih => exact ih (h.step hstep)

/-! ## Trace labels

The sequence numbers returned by a run are the numbers `0, 1, ...` in
order.  This is the operational content of FIFO and linearizability.
-/

/-- Sequence numbers of successful pushes in a result list, in order. -/
def pushLabels (rs : List (Result V)) : List Nat :=
  rs.filterMap fun
    | .pushed n => some n
    | _ => none

/-- Sequence numbers of successful pops in a result list, in order. -/
def popLabels (rs : List (Result V)) : List Nat :=
  rs.filterMap fun
    | .popped n _ => some n
    | _ => none

/-- The values returned by successful pops, in order. -/
def popValues (rs : List (Result V)) : List V :=
  rs.filterMap fun
    | .popped _ v => some v
    | _ => none

/-- The write counter never moves backwards. -/
theorem Step.W_mono {C limit : Nat} {s s' : AbsState V} {a : Action V} {r : Result V}
    (h : Step C limit s a s' r) : s.W ≤ s'.W := by
  cases h <;> dsimp <;> omega

/-- The read counter never moves backwards. -/
theorem Step.R_mono {C limit : Nat} {s s' : AbsState V} {a : Action V} {r : Result V}
    (h : Step C limit s a s' r) : s.R ≤ s'.R := by
  cases h <;> dsimp <;> omega

theorem Steps.W_mono {C limit : Nat} {s s' : AbsState V}
    {as : List (Action V)} {rs : List (Result V)}
    (hs : Steps C limit s as s' rs) : s.W ≤ s'.W := by
  induction hs with
  | nil => exact Nat.le_refl _
  | cons hstep _ ih => exact Nat.le_trans hstep.W_mono ih

theorem Steps.R_mono {C limit : Nat} {s s' : AbsState V}
    {as : List (Action V)} {rs : List (Result V)}
    (hs : Steps C limit s as s' rs) : s.R ≤ s'.R := by
  induction hs with
  | nil => exact Nat.le_refl _
  | cons hstep _ ih => exact Nat.le_trans hstep.R_mono ih

/-- A push transition returns the old `W`. -/
theorem Step.push_label {C limit : Nat} {s s' : AbsState V} {v : V} {r : Result V}
    (h : Step C limit s (.push v) s' r) : r = .pushed s.W := by
  cases h with
  | push => rfl

/-- A pop transition returns the old `R` and the value stored there. -/
theorem Step.pop_label {C limit : Nat} {s s' : AbsState V} {r : Result V}
    (h : Step C limit s .pop s' r) :
    ∃ v, r = .popped s.R v ∧ s.val s.R = some v := by
  cases h with
  | pop hr hne hval => exact ⟨_, rfl, hval⟩

/-- Push labels from a run starting at `s0` are `s0.W, s0.W+1, ...`. -/
theorem pushLabels_eq_range' {C limit : Nat} {s0 sf : AbsState V}
    {as : List (Action V)} {rs : List (Result V)}
    (hs : Steps C limit s0 as sf rs) :
    pushLabels rs = List.range' s0.W (sf.W - s0.W) := by
  induction hs with
  | nil => simp [pushLabels]
  | cons hstep htail ih =>
      rename_i s0' s1' sf' act res as' rs'
      cases hstep with
      | push =>
          simp only [pushLabels, List.filterMap_cons]
          change s0'.W :: pushLabels rs' = List.range' s0'.W (sf'.W - s0'.W)
          rw [ih]
          dsimp only
          have hmono : s0'.W + 1 ≤ sf'.W := htail.W_mono
          have hsub : sf'.W - s0'.W = (sf'.W - (s0'.W + 1)) + 1 := by omega
          rw [hsub]
          simp [List.range']
      | pop =>
          simp only [pushLabels, List.filterMap_cons]
          change pushLabels rs' = List.range' s0'.W (sf'.W - s0'.W)
          rw [ih]
      | helpW =>
          simp only [pushLabels, List.filterMap_cons]
          change pushLabels rs' = List.range' s0'.W (sf'.W - s0'.W)
          rw [ih]
      | helpR =>
          simp only [pushLabels, List.filterMap_cons]
          change pushLabels rs' = List.range' s0'.W (sf'.W - s0'.W)
          rw [ih]

/-- Pop labels from a run starting at `s0` are `s0.R, s0.R+1, ...`. -/
theorem popLabels_eq_range' {C limit : Nat} {s0 sf : AbsState V}
    {as : List (Action V)} {rs : List (Result V)}
    (hs : Steps C limit s0 as sf rs) :
    popLabels rs = List.range' s0.R (sf.R - s0.R) := by
  induction hs with
  | nil => simp [popLabels]
  | cons hstep htail ih =>
      rename_i s0' s1' sf' act res as' rs'
      cases hstep with
      | push =>
          simp only [popLabels, List.filterMap_cons]
          change popLabels rs' = List.range' s0'.R (sf'.R - s0'.R)
          rw [ih]
      | pop =>
          simp only [popLabels, List.filterMap_cons]
          change s0'.R :: popLabels rs' = List.range' s0'.R (sf'.R - s0'.R)
          rw [ih]
          dsimp only
          have hmono : s0'.R + 1 ≤ sf'.R := htail.R_mono
          have hsub : sf'.R - s0'.R = (sf'.R - (s0'.R + 1)) + 1 := by omega
          rw [hsub]
          simp [List.range']
      | helpW =>
          simp only [popLabels, List.filterMap_cons]
          change popLabels rs' = List.range' s0'.R (sf'.R - s0'.R)
          rw [ih]
      | helpR =>
          simp only [popLabels, List.filterMap_cons]
          change popLabels rs' = List.range' s0'.R (sf'.R - s0'.R)
          rw [ih]

end Mpmc
