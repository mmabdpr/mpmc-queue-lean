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
  Slot view: what every cell must contain, as a function of the abstract
  counters `(W, R)` and the capacity `C`.

  A slot `j` owns the positions `j, j+C, j+2C, ...`.  The cell in slot
  `j` always describes the first such position at or after `R`; that
  position is published exactly when it is below `W`.
-/

import Mpmc.Abstract

namespace Mpmc

/-- Number of laps of slot `j` completed before `R`. -/
def slotQ (R j C : Nat) : Nat :=
  (R + C - 1 - j) / C

/-- The first position `>= R` whose slot is `j`. -/
def slotPos (R j C : Nat) : Nat :=
  j + slotQ R j C * C

/-- `slotPos` is in the slot it names. -/
theorem slotPos_mod {R j C : Nat} (hj : j < C) :
    slotPos R j C % C = j := by
  unfold slotPos slotQ
  rw [Nat.mul_comm]
  rw [Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt hj

/-- `slotPos` is at or after `R`. -/
theorem slotPos_ge {R j C : Nat} (hC : 0 < C) : R ≤ slotPos R j C := by
  unfold slotPos
  have h1 : slotQ R j C * C ≤ R + C - 1 - j := by
    unfold slotQ
    exact Nat.div_mul_le_self _ _
  have h2 : R + C - 1 - j < (slotQ R j C + 1) * C := by
    unfold slotQ
    exact (Nat.div_lt_iff_lt_mul hC).1 (Nat.lt_succ_self _)
  have h2' : R + C - 1 - j < slotQ R j C * C + C := by
    simpa [Nat.add_mul] using h2
  omega

/-- `slotPos` is below `R + C`. -/
theorem slotPos_lt {R j C : Nat} (hj : j < C) :
    slotPos R j C < R + C := by
  unfold slotPos
  have h1 : slotQ R j C * C ≤ R + C - 1 - j := by
    unfold slotQ
    exact Nat.div_mul_le_self _ _
  omega

/-- There is exactly one representative of slot `j` in `[R, R+C)`. -/
theorem slotPos_unique {R j C p : Nat} (hC : 0 < C) (_hj : j < C)
    (hR : R ≤ p) (hp : p < R + C) (hmod : p % C = j) :
    p = slotPos R j C := by
  have hsp : slotPos R j C = j + slotQ R j C * C := rfl
  have hp_decomp : p = j + (p / C) * C := by
    have h := Nat.div_add_mod p C
    rw [hmod] at h
    rw [Nat.mul_comm C (p / C)] at h
    omega
  -- `slotQ` is the least `k` with `j + k*C >= R`.
  have hq_le : slotQ R j C ≤ p / C := by
    by_cases hq0 : slotQ R j C = 0
    · rw [hq0]; exact Nat.zero_le _
    · by_cases hle : slotQ R j C ≤ p / C
      · exact hle
      · have hk1 : p / C + 1 ≤ slotQ R j C := by omega
        have hmul : (p / C + 1) * C ≤ slotQ R j C * C :=
          Nat.mul_le_mul_right C hk1
        have hmul' : (p / C) * C + C ≤ slotQ R j C * C := by
          simpa [Nat.add_mul] using hmul
        have h1 : slotQ R j C * C ≤ R + C - 1 - j := by
          unfold slotQ
          exact Nat.div_mul_le_self _ _
        omega
  -- `p < slotPos + C` because `slotPos >= R`.
  have hsp_ge : R ≤ slotPos R j C := slotPos_ge hC
  have hlt : p < slotPos R j C + C := by omega
  have hk_lt : p / C < slotQ R j C + 1 := by
    apply Nat.lt_of_mul_lt_mul_right (a := C)
    have hqC : (slotQ R j C + 1) * C = slotQ R j C * C + C := by
      rw [Nat.add_mul]; simp
    rw [hqC]
    omega
  have hk_eq : p / C = slotQ R j C := by omega
  rw [hk_eq] at hp_decomp
  omega

end Mpmc
