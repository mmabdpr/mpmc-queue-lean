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
  Kernel refinement: the generated imperative kernel implements the
  abstract queue machine of `Mpmc.Abstract`.

  `KRef` relates a kernel machine state to an abstract state and the
  abstract cell view.  The theorems below are the bridge between the
  proved protocol (`Mpmc.Protocol`) and the executable kernel that
  `Mpmc.Codegen` prints as C.

  The kernel programs use `UInt64` arithmetic.  The refinement theorems
  therefore carry the same horizon bound as the C implementation:
  `limit + C <= 2^63`, so markers and positions never wrap.
-/

import Mpmc.Protocol
import Mpmc.Kernel

namespace Mpmc

open Mpmc.Kernel

set_option maxHeartbeats 2000000

/-- Interpret a kernel cell as an abstract cell. -/
def kcellToCell (c : KCell) : Cell UInt64 :=
  ⟨c.marker.toNat, c.payload⟩

/-- Project a kernel machine state onto the abstract shared memory. -/
def toMem (st : MState) : Mem UInt64 :=
  { w := st.hintW.toNat
    r := st.hintR.toNat
    cells := fun j => kcellToCell (st.cells j) }

/-- Kernel/abstract refinement relation.

The parameters agree with `C` and `limit`, the hints agree, and every
slot of the kernel cell array is the abstract view.  `C` is a power of
two in the executable; the proofs only need `0 < C` and the mask
identity, so `hCpow` records `C = 2^k`.
-/
structure KRef (C limit : Nat) (s : AbsState UInt64) (st : MState) : Prop where
  hcap : st.params.capacity.toNat = C
  hmask : st.params.mask.toNat = C - 1
  hlimit : st.params.limit.toNat = limit
  hw : st.hintW.toNat = s.w
  hr : st.hintR.toNat = s.r
  hcells : ∀ j, j < C → kcellToCell (st.cells j) = viewCell 0 C s j

theorem KRef.ref {C limit : Nat} {s : AbsState UInt64} {st : MState}
    (h : KRef C limit s st) : Ref 0 C s (toMem st) :=
  ⟨h.hw, h.hr, h.hcells⟩

/-- The write slot index computed by the kernel is the abstract slot. -/
theorem KRef.slot {C limit k : Nat} {s : AbsState UInt64} {st : MState}
    (h : KRef C limit s st) (hCpow : C = 2 ^ k) (hw : s.w = s.W) :
    (st.hintW &&& st.params.mask).toNat = s.W % C := by
  rw [UInt64.toNat_and, h.hw, h.hmask, hw]
  have hC1 : C - 1 = 2 ^ k - 1 := by omega
  rw [hC1, Nat.and_two_pow_sub_one_eq_mod, hCpow]

/-- The read slot index computed by the kernel is the abstract slot. -/
theorem KRef.rslot {C limit k : Nat} {s : AbsState UInt64} {st : MState}
    (h : KRef C limit s st) (hCpow : C = 2 ^ k) (hr : s.r = s.R) :
    (st.hintR &&& st.params.mask).toNat = s.R % C := by
  rw [UInt64.toNat_and, h.hr, h.hmask, hr]
  have hC1 : C - 1 = 2 ^ k - 1 := by omega
  rw [hC1, Nat.and_two_pow_sub_one_eq_mod, hCpow]

/-- The write slot index computed by the kernel is the abstract slot. -/
theorem KRef.hintSlotW {C limit k : Nat} {s : AbsState UInt64} {st : MState}
    (h : KRef C limit s st) (hCpow : C = 2 ^ k) :
    (st.hintW &&& st.params.mask).toNat = s.w % C := by
  rw [UInt64.toNat_and, h.hw, h.hmask]
  have hC1 : C - 1 = 2 ^ k - 1 := by omega
  rw [hC1, Nat.and_two_pow_sub_one_eq_mod, hCpow]

/-- The read slot index computed by the kernel is the abstract slot. -/
theorem KRef.hintSlotR {C limit k : Nat} {s : AbsState UInt64} {st : MState}
    (h : KRef C limit s st) (hCpow : C = 2 ^ k) :
    (st.hintR &&& st.params.mask).toNat = s.r % C := by
  rw [UInt64.toNat_and, h.hr, h.hmask]
  have hC1 : C - 1 = 2 ^ k - 1 := by omega
  rw [hC1, Nat.and_two_pow_sub_one_eq_mod, hCpow]

/-- At a current write hint with space, the slot is the empty cell for `W`. -/
theorem KRef.push_cell {C limit : Nat} {s : AbsState UInt64} {st : MState}
    (h : KRef C limit s st) (hi : Inv C limit s)
    (hC : 0 < C) (hw : s.w = s.W) (hocc : s.W - s.R < C) :
    kcellToCell (st.cells (s.W % C)) = emptyCell 0 s.W := by
  rw [h.hcells (s.W % C) (Nat.mod_lt _ hC)]
  rw [viewCell_not_ready]
  · rw [slotPos_push hi hw hocc hC]
  · rw [slotPos_push hi hw hocc hC]
    omega

/-- At a current read hint with a published value, the slot is the full
cell for `R`. -/
theorem KRef.pop_cell {C limit : Nat} {s : AbsState UInt64} {st : MState}
    (h : KRef C limit s st) (hi : Inv C limit s)
    (hC : 0 < C) (hne : s.R < s.W) :
    kcellToCell (st.cells (s.R % C)) = fullCell s.R ((s.val s.R).getD 0) := by
  rw [h.hcells (s.R % C) (Nat.mod_lt _ hC)]
  rw [viewCell_ready_cell]
  · rw [slotPos_self hC]
  · rw [slotPos_self hC]
    exact hne

/-- At a current write hint with a full queue, the slot is the full cell
for `W - C`. -/
theorem KRef.push_cell_full {C limit : Nat} {s : AbsState UInt64} {st : MState}
    (h : KRef C limit s st) (hi : Inv C limit s)
    (hC : 0 < C) (hfull : s.W - s.R = C) :
    kcellToCell (st.cells (s.W % C)) =
      fullCell (s.W - C) ((s.val (s.W - C)).getD 0) := by
  rw [h.hcells (s.W % C) (Nat.mod_lt _ hC)]
  rw [viewCell_ready_cell]
  · rw [slotPos_push_full hi hfull hC]
  · rw [slotPos_push_full hi hfull hC]
    omega

/-- At a current read hint with an empty queue, the slot is the empty
cell for `R`. -/
theorem KRef.pop_cell_empty {C limit : Nat} {s : AbsState UInt64} {st : MState}
    (h : KRef C limit s st) (hi : Inv C limit s)
    (hC : 0 < C) (hempty : s.R = s.W) :
    kcellToCell (st.cells (s.R % C)) = emptyCell 0 s.R := by
  rw [h.hcells (s.R % C) (Nat.mod_lt _ hC)]
  rw [viewCell_not_ready]
  · rw [slotPos_self hC]
  · rw [slotPos_self hC, hempty]
    omega

/-- Extensionality for `Mem` (no Mathlib). -/
theorem Mem.ext' {V : Type} {m1 m2 : Mem V}
    (h1 : m1.w = m2.w) (h2 : m1.r = m2.r)
    (h3 : ∀ j, m1.cells j = m2.cells j) : m1 = m2 := by
  cases m1; cases m2; simp_all
  exact funext h3

/-- `(x <<< 1) + 1` as a natural number, without wrap. -/
theorem marker_toNat (x : UInt64) (hx : x.toNat < 2 ^ 63) :
    (((x <<< 1) + 1).toNat) = 2 * x.toNat + 1 := by
  rw [UInt64.toNat_add, UInt64.toNat_shiftLeft]
  have h1 : (1 : UInt64).toNat = 1 := rfl
  rw [h1]
  have hmod : 1 % 64 = 1 := by decide
  rw [hmod, Nat.shiftLeft_eq]
  have hx2 : x.toNat * 2 < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt hx2]
  have hsum : x.toNat * 2 + 1 < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt hsum]
  omega

/-- `x + 1` as a natural number, without wrap. -/
theorem add_one_toNat (x : UInt64) (hx : x.toNat < 2 ^ 63) :
    (x + 1).toNat = x.toNat + 1 := by
  rw [UInt64.toNat_add]
  have h1 : (1 : UInt64).toNat = 1 := rfl
  rw [h1]
  have hsum : x.toNat + 1 < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt hsum]

/-- A successful push refines the abstract push followed by the hint
advance.  The result state has `w = W + 1`; the abstract `pushState`
updates `W` and `val`. -/
theorem push_success {C limit k : Nat} {s : AbsState UInt64} {st : MState}
    (hi : Inv C limit s) (hk : KRef C limit s st)
    (hC : 0 < C) (hCpow : C = 2 ^ k) (hbound : limit < 2 ^ 63)
    (hw : s.w = s.W) (hocc : s.W - s.R < C) (hlim : s.W < limit) :
    ∃ st', run 5 pushProgram 0 st = .returned 0 st' ∧
      st'.hintW.toNat = s.w + 1 ∧
      st'.hintR = st.hintR ∧
      (∀ j, j < C →
        kcellToCell (st'.cells j) = viewCell 0 C (pushState s st.params.value) j) ∧
      st'.out0.toNat = s.W := by
  let slot : UInt64 := st.hintW &&& st.params.mask
  let c : KCell := st.cells (s.W % C)
  let st0 : MState := { st with regs := upd st.regs rHint st.hintW }
  let st1 : MState :=
    { st0 with
      regs := upd (upd (upd (upd st0.regs rSlot slot) rMarker c.marker)
        rPayload c.payload) rPos (c.marker >>> 1) }
  let st2 : MState :=
    { st1 with regs := upd st1.regs rTmp0 (c.marker &&& 1) }
  let desired : KCell := ⟨(st.hintW <<< 1) + 1, st.params.value⟩
  let st3a : MState :=
    { st2 with
      regs := upd (upd st2.regs rTmp0 ((st.hintW <<< 1) + 1))
        rTmp1 st.params.value }
  let st3 : MState :=
    { st3a with
      cells := upd st3a.cells slot.toNat desired,
      regs := upd st3a.regs rOk 1 }
  let nxt : UInt64 := st.hintW + 1
  let st4 : MState :=
    { st3 with
      out0 := st.hintW
      hintW := nxt
      regs := upd (upd st3.regs rTmp2 nxt) rOk 1 }
  have hslot : slot.toNat = s.W % C := hk.slot hCpow hw
  have hview : kcellToCell c = emptyCell 0 s.W := hk.push_cell hi hC hw hocc
  have hmarker : c.marker.toNat = 2 * s.W := by
    have := congrArg Cell.marker hview
    simpa [kcellToCell, emptyCell] using this
  have hpayload : c.payload = 0 := by
    have := congrArg Cell.payload hview
    simpa [kcellToCell, emptyCell] using this
  have hpos : (c.marker >>> 1) = st.hintW := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_shiftRight, hmarker, hk.hw, hw]
    have h1 : (1 : UInt64).toNat = 1 := rfl
    rw [h1]
    have hmod : 1 % 64 = 1 := by decide
    rw [hmod, Nat.shiftRight_eq_div_pow]
    simp only [Nat.reducePow]
    exact Nat.mul_div_right s.W (by decide : 0 < 2)
  have hready : (c.marker &&& 1) = 0 := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_and, hmarker]
    simp
  have hlt : st.hintW < st.params.limit := by
    rw [UInt64.lt_iff_toNat_lt, hk.hw, hk.hlimit, hw]
    exact hlim
  have h0 : step pushProgram 0 st = .running 1 st0 := by
    simp [step, pushProgram, execOps, execOp, eval, rHint, st0, hlt]
  have h1 : step pushProgram 1 st0 = .running 2 st1 := by
    simp [step, pushProgram, execOps, execOp, eval, rHint, rSlot, rMarker,
      rPayload, rPos, rTmp0, rTmp1, rOk, rTmp2, upd, st0, st1, slot, c, hslot, hpos]
  have h2 : step pushProgram 2 st1 = .running 3 st2 := by
    simp [step, pushProgram, execOps, execOp, eval, rHint, rSlot, rMarker,
      rPayload, rPos, rTmp0, rTmp1, rOk, rTmp2, upd, st0, st1, st2, c, hready]
  have hcas : st.cells (st.hintW.toNat &&& st.params.mask.toNat) =
      ({ marker := (st.cells (s.W % C)).marker,
         payload := (st.cells (s.W % C)).payload } : KCell) := by
    rw [← UInt64.toNat_and, ← hslot]
  have h3 : step pushProgram 3 st2 = .running 4 st3 := by
    simp [step, pushProgram, execOps, execOp, eval, rHint, rSlot, rMarker,
      rPayload, rPos, rTmp0, rTmp1, rOk, rTmp2, upd, st0, st1, st2, st3,
      st3a, desired, slot, c, hcas]
  have hhint : st3.hintW = st.hintW := by
    simp [st3, st3a, st2, st1, st0]
  have h4 : step pushProgram 4 st3 = .returned 0 st4 := by
    simp [step, pushProgram, execOps, execOp, eval, rHint, rSlot, rMarker,
      rPayload, rPos, rTmp0, rTmp1, rOk, rTmp2, upd, st0, st1, st2, st3,
      st3a, st4, nxt, hhint]
  refine ⟨st4, ?_, ?_, ?_, ?_, ?_⟩
  · calc run 5 pushProgram 0 st
      = run 4 pushProgram 1 st0 := by simp [run, h0]
      _ = run 3 pushProgram 2 st1 := by simp [run, h1]
      _ = run 2 pushProgram 3 st2 := by simp [run, h2]
      _ = run 1 pushProgram 4 st3 := by simp [run, h3]
      _ = .returned 0 st4 := by simp [run, h4]
  · -- hint advance
    simp only [st4, nxt]
    rw [UInt64.toNat_add, hk.hw]
    have hlt64 : s.w + 1 < 2 ^ 64 := by
      have : s.w < 2 ^ 63 := by omega
      omega
    have h1u : (1 : UInt64).toNat = 1 := rfl
    rw [h1u, Nat.mod_eq_of_lt hlt64]
  · -- read hint unchanged
    simp [st4, st3, st3a, st2, st1, st0]
  · -- cell view after the push and hint advance
    let m0 : Mem UInt64 := toMem st
    let m3 : Mem UInt64 := toMem st3
    let m4 : Mem UInt64 := toMem st4
    have hm3 : m3 = m0.setCell slot.toNat (fullCell s.W st.params.value) := by
      apply Mem.ext'
      · simp [m3, m0, toMem, st3, st3a, st2, st1, st0, Mem.setCell]
      · simp [m3, m0, toMem, st3, st3a, st2, st1, st0, Mem.setCell]
      · intro j
        by_cases hj : j = slot.toNat
        · subst j
          simp [m3, m0, toMem, st3, st3a, st2, st1, st0, Mem.setCell,
            desired, kcellToCell, fullCell, hmarker, hpayload, hk.hw, hw,
            hslot]
          rw [Nat.shiftLeft_eq]
          have h2 : s.W * 2 + 1 < 2 ^ 64 := by
            have : s.W < 2 ^ 63 := by omega
            omega
          rw [Nat.mod_eq_of_lt h2]
          omega
        · have hj' : j ≠ s.W % C := by
            rw [← hslot]; exact hj
          simp [m3, m0, toMem, st3, st3a, st2, st1, st0, Mem.setCell, hj',
            hslot]
    have hpr : Ref 0 C (pushState s st.params.value) m3 := by
      simpa [m0, hm3, hslot] using
        push_ref (z := (0 : UInt64)) hi hw hocc hC m0 (hk.ref) st.params.value
    have hm4 : m4 = { m3 with w := s.w + 1 } := by
      apply Mem.ext'
      · simp [m4, m3, toMem, st4, st3, st3a, st2, st1, st0]
        rw [add_one_toNat]
        · rw [hk.hw]
        · rw [hk.hw]; omega
      · simp [m4, m3, toMem, st4, st3, st3a, st2, st1, st0]
      · intro j; rfl
    have hhr : Ref 0 C { pushState s st.params.value with w := s.w + 1 } m4 := by
      simpa [hm4, pushState] using
        helpW_ref (limit := limit) (z := (0 : UInt64)) (s := pushState s st.params.value) (m := m3) hpr
    simpa [m4, toMem, pushState, viewCell] using hhr.2.2
  · -- published sequence
    simp [st4, st3, st3a, st2, st1, st0, hk.hw, hw]

/-- A successful pop refines the abstract pop followed by the read-hint
advance.  The result state has `r = R + 1`; the abstract `popState`
updates `R`. -/
theorem pop_success {C limit k : Nat} {s : AbsState UInt64} {st : MState}
    (hi : Inv C limit s) (hk : KRef C limit s st)
    (hC : 0 < C) (hCpow : C = 2 ^ k) (hbound : limit < 2 ^ 63)
    (hCmax : C ≤ 2 ^ 24) (hlimitC : limit + C ≤ 2 ^ 63)
    (hr : s.r = s.R) (hne : s.R < s.W) (hlim : s.R < limit) :
    ∃ st', run 5 popProgram 0 st = .returned 0 st' ∧
      st'.hintR.toNat = s.r + 1 ∧
      st'.hintW = st.hintW ∧
      (∀ j, j < C →
        kcellToCell (st'.cells j) = viewCell 0 C (popState s) j) ∧
      st'.out0 = (s.val s.R).getD 0 ∧
      st'.out1.toNat = s.R := by
  let slot : UInt64 := st.hintR &&& st.params.mask
  let c : KCell := st.cells (s.R % C)
  let st0 : MState := { st with regs := upd st.regs rHint st.hintR }
  let st1 : MState :=
    { st0 with
      regs := upd (upd (upd (upd st0.regs rSlot slot) rMarker c.marker)
        rPayload c.payload) rPos (c.marker >>> 1) }
  let st2 : MState :=
    { st1 with regs := upd st1.regs rTmp0 (c.marker &&& 1) }
  let desired : KCell := ⟨(st.hintR + st.params.capacity) <<< 1, 0⟩
  let st3a : MState :=
    { st2 with
      regs := upd (upd st2.regs rTmp0 (((st.hintR + st.params.capacity) <<< 1)))
        rTmp1 0 }
  let st3 : MState :=
    { st3a with
      cells := upd st3a.cells slot.toNat desired,
      regs := upd st3a.regs rOk 1 }
  let nxt : UInt64 := st.hintR + 1
  let st4 : MState :=
    { st3 with
      out0 := c.payload
      out1 := st.hintR
      hintR := nxt
      regs := upd (upd st3.regs rTmp2 nxt) rOk 1 }
  have hslot : slot.toNat = s.R % C := hk.rslot hCpow hr
  have hview : kcellToCell c = fullCell s.R ((s.val s.R).getD 0) := hk.pop_cell hi hC hne
  have hmarker : c.marker.toNat = 2 * s.R + 1 := by
    have := congrArg Cell.marker hview
    simpa [kcellToCell, fullCell] using this
  have hpayload : c.payload = (s.val s.R).getD 0 := by
    have := congrArg Cell.payload hview
    exact this
  have hpos : (c.marker >>> 1) = st.hintR := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_shiftRight, hmarker, hk.hr, hr]
    have h1 : (1 : UInt64).toNat = 1 := rfl
    rw [h1]
    have hmod : 1 % 64 = 1 := by decide
    rw [hmod, Nat.shiftRight_eq_div_pow]
    simp only [Nat.reducePow]
    omega
  have hready : (c.marker &&& 1) = 1 := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_and, hmarker]
    simp
  have hlt : st.hintR < st.params.limit := by
    rw [UInt64.lt_iff_toNat_lt, hk.hr, hk.hlimit, hr]
    exact hlim
  have h0 : step popProgram 0 st = .running 1 st0 := by
    simp [step, popProgram, execOps, execOp, eval, rHint, st0, hlt]
  have h1 : step popProgram 1 st0 = .running 2 st1 := by
    simp [step, popProgram, execOps, execOp, eval, rHint, rSlot, rMarker,
      rPayload, rPos, rTmp0, rTmp1, rOk, rTmp2, upd, st0, st1, slot, c, hslot, hpos]
  have h2 : step popProgram 2 st1 = .running 7 st2 := by
    simp [step, popProgram, execOps, execOp, eval, rHint, rSlot, rMarker,
      rPayload, rPos, rTmp0, rTmp1, rOk, rTmp2, upd, st0, st1, st2, c, hready]
  have hcas : st.cells (st.hintR.toNat &&& st.params.mask.toNat) =
      ({ marker := (st.cells (s.R % C)).marker,
         payload := (st.cells (s.R % C)).payload } : KCell) := by
    rw [← UInt64.toNat_and, ← hslot]
  have h3 : step popProgram 7 st2 = .running 4 st3 := by
    simp [step, popProgram, execOps, execOp, eval, rHint, rSlot, rMarker,
      rPayload, rPos, rTmp0, rTmp1, rOk, rTmp2, upd, st0, st1, st2, st3,
      st3a, desired, slot, c, hcas]
  have hhint : st3.hintR = st.hintR := by
    simp [st3, st3a, st2, st1, st0]
  have h4 : step popProgram 4 st3 = .returned 0 st4 := by
    simp [step, popProgram, execOps, execOp, eval, rHint, rSlot, rMarker,
      rPayload, rPos, rTmp0, rTmp1, rOk, rTmp2, upd, st0, st1, st2, st3,
      st3a, st4, nxt, hhint]
  refine ⟨st4, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc run 5 popProgram 0 st
      = run 4 popProgram 1 st0 := by simp [run, h0]
      _ = run 3 popProgram 2 st1 := by simp [run, h1]
      _ = run 2 popProgram 7 st2 := by simp [run, h2]
      _ = run 1 popProgram 4 st3 := by simp [run, h3]
      _ = .returned 0 st4 := by simp [run, h4]
  · -- read hint advance
    simp only [st4, nxt]
    rw [UInt64.toNat_add, hk.hr]
    have hlt64 : s.r + 1 < 2 ^ 64 := by
      have : s.r < 2 ^ 63 := by omega
      omega
    have h1u : (1 : UInt64).toNat = 1 := rfl
    rw [h1u, Nat.mod_eq_of_lt hlt64]
  · -- write hint unchanged
    simp [st4, st3, st3a, st2, st1, st0]
  · -- cell view after the pop and hint advance
    let m0 : Mem UInt64 := toMem st
    let m3 : Mem UInt64 := toMem st3
    let m4 : Mem UInt64 := toMem st4
    have hm3 : m3 = m0.setCell slot.toNat (emptyCell 0 (s.R + C)) := by
      apply Mem.ext'
      · simp [m3, m0, toMem, st3, st3a, st2, st1, st0, Mem.setCell]
      · simp [m3, m0, toMem, st3, st3a, st2, st1, st0, Mem.setCell]
      · intro j
        by_cases hj : j = slot.toNat
        · subst j
          simp [m3, m0, toMem, st3, st3a, st2, st1, st0, Mem.setCell,
            desired, kcellToCell, emptyCell, hk.hr, hk.hcap, hslot, hr]
          rw [Nat.shiftLeft_eq]
          have hxc : s.R + C < 2 ^ 64 := by omega
          rw [Nat.mod_eq_of_lt hxc]
          have h2 : (s.R + C) * 2 < 2 ^ 64 := by omega
          rw [Nat.mod_eq_of_lt h2]
          omega
        · have hj' : j ≠ s.R % C := by
            rw [← hslot]; exact hj
          simp [m3, m0, toMem, st3, st3a, st2, st1, st0, Mem.setCell, hj',
            hslot]
    have hpr : Ref 0 C (popState s) m3 := by
      simpa [m0, hm3, hslot] using
        pop_ref (z := (0 : UInt64)) hi hC m0 (hk.ref)
    have hm4 : m4 = { m3 with r := s.r + 1 } := by
      apply Mem.ext'
      · simp [m4, m3, toMem, st4, st3, st3a, st2, st1, st0]
      · simp [m4, m3, toMem, st4, st3, st3a, st2, st1, st0]
        rw [add_one_toNat]
        · rw [hk.hr]
        · rw [hk.hr]; omega
      · intro j; rfl
    have hhr : Ref 0 C { popState s with r := s.r + 1 } m4 := by
      simpa [hm4, popState] using
        helpR_ref (limit := limit) (z := (0 : UInt64)) (s := popState s) (m := m3) hpr
    simpa [m4, toMem, popState, viewCell] using hhr.2.2
  · -- payload output
    simp [st4, st3, st3a, st2, st1, st0, hpayload]
  · -- consumed sequence output
    simp [st4, st3, st3a, st2, st1, st0, hk.hr, hr]

/-- The lagging write-hint case where the slot still carries the full
cell for `w`: the kernel helps the hint forward and loops. -/
theorem push_help_full {C limit k : Nat} {s : AbsState UInt64} {st : MState}
    {p : UInt64}
    (hi : Inv C limit s) (hk : KRef C limit s st)
    (hC : 0 < C) (hCpow : C = 2 ^ k) (hbound : limit < 2 ^ 63)
    (hW : s.W = s.w + 1)
    (hview : kcellToCell (st.cells (s.w % C)) = fullCell s.w p) :
    ∃ st', run 4 pushProgram 0 st = .running 0 st' ∧
      KRef C limit { s with w := s.w + 1 } st' ∧
      st'.hintW.toNat = s.w + 1 ∧ st'.hintR = st.hintR := by
  let slot : UInt64 := st.hintW &&& st.params.mask
  let c : KCell := st.cells (s.w % C)
  let st0 : MState := { st with regs := upd st.regs rHint st.hintW }
  let st1 : MState :=
    { st0 with
      regs := upd (upd (upd (upd st0.regs rSlot slot) rMarker c.marker)
        rPayload c.payload) rPos (c.marker >>> 1) }
  let st2 : MState :=
    { st1 with regs := upd st1.regs rTmp0 (c.marker &&& 1) }
  let nxt : UInt64 := st.hintW + 1
  let st3 : MState :=
    { st2 with
      hintW := nxt
      regs := upd (upd st2.regs rTmp2 nxt) rOk 1 }
  have hslot : slot.toNat = s.w % C := hk.hintSlotW hCpow
  have hmarker : c.marker.toNat = 2 * s.w + 1 := by
    have := congrArg Cell.marker hview
    simpa [kcellToCell, fullCell] using this
  have hpos : (c.marker >>> 1) = st.hintW := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_shiftRight, hmarker, hk.hw]
    have h1 : (1 : UInt64).toNat = 1 := rfl
    rw [h1]
    have hmod : 1 % 64 = 1 := by decide
    rw [hmod, Nat.shiftRight_eq_div_pow]
    simp only [Nat.reducePow]
    omega
  have hready : (c.marker &&& 1) = 1 := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_and, hmarker]
    simp
  have hWh : s.w + 1 ≤ limit := by
    rw [← hW]; exact hi.hlimit
  have hlt : st.hintW < st.params.limit := by
    rw [UInt64.lt_iff_toNat_lt, hk.hw, hk.hlimit]
    omega
  have h0 : step pushProgram 0 st = .running 1 st0 := by
    simp [step, pushProgram, execOps, execOp, eval, rHint, st0, hlt]
  have h1 : step pushProgram 1 st0 = .running 2 st1 := by
    simp [step, pushProgram, execOps, execOp, eval, rHint, rSlot, rMarker,
      rPayload, rPos, rTmp0, rTmp1, rOk, rTmp2, upd, st0, st1, slot, c,
      hslot, hpos]
  have h2 : step pushProgram 2 st1 = .running 7 st2 := by
    simp [step, pushProgram, execOps, execOp, eval, rHint, rSlot, rMarker,
      rPayload, rPos, rTmp0, rTmp1, rOk, rTmp2, upd, st0, st1, st2, c,
      hready]
  have h3 : step pushProgram 7 st2 = .running 0 st3 := by
    simp [step, pushProgram, execOps, execOp, eval, rHint, rSlot, rMarker,
      rPayload, rPos, rTmp0, rTmp1, rOk, rTmp2, upd, st0, st1, st2, st3,
      nxt]
  refine ⟨st3, ?_, ?_, ?_, ?_⟩
  · calc run 4 pushProgram 0 st
      = run 3 pushProgram 1 st0 := by simp [run, h0]
      _ = run 2 pushProgram 2 st1 := by simp [run, h1]
      _ = run 1 pushProgram 7 st2 := by simp [run, h2]
      _ = .running 0 st3 := by simp [run, h3]
  · refine ⟨hk.hcap, hk.hmask, hk.hlimit, ?_, ?_, ?_⟩
    · simp only [st3, nxt]
      rw [UInt64.toNat_add, hk.hw]
      have hlt64 : s.w + 1 < 2 ^ 64 := by
        have : s.w < 2 ^ 63 := by omega
        omega
      have h1u : (1 : UInt64).toNat = 1 := rfl
      rw [h1u, Nat.mod_eq_of_lt hlt64]
    · simp [st3, st2, st1, st0]
      exact hk.hr
    · intro j hj
      simpa [st3, st2, st1, st0, viewCell] using hk.hcells j hj
  · simp only [st3, nxt]
    rw [UInt64.toNat_add, hk.hw]
    have hlt64 : s.w + 1 < 2 ^ 64 := by
      have : s.w < 2 ^ 63 := by omega
      omega
    have h1u : (1 : UInt64).toNat = 1 := rfl
    rw [h1u, Nat.mod_eq_of_lt hlt64]
  · simp [st3, st2, st1, st0]

/-- The lagging write-hint case where the slot already carries the empty
cell for `w + C`: the kernel helps the hint forward and loops. -/
theorem push_help_empty {C limit k : Nat} {s : AbsState UInt64} {st : MState}
    (hi : Inv C limit s) (hk : KRef C limit s st)
    (hC : 0 < C) (hCpow : C = 2 ^ k) (hbound : limit < 2 ^ 63)
    (hCmax : C ≤ 2 ^ 24) (hlimitC : limit + C ≤ 2 ^ 63)
    (hW : s.W = s.w + 1)
    (hview : kcellToCell (st.cells (s.w % C)) = emptyCell 0 (s.w + C)) :
    ∃ st', run 5 pushProgram 0 st = .running 0 st' ∧
      KRef C limit { s with w := s.w + 1 } st' ∧
      st'.hintW.toNat = s.w + 1 ∧ st'.hintR = st.hintR := by
  let slot : UInt64 := st.hintW &&& st.params.mask
  let c : KCell := st.cells (s.w % C)
  let st0 : MState := { st with regs := upd st.regs rHint st.hintW }
  let st1 : MState :=
    { st0 with
      regs := upd (upd (upd (upd st0.regs rSlot slot) rMarker c.marker)
        rPayload c.payload) rPos (c.marker >>> 1) }
  let st2 : MState :=
    { st1 with regs := upd st1.regs rPos (st.hintW - (c.marker >>> 1)) }
  let nxt : UInt64 := st.hintW + 1
  let st3 : MState :=
    { st2 with
      hintW := nxt
      regs := upd (upd st2.regs rTmp2 nxt) rOk 1 }
  have hWh : s.w + 1 ≤ limit := by
    rw [← hW]; exact hi.hlimit
  have hxc : s.w + C < 2 ^ 64 := by omega
  have hslot : slot.toNat = s.w % C := hk.hintSlotW hCpow
  have hmarker : c.marker.toNat = 2 * (s.w + C) := by
    have := congrArg Cell.marker hview
    simpa [kcellToCell, emptyCell] using this
  have hpos : (c.marker >>> 1) = st.hintW + st.params.capacity := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_shiftRight, UInt64.toNat_add, hmarker, hk.hw, hk.hcap]
    have h1 : (1 : UInt64).toNat = 1 := rfl
    rw [h1, show 1 % 64 = 1 by decide, Nat.shiftRight_eq_div_pow]
    simp only [Nat.reducePow]
    rw [Nat.mod_eq_of_lt hxc]
    omega
  have hne : (c.marker >>> 1) ≠ st.hintW := by
    rw [hpos]
    intro h
    have h2 := congrArg UInt64.toNat h
    rw [UInt64.toNat_add, hk.hw, hk.hcap] at h2
    rw [Nat.mod_eq_of_lt hxc] at h2
    omega
  have hcap0 : st.params.capacity ≠ 0 := by
    intro h
    have h2 := congrArg UInt64.toNat h
    rw [hk.hcap] at h2
    simp at h2
    omega
  have hbehind : half < st.hintW - (c.marker >>> 1) := by
    rw [UInt64.lt_iff_toNat_lt]
    rw [hpos, UInt64.toNat_sub, UInt64.toNat_add, hk.hw, hk.hcap]
    rw [Nat.mod_eq_of_lt hxc]
    have hnat : 2 ^ 64 - (s.w + C) + s.w = 2 ^ 64 - C := by omega
    rw [hnat]
    have hlt : 2 ^ 64 - C < 2 ^ 64 := by omega
    rw [Nat.mod_eq_of_lt hlt]
    simp [half]
    omega
  have hbehind_ne : st.hintW - (c.marker >>> 1) ≠ st.params.capacity := by
    intro h
    have h2 := congrArg UInt64.toNat h
    rw [hpos, UInt64.toNat_sub, UInt64.toNat_add, hk.hw, hk.hcap] at h2
    rw [Nat.mod_eq_of_lt hxc] at h2
    have hnat : 2 ^ 64 - (s.w + C) + s.w = 2 ^ 64 - C := by omega
    rw [hnat] at h2
    have hlt : 2 ^ 64 - C < 2 ^ 64 := by omega
    rw [Nat.mod_eq_of_lt hlt] at h2
    omega
  have hlt : st.hintW < st.params.limit := by
    rw [UInt64.lt_iff_toNat_lt, hk.hw, hk.hlimit]
    omega
  have h0 : step pushProgram 0 st = .running 1 st0 := by
    simp [step, pushProgram, execOps, execOp, eval, rHint, st0, hlt]
  have h1 : step pushProgram 1 st0 = .running 5 st1 := by
    simp [step, pushProgram, execOps, execOp, eval, rHint, rSlot, rMarker,
      rPayload, rPos, rTmp0, rTmp1, rOk, rTmp2, upd, st0, st1, slot, c,
      hslot, hpos, hne, hcap0]
  have h5 : step pushProgram 5 st1 = .running 8 st2 := by
    simp [step, pushProgram, execOps, execOp, eval, rHint, rSlot, rMarker,
      rPayload, rPos, rTmp0, rTmp1, rOk, rTmp2, upd, st0, st1, st2, c,
      hbehind_ne, hcap0]
  have h8 : step pushProgram 8 st2 = .running 7 st2 := by
    simp [step, pushProgram, execOps, execOp, eval, rHint, rSlot, rMarker,
      rPayload, rPos, rTmp0, rTmp1, rOk, rTmp2, upd, st2, c, hbehind]
  have h7 : step pushProgram 7 st2 = .running 0 st3 := by
    simp [step, pushProgram, execOps, execOp, eval, rHint, rSlot, rMarker,
      rPayload, rPos, rTmp0, rTmp1, rOk, rTmp2, upd, st0, st1, st2, st3,
      nxt]
  refine ⟨st3, ?_, ?_, ?_, ?_⟩
  · calc run 5 pushProgram 0 st
      = run 4 pushProgram 1 st0 := by simp [run, h0]
      _ = run 3 pushProgram 5 st1 := by simp [run, h1]
      _ = run 2 pushProgram 8 st2 := by simp [run, h5]
      _ = run 1 pushProgram 7 st2 := by simp [run, h8]
      _ = .running 0 st3 := by simp [run, h7]
  · refine ⟨hk.hcap, hk.hmask, hk.hlimit, ?_, ?_, ?_⟩
    · simp only [st3, nxt]
      rw [UInt64.toNat_add, hk.hw]
      have hlt64 : s.w + 1 < 2 ^ 64 := by omega
      have h1u : (1 : UInt64).toNat = 1 := rfl
      rw [h1u, Nat.mod_eq_of_lt hlt64]
    · simp [st3, st2, st1, st0]
      exact hk.hr
    · intro j hj
      simpa [st3, st2, st1, st0, viewCell] using hk.hcells j hj
  · simp only [st3, nxt]
    rw [UInt64.toNat_add, hk.hw]
    have hlt64 : s.w + 1 < 2 ^ 64 := by omega
    have h1u : (1 : UInt64).toNat = 1 := rfl
    rw [h1u, Nat.mod_eq_of_lt hlt64]
  · simp [st3, st2, st1, st0]

/-- The lagging read-hint case: the slot carries the cell for `r + C`
(either still full or already empty), so the kernel helps the read hint
forward and loops. -/
theorem pop_help {C limit k : Nat} {s : AbsState UInt64} {st : MState}
    {p : UInt64}
    (hi : Inv C limit s) (hk : KRef C limit s st)
    (hC : 0 < C) (hCpow : C = 2 ^ k) (hbound : limit < 2 ^ 63)
    (hCmax : C ≤ 2 ^ 24) (hlimitC : limit + C ≤ 2 ^ 63)
    (hR : s.R = s.r + 1)
    (hview : kcellToCell (st.cells (s.r % C)) = fullCell (s.r + C) p ∨
      kcellToCell (st.cells (s.r % C)) = emptyCell 0 (s.r + C)) :
    ∃ st', run 4 popProgram 0 st = .running 0 st' ∧
      KRef C limit { s with r := s.r + 1 } st' ∧
      st'.hintR.toNat = s.r + 1 ∧ st'.hintW = st.hintW := by
  let slot : UInt64 := st.hintR &&& st.params.mask
  let c : KCell := st.cells (s.r % C)
  let st0 : MState := { st with regs := upd st.regs rHint st.hintR }
  let st1 : MState :=
    { st0 with
      regs := upd (upd (upd (upd st0.regs rSlot slot) rMarker c.marker)
        rPayload c.payload) rPos (c.marker >>> 1) }
  let st2 : MState :=
    { st1 with regs := upd st1.regs rPos ((c.marker >>> 1) - st.hintR) }
  let nxt : UInt64 := st.hintR + 1
  let st3 : MState :=
    { st2 with
      hintR := nxt
      regs := upd (upd st2.regs rTmp2 nxt) rOk 1 }
  have hWh : s.r + 1 ≤ limit := by
    rw [← hR]
    exact Nat.le_trans hi.hR_le_W hi.hlimit
  have hxc : s.r + C < 2 ^ 64 := by omega
  have hslot : slot.toNat = s.r % C := hk.hintSlotR hCpow
  have hpos : (c.marker >>> 1) = st.hintR + st.params.capacity := by
    cases hview with
    | inl hfull =>
        have hmarker : c.marker.toNat = 2 * (s.r + C) + 1 := by
          have := congrArg Cell.marker hfull
          simpa [kcellToCell, fullCell] using this
        apply UInt64.toNat_inj.mp
        rw [UInt64.toNat_shiftRight, UInt64.toNat_add, hmarker, hk.hr, hk.hcap]
        have h1 : (1 : UInt64).toNat = 1 := rfl
        rw [h1, show 1 % 64 = 1 by decide, Nat.shiftRight_eq_div_pow]
        simp only [Nat.reducePow]
        rw [Nat.mod_eq_of_lt hxc]
        omega
    | inr hempty =>
        have hmarker : c.marker.toNat = 2 * (s.r + C) := by
          have := congrArg Cell.marker hempty
          simpa [kcellToCell, emptyCell] using this
        apply UInt64.toNat_inj.mp
        rw [UInt64.toNat_shiftRight, UInt64.toNat_add, hmarker, hk.hr, hk.hcap]
        have h1 : (1 : UInt64).toNat = 1 := rfl
        rw [h1, show 1 % 64 = 1 by decide, Nat.shiftRight_eq_div_pow]
        simp only [Nat.reducePow]
        rw [Nat.mod_eq_of_lt hxc]
        omega
  have hcap0 : st.params.capacity ≠ 0 := by
    intro h
    have h2 := congrArg UInt64.toNat h
    rw [hk.hcap] at h2
    simp at h2
    omega
  have hne : (c.marker >>> 1) ≠ st.hintR := by
    rw [hpos]
    intro h
    have h2 := congrArg UInt64.toNat h
    rw [UInt64.toNat_add, hk.hr, hk.hcap] at h2
    rw [Nat.mod_eq_of_lt hxc] at h2
    omega
  have hsub : (st.hintR + st.params.capacity) - st.hintR = st.params.capacity := by
    rw [UInt64.add_comm st.hintR st.params.capacity]
    exact UInt64.add_sub_cancel st.params.capacity st.hintR
  have hlt : st.hintR < st.params.limit := by
    rw [UInt64.lt_iff_toNat_lt, hk.hr, hk.hlimit]
    omega
  have hhalf : st.params.capacity < half := by
    rw [UInt64.lt_iff_toNat_lt, hk.hcap]
    simp [half]
    omega
  have h0 : step popProgram 0 st = .running 1 st0 := by
    simp [step, popProgram, execOps, execOp, eval, rHint, st0, hlt]
  have h1 : step popProgram 1 st0 = .running 5 st1 := by
    simp [step, popProgram, execOps, execOp, eval, rHint, rSlot, rMarker,
      rPayload, rPos, rTmp0, rTmp1, rOk, rTmp2, upd, st0, st1, slot, c,
      hslot, hpos, hne, hcap0]
  have hbranch : (c.marker >>> 1) - st.hintR < half := by
    rw [hpos, hsub]
    exact hhalf
  have h5 : step popProgram 5 st1 = .running 6 st2 := by
    simp [step, popProgram, execOps, execOp, eval, rHint, rSlot, rMarker,
      rPayload, rPos, rTmp0, rTmp1, rOk, rTmp2, upd, st0, st1, st2, c,
      hsub, hhalf, hbranch]
  have h6 : step popProgram 6 st2 = .running 0 st3 := by
    simp [step, popProgram, execOps, execOp, eval, rHint, rSlot, rMarker,
      rPayload, rPos, rTmp0, rTmp1, rOk, rTmp2, upd, st0, st1, st2, st3,
      nxt]
  refine ⟨st3, ?_, ?_, ?_, ?_⟩
  · calc run 4 popProgram 0 st
      = run 3 popProgram 1 st0 := by simp [run, h0]
      _ = run 2 popProgram 5 st1 := by simp [run, h1]
      _ = run 1 popProgram 6 st2 := by simp [run, h5]
      _ = .running 0 st3 := by simp [run, h6]
  · refine ⟨hk.hcap, hk.hmask, hk.hlimit, hk.hw, ?_, ?_⟩
    · simp only [st3, nxt]
      rw [UInt64.toNat_add, hk.hr]
      have hlt64 : s.r + 1 < 2 ^ 64 := by omega
      have h1u : (1 : UInt64).toNat = 1 := rfl
      rw [h1u, Nat.mod_eq_of_lt hlt64]
    · intro j hj
      simpa [st3, st2, st1, st0, viewCell] using hk.hcells j hj
  · simp only [st3, nxt]
    rw [UInt64.toNat_add, hk.hr]
    have hlt64 : s.r + 1 < 2 ^ 64 := by omega
    have h1u : (1 : UInt64).toNat = 1 := rfl
    rw [h1u, Nat.mod_eq_of_lt hlt64]
  · simp [st3, st2, st1, st0]

/-- When the write hint is current and the queue is full, the kernel
returns `FULL` without changing the shared state. -/
theorem push_full {C limit k : Nat} {s : AbsState UInt64} {st : MState}
    (hi : Inv C limit s) (hk : KRef C limit s st)
    (hC : 0 < C) (hCpow : C = 2 ^ k)
    (hw : s.w = s.W) (hfull : s.W - s.R = C) (hlim : s.W < limit) :
    ∃ st', run 4 pushProgram 0 st = .returned 1 st' ∧
      st'.cells = st.cells ∧ st'.hintW = st.hintW ∧
      st'.hintR = st.hintR := by
  let slot : UInt64 := st.hintW &&& st.params.mask
  let c : KCell := st.cells (s.W % C)
  let st0 : MState := { st with regs := upd st.regs rHint st.hintW }
  let st1 : MState :=
    { st0 with
      regs := upd (upd (upd (upd st0.regs rSlot slot) rMarker c.marker)
        rPayload c.payload) rPos (c.marker >>> 1) }
  let st2 : MState :=
    { st1 with regs := upd st1.regs rPos (st.hintW - (c.marker >>> 1)) }
  have hslot : slot.toNat = s.W % C := hk.slot hCpow hw
  have hview : kcellToCell c = fullCell (s.W - C) ((s.val (s.W - C)).getD 0) :=
    hk.push_cell_full hi hC hfull
  have hmarker : c.marker.toNat = 2 * (s.W - C) + 1 := by
    have := congrArg Cell.marker hview
    simpa [kcellToCell, fullCell] using this
  have hCLeW : C ≤ s.W := by omega
  have hposNat : (c.marker >>> 1).toNat = s.W - C := by
    rw [UInt64.toNat_shiftRight, hmarker]
    have h1 : (1 : UInt64).toNat = 1 := rfl
    rw [h1]
    have hmod : 1 % 64 = 1 := by decide
    rw [hmod, Nat.shiftRight_eq_div_pow]
    simp only [Nat.reducePow]
    omega
  have hpos : (c.marker >>> 1) = st.hintW - st.params.capacity := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_sub_of_le, hk.hw, hk.hcap]
    · rw [hw]
      exact hposNat
    · rw [UInt64.le_iff_toNat_le, hk.hcap, hk.hw]
      omega
  have hbehind : st.hintW - (c.marker >>> 1) = st.params.capacity := by
    rw [hpos]
    rw [UInt64.sub_eq_iff_eq_add]
    rw [UInt64.add_comm]
    exact (UInt64.sub_add_cancel st.hintW st.params.capacity).symm
  have hne : (c.marker >>> 1) ≠ st.hintW := by
    rw [hpos]
    intro h
    have h2 := congrArg UInt64.toNat h
    rw [UInt64.toNat_sub_of_le, hk.hw, hk.hcap] at h2
    · omega
    · rw [UInt64.le_iff_toNat_le, hk.hcap, hk.hw]
      omega
  have hne' : st.hintW - st.params.capacity ≠ st.hintW := by
    rw [← hpos]
    exact hne
  have hlt : st.hintW < st.params.limit := by
    rw [UInt64.lt_iff_toNat_lt, hk.hw, hk.hlimit, hw]
    exact hlim
  have h0 : step pushProgram 0 st = .running 1 st0 := by
    simp [step, pushProgram, execOps, execOp, eval, rHint, st0, hlt]
  have h1 : step pushProgram 1 st0 = .running 5 st1 := by
    simp [step, pushProgram, execOps, execOp, eval, rHint, rSlot, rMarker,
      rPayload, rPos, rTmp0, rTmp1, rOk, rTmp2, upd, st0, st1, slot, c,
      hslot, hpos, hne']
  have h5 : step pushProgram 5 st1 = .running 6 st2 := by
    simp [step, pushProgram, execOps, execOp, eval, rHint, rSlot, rMarker,
      rPayload, rPos, rTmp0, rTmp1, rOk, rTmp2, upd, st0, st1, st2, c,
      hbehind]
  have h6 : step pushProgram 6 st2 = .returned 1 st2 := by
    simp [step, pushProgram, execOps, eval, st2]
  refine ⟨st2, ?_, ?_, ?_, ?_⟩
  · calc run 4 pushProgram 0 st
      = run 3 pushProgram 1 st0 := by simp [run, h0]
      _ = run 2 pushProgram 5 st1 := by simp [run, h1]
      _ = run 1 pushProgram 6 st2 := by simp [run, h5]
      _ = .returned 1 st2 := by simp [run, h6]
  · simp [st2, st1, st0]
  · simp [st2, st1, st0]
  · simp [st2, st1, st0]

/-- When the read hint is current and the queue is empty, the kernel
returns `EMPTY` without changing the shared state. -/
theorem pop_empty {C limit k : Nat} {s : AbsState UInt64} {st : MState}
    (hi : Inv C limit s) (hk : KRef C limit s st)
    (hC : 0 < C) (hCpow : C = 2 ^ k)
    (hr : s.r = s.R) (hempty : s.R = s.W) (hlim : s.R < limit) :
    ∃ st', run 4 popProgram 0 st = .returned 2 st' ∧
      st'.cells = st.cells ∧ st'.hintW = st.hintW ∧
      st'.hintR = st.hintR := by
  let slot : UInt64 := st.hintR &&& st.params.mask
  let c : KCell := st.cells (s.R % C)
  let st0 : MState := { st with regs := upd st.regs rHint st.hintR }
  let st1 : MState :=
    { st0 with
      regs := upd (upd (upd (upd st0.regs rSlot slot) rMarker c.marker)
        rPayload c.payload) rPos (c.marker >>> 1) }
  let st2 : MState :=
    { st1 with regs := upd st1.regs rTmp0 (c.marker &&& 1) }
  have hslot : slot.toNat = s.R % C := hk.rslot hCpow hr
  have hview : kcellToCell c = emptyCell 0 s.R := hk.pop_cell_empty hi hC hempty
  have hmarker : c.marker.toNat = 2 * s.R := by
    have := congrArg Cell.marker hview
    simpa [kcellToCell, emptyCell] using this
  have hpos : (c.marker >>> 1) = st.hintR := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_shiftRight, hmarker, hk.hr, hr]
    have h1 : (1 : UInt64).toNat = 1 := rfl
    rw [h1]
    have hmod : 1 % 64 = 1 := by decide
    rw [hmod, Nat.shiftRight_eq_div_pow]
    simp only [Nat.reducePow]
    omega
  have hready : (c.marker &&& 1) = 0 := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_and, hmarker]
    simp
  have hlt : st.hintR < st.params.limit := by
    rw [UInt64.lt_iff_toNat_lt, hk.hr, hk.hlimit, hr]
    exact hlim
  have h0 : step popProgram 0 st = .running 1 st0 := by
    simp [step, popProgram, execOps, execOp, eval, rHint, st0, hlt]
  have h1 : step popProgram 1 st0 = .running 2 st1 := by
    simp [step, popProgram, execOps, execOp, eval, rHint, rSlot, rMarker,
      rPayload, rPos, rTmp0, rTmp1, rOk, rTmp2, upd, st0, st1, slot, c,
      hslot, hpos]
  have h2 : step popProgram 2 st1 = .running 3 st2 := by
    simp [step, popProgram, execOps, execOp, eval, rHint, rSlot, rMarker,
      rPayload, rPos, rTmp0, rTmp1, rOk, rTmp2, upd, st0, st1, st2, c,
      hready]
  have h3 : step popProgram 3 st2 = .returned 2 st2 := by
    simp [step, popProgram, execOps, eval, st2]
  refine ⟨st2, ?_, ?_, ?_, ?_⟩
  · calc run 4 popProgram 0 st
      = run 3 popProgram 1 st0 := by simp [run, h0]
      _ = run 2 popProgram 2 st1 := by simp [run, h1]
      _ = run 1 popProgram 3 st2 := by simp [run, h2]
      _ = .returned 2 st2 := by simp [run, h3]
  · simp [st2, st1, st0]
  · simp [st2, st1, st0]
  · simp [st2, st1, st0]

/-- With the write hint at the publication horizon, the kernel returns
`EXHAUSTED` without changing the shared state. -/
theorem push_exhausted {C limit : Nat} {s : AbsState UInt64} {st : MState}
    (hk : KRef C limit s st) (hw : s.w = s.W) (hex : s.W = limit) :
    ∃ st', run 2 pushProgram 0 st = .returned 3 st' ∧
      st'.cells = st.cells ∧ st'.hintW = st.hintW ∧
      st'.hintR = st.hintR := by
  let st0 : MState := { st with regs := upd st.regs rHint st.hintW }
  have hge : ¬ st.hintW < st.params.limit := by
    rw [UInt64.lt_iff_toNat_lt, hk.hw, hk.hlimit, hw, hex]
    omega
  have h0 : step pushProgram 0 st = .running 9 st0 := by
    simp [step, pushProgram, execOps, execOp, eval, rHint, st0, hge]
  have h9 : step pushProgram 9 st0 = .returned 3 st0 := by
    simp [step, pushProgram, execOps, eval, st0]
  refine ⟨st0, ?_, ?_, ?_, ?_⟩
  · calc run 2 pushProgram 0 st
      = run 1 pushProgram 9 st0 := by simp [run, h0]
      _ = .returned 3 st0 := by simp [run, h9]
  · simp [st0]
  · simp [st0]
  · simp [st0]

/-- With the read hint at the publication horizon, the kernel returns
`EXHAUSTED` without changing the shared state. -/
theorem pop_exhausted {C limit : Nat} {s : AbsState UInt64} {st : MState}
    (hk : KRef C limit s st) (hr : s.r = s.R) (hex : s.R = limit) :
    ∃ st', run 2 popProgram 0 st = .returned 3 st' ∧
      st'.cells = st.cells ∧ st'.hintW = st.hintW ∧
      st'.hintR = st.hintR := by
  let st0 : MState := { st with regs := upd st.regs rHint st.hintR }
  have hge : ¬ st.hintR < st.params.limit := by
    rw [UInt64.lt_iff_toNat_lt, hk.hr, hk.hlimit, hr, hex]
    omega
  have h0 : step popProgram 0 st = .running 8 st0 := by
    simp [step, popProgram, execOps, execOp, eval, rHint, st0, hge]
  have h8 : step popProgram 8 st0 = .returned 3 st0 := by
    simp [step, popProgram, execOps, eval, st0]
  refine ⟨st0, ?_, ?_, ?_, ?_⟩
  · calc run 2 popProgram 0 st
      = run 1 popProgram 8 st0 := by simp [run, h0]
      _ = .returned 3 st0 := by simp [run, h8]
  · simp [st0]
  · simp [st0]
  · simp [st0]

end Mpmc
