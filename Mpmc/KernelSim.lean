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
  Kernel-to-event simulation, part 2: the local stage invariants.

  `KernelConcurrent` defines the shared/local split and the single
  `opStep`; `KernelClassify` classifies a cell load and proves the four
  event-producing operations.  This file adds the per-thread *stage*
  invariant: a predicate indexed by the thread's phase which records only
  facts that survive interference from other threads:

  * the hint register value and its provenance bound,
  * the slot register,
  * the snapshot taken by the cell load (marker, position, and the fact
    that it is not above the current cell marker),
  * the route facts the branches need, and
  * the `PushCasPre`/`PopCasPre`/`PushHintPre`/`PopHintPre` shapes at the
    event-producing positions.

  Nothing in a stage mentions the current cell content: a successful cell
  CAS supplies that through its success hypothesis.

  The main results are `push_local_step` and `pop_local_step`: every
  operation of a reachable phase either performs exactly one abstract
  event (one of the four event lemmas of `KernelClassify`) or is a
  stutter, and the stage invariant is preserved.
-/
import Mpmc.KernelClassify

namespace Mpmc

open Mpmc.Kernel

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.unnecessarySimpa false

/-! ## `UInt64` arithmetic helpers

The programs compute with `UInt64`.  Every value they produce is bounded
by `limit + C ≤ 2^63`, so the following bridges between `Nat` arithmetic
and the machine words are all that is needed. -/

theorem u64_eq_ofNat_iff {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (UInt64.ofNat a = UInt64.ofNat b) ↔ a = b := by
  rw [← UInt64.toNat_inj, UInt64.toNat_ofNat', UInt64.toNat_ofNat',
    Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

theorem u64_lt_ofNat_iff {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (UInt64.ofNat a < UInt64.ofNat b) ↔ a < b := by
  rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat', UInt64.toNat_ofNat',
    Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

theorem u64_ofNat_add {a b : Nat} (h : a + b < 2 ^ 64) :
    UInt64.ofNat a + UInt64.ofNat b = UInt64.ofNat (a + b) := by
  have ha : a < 2 ^ 64 := by omega
  have hb : b < 2 ^ 64 := by omega
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_add, UInt64.toNat_ofNat', UInt64.toNat_ofNat', UInt64.toNat_ofNat',
    Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt h]

theorem u64_ofNat_sub {a b : Nat} (hb : b ≤ a) (ha : a < 2 ^ 64) :
    UInt64.ofNat a - UInt64.ofNat b = UInt64.ofNat (a - b) := by
  have hb64 : b < 2 ^ 64 := by omega
  have hab64 : a - b < 2 ^ 64 := by omega
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_sub, UInt64.toNat_ofNat', UInt64.toNat_ofNat', UInt64.toNat_ofNat',
    Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb64]
  have hsplit : 2 ^ 64 - b + a = 2 ^ 64 + (a - b) := by omega
  rw [hsplit, Nat.add_mod, Nat.mod_self, Nat.zero_add,
    Nat.mod_eq_of_lt (Nat.mod_lt _ (by decide : 0 < 2 ^ 64)), Nat.mod_eq_of_lt hab64]

theorem u64_ofNat_shl_one {a : Nat} (h : 2 * a < 2 ^ 64) :
    UInt64.ofNat a <<< (1 : UInt64) = UInt64.ofNat (2 * a) := by
  have ha : a < 2 ^ 64 := by omega
  have h1 : (1 : UInt64).toNat = 1 := rfl
  have h64 : (1 : Nat) % 64 = 1 := by decide
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_shiftLeft, UInt64.toNat_ofNat', UInt64.toNat_ofNat', h1, h64,
    Nat.shiftLeft_eq, Nat.pow_one, Nat.mod_eq_of_lt ha, Nat.mul_comm a 2]

theorem u64_ofNat_shr_one {a : Nat} (ha : a < 2 ^ 64) :
    UInt64.ofNat a >>> (1 : UInt64) = UInt64.ofNat (a / 2) := by
  have h1 : (1 : UInt64).toNat = 1 := rfl
  have h64 : (1 : Nat) % 64 = 1 := by decide
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_shiftRight, UInt64.toNat_ofNat', UInt64.toNat_ofNat', h1, h64,
    Nat.mod_eq_of_lt ha, Nat.shiftRight_eq_div_pow, Nat.pow_one]
  exact (Nat.mod_eq_of_lt (by omega : a / 2 < 2 ^ 64)).symm

theorem u64_ofNat_and_one (a : Nat) :
    UInt64.ofNat a &&& (1 : UInt64) = UInt64.ofNat (a % 2) := by
  have h1 : (1 : UInt64).toNat = 1 := rfl
  have h2 : a % 2 < 2 ^ 64 := by have := Nat.mod_lt a (by decide : 0 < 2); omega
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_and, UInt64.toNat_ofNat', UInt64.toNat_ofNat', h1,
    Nat.mod_eq_of_lt h2]
  rw [show (a % 2 ^ 64) &&& 1 = (a % 2 ^ 64) % 2 from Nat.and_two_pow_sub_one_eq_mod _ 1]
  exact Nat.mod_mod_of_dvd a (by decide : 2 ∣ 2 ^ 64)

theorem u64_ofNat_and_mask {C k h : Nat} (hC : C = 2 ^ k) (hC64 : C < 2 ^ 64)
    (hh : h < 2 ^ 64) :
    UInt64.ofNat h &&& UInt64.ofNat (C - 1) = UInt64.ofNat (h % C) := by
  have hC1 : C - 1 < 2 ^ 64 := by omega
  have hmod : h % C < 2 ^ 64 := by have := Nat.mod_le h C; omega
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_and, UInt64.toNat_ofNat', UInt64.toNat_ofNat', UInt64.toNat_ofNat',
    Nat.mod_eq_of_lt hh, Nat.mod_eq_of_lt hC1, Nat.mod_eq_of_lt hmod]
  have hCk : C - 1 = 2 ^ k - 1 := by omega
  rw [hCk]
  rw [Nat.and_two_pow_sub_one_eq_mod h k, hC]

theorem u64_eq_zero_ofNat {a : Nat} (ha : a < 2 ^ 64) :
    (UInt64.ofNat a = 0) ↔ a = 0 := by
  rw [← UInt64.toNat_inj, UInt64.toNat_ofNat', Nat.mod_eq_of_lt ha]
  simp

/-! ## Consuming an `OpResult` -/

/-- The shared/local pair a thread reaches after one `opStep` returned
`r`: the shared memory is the kernel state's shared projection and the
thread's phase is the result's phase. -/
def After (sh : Shared) (loc : Local) (r : OpResult) (sh' : Shared) (loc' : Local) : Prop :=
  match r with
  | OpResult.running pc oi st =>
      sh' = sh.after st ∧ loc' = { loc.after st with phase := Phase.running pc oi }
  | OpResult.returned v st =>
      sh' = sh.after st ∧ loc' = { loc.after st with phase := Phase.returned v }
  | OpResult.trapped st =>
      sh' = sh.after st ∧ loc' = { loc.after st with phase := Phase.trapped }

/-! ## Output projection facts for the success paths -/

@[simp] theorem execOp_casHint_out0 (r : Nat) (which : Hint) (e d : Expr) (m : MemOrd)
    (st : MState) : (execOp (.casHint r which e d m) st).out0 = st.out0 := by
  simp only [execOp]
  split
  · by_cases h : st.hintW = eval e st <;> simp [h]
  · by_cases h : st.hintR = eval e st <;> simp [h]

@[simp] theorem execOp_casHint_out1 (r : Nat) (which : Hint) (e d : Expr) (m : MemOrd)
    (st : MState) : (execOp (.casHint r which e d m) st).out1 = st.out1 := by
  simp only [execOp]
  split
  · by_cases h : st.hintW = eval e st <;> simp [h]
  · by_cases h : st.hintR = eval e st <;> simp [h]

@[simp] theorem execOp_casHint_regs_of_ne {r x : Nat} (hx : x ≠ r) (which : Hint) (e d : Expr)
    (m : MemOrd) (st : MState) :
    (execOp (.casHint r which e d m) st).regs x = st.regs x := by
  simp only [execOp]
  split
  · by_cases h : st.hintW = eval e st <;> simp [h, upd, hx]
  · by_cases h : st.hintR = eval e st <;> simp [h, upd, hx]

@[simp] theorem execOp_casCell_regs_of_ne {r x : Nat} (hx : x ≠ r)
    (slot em ep dm dp : Expr) (okOrd failOrd : MemOrd) (st : MState) :
    (execOp (.casCell r slot em ep dm dp okOrd failOrd) st).regs x = st.regs x := by
  simp only [execOp]
  split <;> simp [upd, hx]

/-! ## The push stage invariant

The predicate is indexed by the thread's phase.  The stages follow the
program's control flow:

```
0,0 load hint       -> 0,1 test  -> 1,0 slot -> 1,1 load cell -> 1,2 pos
1,3 test ready      -> 2,0 parity -> 2,1 CAS   -> 3,0..3,2 -> 3,3 branch
3,3                 -> 0,0 (CAS failed) | 4,0..4,2 hint CAS -> 4,3 return
1,3 (not ready)     -> 5,0 ahead  -> 5,1 full (6,0) | 8,0 follow -> 7,0..7,1 help
```

Each constructor records only interference-stable facts. -/

inductive PushInv (C limit : Nat) (s : AbsState UInt64) (sh : Shared) (loc : Local) :
    Phase → Prop
  /-- Before the hint load. -/
  | entry (hpc : loc.phase = Phase.running 0 0) : PushInv C limit s sh loc (Phase.running 0 0)
  /-- After loading the write hint. -/
  | hint (h : Nat) (hpc : loc.phase = Phase.running 0 1)
      (hintEq : loc.regs rHint = UInt64.ofNat h)
      (hintLe : h ≤ s.w) : PushInv C limit s sh loc (Phase.running 0 1)
  /-- After the horizon test. -/
  | check (h : Nat) (hpc : loc.phase = Phase.running 1 0)
      (hintEq : loc.regs rHint = UInt64.ofNat h)
      (hintLe : h ≤ s.w) (hlim : h < limit) : PushInv C limit s sh loc (Phase.running 1 0)
  /-- After the slot computation. -/
  | slot (h : Nat) (hpc : loc.phase = Phase.running 1 1)
      (hintEq : loc.regs rHint = UInt64.ofNat h)
      (hintLe : h ≤ s.w) (hlim : h < limit)
      (slotEq : loc.regs rSlot = UInt64.ofNat (h % C)) :
      PushInv C limit s sh loc (Phase.running 1 1)
  /-- After the cell load.  `m` is the loaded marker and `q = m / 2` its
  position; `hfull` records the only non-ready, non-full route. -/
  | load (h m q : Nat) (hpc : loc.phase = Phase.running 1 2)
      (hintEq : loc.regs rHint = UInt64.ofNat h)
      (hintLe : h ≤ s.w) (hlim : h < limit)
      (slotEq : loc.regs rSlot = UInt64.ofNat (h % C))
      (markerEq : loc.regs rMarker = UInt64.ofNat m) (hm64 : m < 2 ^ 64)
      (markerMono : m ≤ ((Shared.toMem sh).cells (h % C)).marker)
      (hq : q = m / 2) (hq63 : q < 2 ^ 63)
      (hfull : q < h → q + C = h) :
      PushInv C limit s sh loc (Phase.running 1 2)
  /-- After `rPos := marker >>> 1`. -/
  | pos (h m q : Nat) (hpc : loc.phase = Phase.running 1 3)
      (hintEq : loc.regs rHint = UInt64.ofNat h)
      (hintLe : h ≤ s.w) (hlim : h < limit)
      (slotEq : loc.regs rSlot = UInt64.ofNat (h % C))
      (markerEq : loc.regs rMarker = UInt64.ofNat m)
      (markerMono : m ≤ ((Shared.toMem sh).cells (h % C)).marker)
      (posEq : loc.regs rPos = UInt64.ofNat q)
      (hq : q = m / 2) (hq63 : q < 2 ^ 63)
      (hfull : q < h → q + C = h) :
      PushInv C limit s sh loc (Phase.running 1 3)
  /-- The ready test succeeded (`q = h`). -/
  | readyTest (h m q : Nat) (hpc : loc.phase = Phase.running 2 0)
      (hintEq : loc.regs rHint = UInt64.ofNat h)
      (hintLe : h ≤ s.w) (hlim : h < limit)
      (slotEq : loc.regs rSlot = UInt64.ofNat (h % C))
      (markerEq : loc.regs rMarker = UInt64.ofNat m)
      (markerMono : m ≤ ((Shared.toMem sh).cells (h % C)).marker)
      (posEq : loc.regs rPos = UInt64.ofNat q)
      (hq : q = m / 2) (hq63 : q < 2 ^ 63)
      (hfull : q < h → q + C = h) (qeq : q = h) :
      PushInv C limit s sh loc (Phase.running 2 0)
  /-- After `rTmp0 := marker &&& 1`. -/
  | evenTest (h m q : Nat) (hpc : loc.phase = Phase.running 2 1)
      (hintEq : loc.regs rHint = UInt64.ofNat h)
      (hintLe : h ≤ s.w) (hlim : h < limit)
      (slotEq : loc.regs rSlot = UInt64.ofNat (h % C))
      (markerEq : loc.regs rMarker = UInt64.ofNat m)
      (markerMono : m ≤ ((Shared.toMem sh).cells (h % C)).marker)
      (posEq : loc.regs rPos = UInt64.ofNat q)
      (hq : q = m / 2) (hq63 : q < 2 ^ 63)
      (hfull : q < h → q + C = h) (qeq : q = h)
      (tmp0Eq : loc.regs rTmp0 = UInt64.ofNat (m % 2)) :
      PushInv C limit s sh loc (Phase.running 2 1)
  /-- The parity test succeeded: the cell is the empty cell for `h`. -/
  | cas0 (h m q : Nat) (hpc : loc.phase = Phase.running 3 0)
      (hintEq : loc.regs rHint = UInt64.ofNat h)
      (hintLe : h ≤ s.w) (hlim : h < limit)
      (slotEq : loc.regs rSlot = UInt64.ofNat (h % C))
      (markerEq : loc.regs rMarker = UInt64.ofNat m)
      (markerMono : m ≤ ((Shared.toMem sh).cells (h % C)).marker)
      (posEq : loc.regs rPos = UInt64.ofNat q)
      (hq : q = m / 2) (hq63 : q < 2 ^ 63)
      (hfull : q < h → q + C = h) (qeq : q = h) (heven : m % 2 = 0) :
      PushInv C limit s sh loc (Phase.running 3 0)
  /-- After computing the desired marker. -/
  | cas1 (h : Nat) (hpc : loc.phase = Phase.running 3 1)
      (hintEq : loc.regs rHint = UInt64.ofNat h)
      (hintLe : h ≤ s.w) (hlim : h < limit)
      (slotEq : loc.regs rSlot = UInt64.ofNat (h % C))
      (markerEq : loc.regs rMarker = UInt64.ofNat (2 * h))
      (desMarker : loc.regs rTmp0 = UInt64.ofNat (2 * h + 1)) :
      PushInv C limit s sh loc (Phase.running 3 1)
  /-- Immediately before the push cell CAS. -/
  | cas (h : Nat) (hp : PushCasPre C limit s sh loc h) :
      PushInv C limit s sh loc (Phase.running 3 2)
  /-- The cell CAS failed. -/
  | casFail (hpc : loc.phase = Phase.running 3 3) (hok : loc.regs rOk = 0) :
      PushInv C limit s sh loc (Phase.running 3 3)
  /-- The cell CAS succeeded; `hmark` is what the help CAS will need. -/
  | casOk (h : Nat) (hpc : loc.phase = Phase.running 3 3) (hok : loc.regs rOk ≠ 0)
      (hintEq : loc.regs rHint = UInt64.ofNat h)
      (hintLe : h ≤ s.w)
      (hmark : 2 * h < ((Shared.toMem sh).cells (h % C)).marker) :
      PushInv C limit s sh loc (Phase.running 3 3)
  /-- After a successful cell CAS, before the output store. -/
  | hintPath0 (h : Nat) (hpc : loc.phase = Phase.running 4 0)
      (hintEq : loc.regs rHint = UInt64.ofNat h)
      (hintLe : h ≤ s.w)
      (hmark : 2 * h < ((Shared.toMem sh).cells (h % C)).marker) :
      PushInv C limit s sh loc (Phase.running 4 0)
  /-- After the output store. -/
  | hintPath1 (h : Nat) (hpc : loc.phase = Phase.running 4 1)
      (hintEq : loc.regs rHint = UInt64.ofNat h)
      (hintLe : h ≤ s.w)
      (hmark : 2 * h < ((Shared.toMem sh).cells (h % C)).marker)
      (outEq : loc.out0 = loc.regs rHint) :
      PushInv C limit s sh loc (Phase.running 4 1)
  /-- Immediately before the write-hint help CAS. -/
  | hintPath2 (h : Nat) (hpc : loc.phase = Phase.running 4 2)
      (hp : PushHintPre C limit s sh loc h)
      (outEq : loc.out0 = loc.regs rHint) :
      PushInv C limit s sh loc (Phase.running 4 2)
  /-- After the help CAS (either outcome); the path returns.  The output
  register still holds the write hint, so the caller-visible output is the
  pushed position. -/
  | hintPath3 (h : Nat) (hpc : loc.phase = Phase.running 4 3)
      (hintEq : loc.regs rHint = UInt64.ofNat h)
      (outEq : loc.out0 = loc.regs rHint) :
      PushInv C limit s sh loc (Phase.running 4 3)
  /-- The `ahead` path with a full slot: `q + C = h`, so the queue is full. -/
  | fullAhead (h m q : Nat) (hpc : loc.phase = Phase.running 5 0)
      (hintEq : loc.regs rHint = UInt64.ofNat h)
      (hintLe : h ≤ s.w) (hlim : h < limit)
      (slotEq : loc.regs rSlot = UInt64.ofNat (h % C))
      (markerEq : loc.regs rMarker = UInt64.ofNat m)
      (hq : q = m / 2) (hfull : q < h) (hqC : q + C = h)
      (posEq : loc.regs rPos = UInt64.ofNat q) :
      PushInv C limit s sh loc (Phase.running 5 0)
  /-- The `ahead` path after the subtraction, full case. -/
  | fullAhead1 (h m q : Nat) (hpc : loc.phase = Phase.running 5 1)
      (hintEq : loc.regs rHint = UInt64.ofNat h)
      (hintLe : h ≤ s.w) (hlim : h < limit)
      (slotEq : loc.regs rSlot = UInt64.ofNat (h % C))
      (markerEq : loc.regs rMarker = UInt64.ofNat m)
      (hq : q = m / 2) (hfull : q < h) (hqC : q + C = h)
      (posEq : loc.regs rPos = UInt64.ofNat (h - q)) :
      PushInv C limit s sh loc (Phase.running 5 1)
  /-- The `ahead` path with a lagging hint: `h < q`, so the difference
  wraps around and the program follows the hint. -/
  | ahead (h m q : Nat) (hpc : loc.phase = Phase.running 5 0)
      (hintEq : loc.regs rHint = UInt64.ofNat h)
      (hintLe : h ≤ s.w) (hlim : h < limit)
      (slotEq : loc.regs rSlot = UInt64.ofNat (h % C))
      (markerEq : loc.regs rMarker = UInt64.ofNat m)
      (markerMono : m ≤ ((Shared.toMem sh).cells (h % C)).marker)
      (hq : q = m / 2) (hq63 : q < 2 ^ 63)
      (hfull : q < h → q + C = h)
      (hltq : h < q)
      (posEq : loc.regs rPos = UInt64.ofNat q) :
      PushInv C limit s sh loc (Phase.running 5 0)
  /-- The `ahead` path after the wrapping subtraction. -/
  | ahead1 (h m q : Nat) (hpc : loc.phase = Phase.running 5 1)
      (hintEq : loc.regs rHint = UInt64.ofNat h)
      (hintLe : h ≤ s.w) (hlim : h < limit)
      (slotEq : loc.regs rSlot = UInt64.ofNat (h % C))
      (markerEq : loc.regs rMarker = UInt64.ofNat m)
      (markerMono : m ≤ ((Shared.toMem sh).cells (h % C)).marker)
      (hq : q = m / 2) (hq63 : q < 2 ^ 63)
      (hltq : h < q)
      (posEq : loc.regs rPos = UInt64.ofNat (2 ^ 64 - (q - h))) :
      PushInv C limit s sh loc (Phase.running 5 1)
  /-- The queue is full: return status 1. -/
  | full (hpc : loc.phase = Phase.running 6 0) : PushInv C limit s sh loc (Phase.running 6 0)
  /-- On the trailing-marker path, the cell position is above the hint. -/
  | help0 (h m q : Nat) (hpc : loc.phase = Phase.running 8 0)
      (hintEq : loc.regs rHint = UInt64.ofNat h)
      (hintLe : h ≤ s.w)
      (markerEq : loc.regs rMarker = UInt64.ofNat m)
      (markerMono : m ≤ ((Shared.toMem sh).cells (h % C)).marker)
      (hq : q = m / 2) (hq63 : q < 2 ^ 63) (hltq : h < q)
      (posEq : loc.regs rPos = UInt64.ofNat (2 ^ 64 - (q - h))) :
      PushInv C limit s sh loc (Phase.running 8 0)
  /-- Before the write-hint help CAS on the lagging-hint path. -/
  | help1 (h : Nat) (hpc : loc.phase = Phase.running 7 0)
      (hintEq : loc.regs rHint = UInt64.ofNat h)
      (hintLe : h ≤ s.w)
      (hmark : 2 * h < ((Shared.toMem sh).cells (h % C)).marker) :
      PushInv C limit s sh loc (Phase.running 7 0)
  /-- Immediately before the write-hint help CAS on the lagging-hint path. -/
  | help2 (h : Nat) (hpc : loc.phase = Phase.running 7 1)
      (hp : PushHintPre C limit s sh loc h) :
      PushInv C limit s sh loc (Phase.running 7 1)
  /-- After the help CAS; the path restarts at the entry. -/
  | help3 (hpc : loc.phase = Phase.running 7 2) : PushInv C limit s sh loc (Phase.running 7 2)
  /-- The horizon test failed: return status 3. -/
  | exhausted (hpc : loc.phase = Phase.running 9 0) :
      PushInv C limit s sh loc (Phase.running 9 0)
  /-- A thread that has returned a status. -/
  | ret (v : UInt64) (hpc : loc.phase = Phase.returned v) : PushInv C limit s sh loc (Phase.returned v)
  /-- A trapped thread. -/
  | trap (hpc : loc.phase = Phase.trapped) : PushInv C limit s sh loc Phase.trapped

/-! ## The pop stage invariant

The pop program mirrors the push program: `0,0` load hint, `1,x` slot and
cell load, `2,x` ready test, `7,0..7,2` cell CAS, `4,x` output and hint
CAS, `5,0..5,1` ahead test, `6,0..6,1` help CAS.  The load decoder
(`pop_load_dec`) gives the extra fact `h ≤ q` unconditionally, which is
what makes the retry fallback unreachable. -/

inductive PopInv (C limit : Nat) (s : AbsState UInt64) (sh : Shared) (loc : Local) :
    Phase → Prop
  /-- Before the hint load. -/
  | entry (hpc : loc.phase = Phase.running 0 0) : PopInv C limit s sh loc (Phase.running 0 0)
  /-- After loading the read hint. -/
  | hint (h : Nat) (hpc : loc.phase = Phase.running 0 1)
      (hintEq : loc.regs rHint = UInt64.ofNat h)
      (hintLe : h ≤ s.r) : PopInv C limit s sh loc (Phase.running 0 1)
  /-- After the horizon test. -/
  | check (h : Nat) (hpc : loc.phase = Phase.running 1 0)
      (hintEq : loc.regs rHint = UInt64.ofNat h)
      (hintLe : h ≤ s.r) (hlim : h < limit) : PopInv C limit s sh loc (Phase.running 1 0)
  /-- After the slot computation. -/
  | slot (h : Nat) (hpc : loc.phase = Phase.running 1 1)
      (hintEq : loc.regs rHint = UInt64.ofNat h)
      (hintLe : h ≤ s.r) (hlim : h < limit)
      (slotEq : loc.regs rSlot = UInt64.ofNat (h % C)) :
      PopInv C limit s sh loc (Phase.running 1 1)
  /-- After the cell load. -/
  | load (h m q : Nat) (hpc : loc.phase = Phase.running 1 2)
      (hintEq : loc.regs rHint = UInt64.ofNat h)
      (hintLe : h ≤ s.r) (hlim : h < limit)
      (slotEq : loc.regs rSlot = UInt64.ofNat (h % C))
      (markerEq : loc.regs rMarker = UInt64.ofNat m) (hm64 : m < 2 ^ 64)
      (markerMono : m ≤ ((Shared.toMem sh).cells (h % C)).marker)
      (hq : q = m / 2) (hq63 : q < 2 ^ 63) (hle_q : h ≤ q) :
      PopInv C limit s sh loc (Phase.running 1 2)
  /-- After `rPos := marker >>> 1`. -/
  | pos (h m q : Nat) (hpc : loc.phase = Phase.running 1 3)
      (hintEq : loc.regs rHint = UInt64.ofNat h)
      (hintLe : h ≤ s.r) (hlim : h < limit)
      (slotEq : loc.regs rSlot = UInt64.ofNat (h % C))
      (markerEq : loc.regs rMarker = UInt64.ofNat m) (hm64 : m < 2 ^ 64)
      (markerMono : m ≤ ((Shared.toMem sh).cells (h % C)).marker)
      (posEq : loc.regs rPos = UInt64.ofNat q)
      (hq : q = m / 2) (hq63 : q < 2 ^ 63) (hle_q : h ≤ q) :
      PopInv C limit s sh loc (Phase.running 1 3)
  /-- The ready test succeeded (`q = h`). -/
  | readyTest (h m q : Nat) (hpc : loc.phase = Phase.running 2 0)
      (hintEq : loc.regs rHint = UInt64.ofNat h)
      (hintLe : h ≤ s.r) (hlim : h < limit)
      (slotEq : loc.regs rSlot = UInt64.ofNat (h % C))
      (markerEq : loc.regs rMarker = UInt64.ofNat m)
      (markerMono : m ≤ ((Shared.toMem sh).cells (h % C)).marker)
      (posEq : loc.regs rPos = UInt64.ofNat q)
      (hq : q = m / 2) (hq63 : q < 2 ^ 63) (hle_q : h ≤ q) (qeq : q = h) :
      PopInv C limit s sh loc (Phase.running 2 0)
  /-- After `rTmp0 := marker &&& 1`. -/
  | evenTest (h m q : Nat) (hpc : loc.phase = Phase.running 2 1)
      (hintEq : loc.regs rHint = UInt64.ofNat h)
      (hintLe : h ≤ s.r) (hlim : h < limit)
      (slotEq : loc.regs rSlot = UInt64.ofNat (h % C))
      (markerEq : loc.regs rMarker = UInt64.ofNat m)
      (markerMono : m ≤ ((Shared.toMem sh).cells (h % C)).marker)
      (posEq : loc.regs rPos = UInt64.ofNat q)
      (hq : q = m / 2) (hq63 : q < 2 ^ 63) (hle_q : h ≤ q) (qeq : q = h)
      (tmp0Eq : loc.regs rTmp0 = UInt64.ofNat (m % 2)) :
      PopInv C limit s sh loc (Phase.running 2 1)
  /-- The parity test found an empty cell: return status 2. -/
  | empty (hpc : loc.phase = Phase.running 3 0) : PopInv C limit s sh loc (Phase.running 3 0)
  /-- The parity test found a full cell for `h`. -/
  | cas0 (h : Nat) (hpc : loc.phase = Phase.running 7 0)
      (hintEq : loc.regs rHint = UInt64.ofNat h)
      (hintLe : h ≤ s.r) (hlim : h < limit)
      (slotEq : loc.regs rSlot = UInt64.ofNat (h % C))
      (markerEq : loc.regs rMarker = UInt64.ofNat (2 * h + 1)) :
      PopInv C limit s sh loc (Phase.running 7 0)
  /-- After computing the desired empty marker. -/
  | cas1 (h : Nat) (hpc : loc.phase = Phase.running 7 1)
      (hintEq : loc.regs rHint = UInt64.ofNat h)
      (hintLe : h ≤ s.r) (hlim : h < limit)
      (slotEq : loc.regs rSlot = UInt64.ofNat (h % C))
      (markerEq : loc.regs rMarker = UInt64.ofNat (2 * h + 1))
      (desMarker : loc.regs rTmp0 = UInt64.ofNat (2 * (h + C))) :
      PopInv C limit s sh loc (Phase.running 7 1)
  /-- Immediately before the pop cell CAS. -/
  | cas (h : Nat) (hp : PopCasPre C limit s sh loc h) :
      PopInv C limit s sh loc (Phase.running 7 2)
  /-- The cell CAS failed. -/
  | casFail (hpc : loc.phase = Phase.running 7 3) (hok : loc.regs rOk = 0) :
      PopInv C limit s sh loc (Phase.running 7 3)
  /-- The cell CAS succeeded; `hmark` is what the help CAS will need. -/
  | casOk (h : Nat) (hpc : loc.phase = Phase.running 7 3) (hok : loc.regs rOk ≠ 0)
      (hintEq : loc.regs rHint = UInt64.ofNat h)
      (hintLe : h ≤ s.r)
      (hmark : 2 * h + 1 < ((Shared.toMem sh).cells (h % C)).marker) :
      PopInv C limit s sh loc (Phase.running 7 3)
  /-- After a successful cell CAS, before the output stores. -/
  | out0 (h : Nat) (hpc : loc.phase = Phase.running 4 0)
      (hintEq : loc.regs rHint = UInt64.ofNat h)
      (hintLe : h ≤ s.r)
      (hmark : 2 * h + 1 < ((Shared.toMem sh).cells (h % C)).marker) :
      PopInv C limit s sh loc (Phase.running 4 0)
  /-- After the payload store. -/
  | out1 (h : Nat) (hpc : loc.phase = Phase.running 4 1)
      (hintEq : loc.regs rHint = UInt64.ofNat h)
      (hintLe : h ≤ s.r)
      (hmark : 2 * h + 1 < ((Shared.toMem sh).cells (h % C)).marker)
      (out0Eq : loc.out0 = loc.regs rPayload) :
      PopInv C limit s sh loc (Phase.running 4 1)
  /-- After the hint store. -/
  | out2 (h : Nat) (hpc : loc.phase = Phase.running 4 2)
      (hintEq : loc.regs rHint = UInt64.ofNat h)
      (hintLe : h ≤ s.r)
      (hmark : 2 * h + 1 < ((Shared.toMem sh).cells (h % C)).marker)
      (out0Eq : loc.out0 = loc.regs rPayload)
      (out1Eq : loc.out1 = loc.regs rHint) :
      PopInv C limit s sh loc (Phase.running 4 2)
  /-- Immediately before the read-hint help CAS. -/
  | out3 (h : Nat) (hpc : loc.phase = Phase.running 4 3)
      (hp : PopHintPre C limit s sh loc h)
      (out0Eq : loc.out0 = loc.regs rPayload)
      (out1Eq : loc.out1 = loc.regs rHint) :
      PopInv C limit s sh loc (Phase.running 4 3)
  /-- After the help CAS; the path returns.  The caller-visible outputs are
  the popped value and its position. -/
  | out4 (h : Nat) (hpc : loc.phase = Phase.running 4 4)
      (hintEq : loc.regs rHint = UInt64.ofNat h)
      (out0Eq : loc.out0 = loc.regs rPayload)
      (out1Eq : loc.out1 = loc.regs rHint) :
      PopInv C limit s sh loc (Phase.running 4 4)
  /-- The `ahead` path: the hint lags the read cursor. -/
  | ahead (h m q : Nat) (hpc : loc.phase = Phase.running 5 0)
      (hintEq : loc.regs rHint = UInt64.ofNat h)
      (hintLe : h ≤ s.r) (hlim : h < limit)
      (slotEq : loc.regs rSlot = UInt64.ofNat (h % C))
      (markerEq : loc.regs rMarker = UInt64.ofNat m)
      (markerMono : m ≤ ((Shared.toMem sh).cells (h % C)).marker)
      (hq : q = m / 2) (hq63 : q < 2 ^ 63) (hle_q : h ≤ q) (qne : q ≠ h)
      (posEq : loc.regs rPos = UInt64.ofNat q) :
      PopInv C limit s sh loc (Phase.running 5 0)
  /-- The `ahead` path after the subtraction. -/
  | ahead1 (h m q : Nat) (hpc : loc.phase = Phase.running 5 1)
      (hintEq : loc.regs rHint = UInt64.ofNat h)
      (hintLe : h ≤ s.r) (hlim : h < limit)
      (slotEq : loc.regs rSlot = UInt64.ofNat (h % C))
      (markerEq : loc.regs rMarker = UInt64.ofNat m)
      (markerMono : m ≤ ((Shared.toMem sh).cells (h % C)).marker)
      (hq : q = m / 2) (hq63 : q < 2 ^ 63) (hle_q : h ≤ q) (qne : q ≠ h)
      (posEq : loc.regs rPos = UInt64.ofNat (q - h)) :
      PopInv C limit s sh loc (Phase.running 5 1)
  /-- The lagging-hint help path. -/
  | help0 (h : Nat) (hpc : loc.phase = Phase.running 6 0)
      (hintEq : loc.regs rHint = UInt64.ofNat h)
      (hintLe : h ≤ s.r)
      (hmark : 2 * h + 1 < ((Shared.toMem sh).cells (h % C)).marker) :
      PopInv C limit s sh loc (Phase.running 6 0)
  /-- Immediately before the read-hint help CAS on the lagging path. -/
  | help1 (h : Nat) (hpc : loc.phase = Phase.running 6 1)
      (hp : PopHintPre C limit s sh loc h) :
      PopInv C limit s sh loc (Phase.running 6 1)
  /-- After the help CAS; the path restarts at the entry. -/
  | help2 (hpc : loc.phase = Phase.running 6 2) : PopInv C limit s sh loc (Phase.running 6 2)
  /-- The horizon test failed: return status 3. -/
  | exhausted (hpc : loc.phase = Phase.running 8 0) :
      PopInv C limit s sh loc (Phase.running 8 0)
  /-- A thread that has returned a status. -/
  | ret (v : UInt64) (hpc : loc.phase = Phase.returned v) : PopInv C limit s sh loc (Phase.returned v)
  /-- A trapped thread. -/
  | trap (hpc : loc.phase = Phase.trapped) : PopInv C limit s sh loc Phase.trapped

/-! ## Extracting the shape of an event -/

theorem EventStep.push_mem {C limit : Nat} {hC : 0 < C}
    {s : AbsState UInt64} {m : Mem UInt64} {s' : AbsState UInt64} {m' : Mem UInt64} {v : UInt64} {h : Nat}
    (he : EventStep 0 C limit hC s m (some (.push v)) (some (.pushed h)) s' m') :
    m' = m.setCell (h % C) (fullCell h v) := by
  cases he with
  | push => rfl

theorem EventStep.push_state {C limit : Nat} {hC : 0 < C}
    {s : AbsState UInt64} {m : Mem UInt64} {s' : AbsState UInt64} {m' : Mem UInt64} {v : UInt64} {h : Nat}
    (he : EventStep 0 C limit hC s m (some (.push v)) (some (.pushed h)) s' m') :
    s' = pushState s v := by
  cases he with
  | push => rfl

theorem EventStep.pop_mem {C limit : Nat} {hC : 0 < C}
    {s : AbsState UInt64} {m : Mem UInt64} {s' : AbsState UInt64} {m' : Mem UInt64} {h : Nat} {p : UInt64}
    (he : EventStep 0 C limit hC s m (some .pop) (some (.popped h p)) s' m') :
    m' = m.setCell (h % C) (emptyCell 0 (h + C)) := by
  cases he with
  | pop => rfl

theorem EventStep.pop_state {C limit : Nat} {hC : 0 < C}
    {s : AbsState UInt64} {m : Mem UInt64} {s' : AbsState UInt64} {m' : Mem UInt64} {h : Nat} {p : UInt64}
    (he : EventStep 0 C limit hC s m (some .pop) (some (.popped h p)) s' m') :
    s' = popState s := by
  cases he with
  | pop => rfl

theorem EventStep.helpW_state {C limit : Nat} {hC : 0 < C}
    {s : AbsState UInt64} {m : Mem UInt64} {s' : AbsState UInt64} {m' : Mem UInt64}
    (he : EventStep 0 C limit hC s m (some .helpW) (some .helped) s' m') :
    s' = { s with w := s.w + 1 } := by
  cases he with
  | helpW => rfl

theorem EventStep.helpR_state {C limit : Nat} {hC : 0 < C}
    {s : AbsState UInt64} {m : Mem UInt64} {s' : AbsState UInt64} {m' : Mem UInt64}
    (he : EventStep 0 C limit hC s m (some .helpR) (some .helped) s' m') :
    s' = { s with r := s.r + 1 } := by
  cases he with
  | helpR => rfl

/-- A `Ref` for the shared projection after an operation gives the full
`SharedRef` back: the kernel never touches the configuration words. -/
theorem SharedRef.after_shared {C limit : Nat} {s s' : AbsState UInt64} {sh : Shared}
    (hs : SharedRef C limit s sh) {st : MState}
    (hr : Ref 0 C s' (Shared.toMem (sh.after st))) :
    SharedRef C limit s' (sh.after st) :=
  ⟨hs.hcap, hs.hmask, hs.hlimit, hr.1, hr.2.1, hr.2.2⟩

theorem SharedRef.limit_eq {C limit : Nat} {s : AbsState UInt64} {sh : Shared}
    (hs : SharedRef C limit s sh) : sh.params.limit = UInt64.ofNat limit := by
  rw [← UInt64.ofNat_toNat (x := sh.params.limit), hs.hlimit]

theorem SharedRef.capacity_eq {C limit : Nat} {s : AbsState UInt64} {sh : Shared}
    (hs : SharedRef C limit s sh) : sh.params.capacity = UInt64.ofNat C := by
  rw [← UInt64.ofNat_toNat (x := sh.params.capacity), hs.hcap]

theorem SharedRef.mask_eq {C limit : Nat} {s : AbsState UInt64} {sh : Shared}
    (hs : SharedRef C limit s sh) : sh.params.mask = UInt64.ofNat (C - 1) := by
  rw [← UInt64.ofNat_toNat (x := sh.params.mask), hs.hmask]

theorem SharedRef.hintW_eq {C limit : Nat} {s : AbsState UInt64} {sh : Shared}
    (hs : SharedRef C limit s sh) : sh.hintW = UInt64.ofNat s.w := by
  rw [← UInt64.ofNat_toNat (x := sh.hintW), hs.hw]

theorem SharedRef.hintR_eq {C limit : Nat} {s : AbsState UInt64} {sh : Shared}
    (hs : SharedRef C limit s sh) : sh.hintR = UInt64.ofNat s.r := by
  rw [← UInt64.ofNat_toNat (x := sh.hintR), hs.hr]

/-! ## The push local step

One `opStep` of the push program at any reachable phase either performs
one abstract event or stutters, and it preserves `PushInv` and
`SharedRef`.  The dispatch is by the phase index of `PushInv`. -/

theorem push_local_step {C limit k : Nat} {s : AbsState UInt64} {sh : Shared} {loc : Local}
    {pc oi : Nat} {r : OpResult}
    (hi : Inv C limit s) (hs : SharedRef C limit s sh)
    (hC : 0 < C) (hpow : C = 2 ^ k) (hbound : limit < 2 ^ 63)
    (hlimitC : limit + C ≤ 2 ^ 63)
    (hphase : loc.phase = Phase.running pc oi)
    (hinv : PushInv C limit s sh loc (Phase.running pc oi))
    (hstep : opStep pushProgram pc oi (toMState sh loc) = r) :
    ∃ (s' : AbsState UInt64) (sh' : Shared) (loc' : Local),
      After sh loc r sh' loc' ∧
      PushInv C limit s' sh' loc' loc'.phase ∧
      SharedRef C limit s' sh' ∧
      ((∃ a res, EventStep 0 C limit hC s (Shared.toMem sh) (some a) (some res) s' (Shared.toMem sh'))
        ∨ (s' = s ∧ sh' = sh)) := by
  cases hinv with
  | entry hpc =>
    have hst : opStep pushProgram 0 0 (toMState sh loc) =
        .running 0 1 { toMState sh loc with
          regs := upd (toMState sh loc).regs rHint (toMState sh loc).hintW } := by
      simp [opStep, pushProgram, execOp]
    rw [hst] at hstep
    cases hstep
    refine ⟨s, sh, { loc.after { toMState sh loc with
        regs := upd (toMState sh loc).regs rHint (toMState sh loc).hintW } with
      phase := Phase.running 0 1 }, ?_, ?_, hs, Or.inr ⟨rfl, rfl⟩⟩
    · exact ⟨rfl, rfl⟩
    · refine PushInv.hint (h := sh.hintW.toNat) rfl ?_ ?_
      · show (upd (toMState sh loc).regs rHint (toMState sh loc).hintW) rHint =
          UInt64.ofNat sh.hintW.toNat
        rw [upd_self]
        exact (UInt64.ofNat_toNat (x := sh.hintW)).symm
      · show sh.hintW.toNat ≤ s.w
        exact Nat.le_of_eq hs.hw
  | hint h hpc hintEq hintLe =>
    have h64 : h < 2 ^ 64 := by
      have h1 : h ≤ s.w := hintLe
      have h2 : s.w ≤ s.W := hi.hw_le
      have h3 : s.W ≤ limit := hi.hlimit
      omega
    have hlim64 : limit < 2 ^ 64 := by omega
    by_cases hlt : h < limit
    · have hcond : (toMState sh loc).regs rHint < (toMState sh loc).params.limit := by
        show loc.regs rHint < sh.params.limit
        rw [hintEq, hs.limit_eq]
        exact (u64_lt_ofNat_iff h64 hlim64).mpr hlt
      have hst : opStep pushProgram 0 1 (toMState sh loc) = .running 1 0 (toMState sh loc) := by
        simp [opStep, pushProgram, eval, hcond]
      rw [hst] at hstep
      cases hstep
      refine ⟨s, sh, { loc.after (toMState sh loc) with phase := Phase.running 1 0 },
        ⟨rfl, rfl⟩, ?_, hs, Or.inr ⟨rfl, rfl⟩⟩
      exact PushInv.check h rfl hintEq hintLe hlt
    · have hcond : ¬ ((toMState sh loc).regs rHint < (toMState sh loc).params.limit) := by
        intro hc
        apply hlt
        have hc2 : UInt64.ofNat h < UInt64.ofNat limit := by
          have hcc := hc
          simp [toMState, hintEq, hs.limit_eq] at hcc
          exact hcc
        exact (u64_lt_ofNat_iff h64 hlim64).mp hc2
      have hst : opStep pushProgram 0 1 (toMState sh loc) = .running 9 0 (toMState sh loc) := by
        simp [opStep, pushProgram, eval, hcond]
      rw [hst] at hstep
      cases hstep
      refine ⟨s, sh, { loc.after (toMState sh loc) with phase := Phase.running 9 0 },
        ⟨rfl, rfl⟩, ?_, hs, Or.inr ⟨rfl, rfl⟩⟩
      exact PushInv.exhausted rfl
  | check h hpc hintEq hintLe hlim =>
    have h64 : h < 2 ^ 64 := by have h1 := hi.hlimit; omega
    have hC64 : C < 2 ^ 64 := by omega
    let st0 := toMState sh loc
    let st' := { st0 with regs := upd (st0.regs) rSlot (st0.regs rHint &&& st0.params.mask) }
    have hst : opStep pushProgram 1 0 (toMState sh loc) = .running 1 1 st' := by
      simp [opStep, pushProgram, execOp, eval, st', st0]
    rw [hst] at hstep
    cases hstep
    refine ⟨s, sh, { loc.after st' with phase := Phase.running 1 1 },
      ⟨rfl, rfl⟩, ?_, hs, Or.inr ⟨rfl, rfl⟩⟩
    refine PushInv.slot h rfl hintEq hintLe hlim ?_
    show st'.regs rSlot = UInt64.ofNat (h % C)
    simp only [st', st0, upd_self, toMState]
    rw [hintEq, hs.mask_eq]
    exact u64_ofNat_and_mask hpow hC64 h64
  | slot h hpc hintEq hintLe hlim slotEq =>
    have h64 : h < 2 ^ 64 := by have h1 := hi.hlimit; omega
    have hmodle : h % C ≤ h := Nat.mod_le h C
    have hmod64 : h % C < 2 ^ 64 := by omega
    have hslotNat : (loc.regs rSlot).toNat = h % C := by
      rw [slotEq]
      exact uint64_toNat_ofNat_of_lt hmod64
    let m := (sh.cells (h % C)).marker.toNat
    let st0 := toMState sh loc
    let regs1 := upd (st0.regs) rMarker (sh.cells (h % C)).marker
    let regs2 := upd regs1 rPayload (sh.cells (h % C)).payload
    let st' := { st0 with regs := regs2 }
    have hcellEq : (toMState sh loc).cells ((toMState sh loc).regs rSlot).toNat
        = sh.cells (h % C) := by
      show sh.cells (loc.regs rSlot).toNat = sh.cells (h % C)
      rw [hslotNat]
    have hst : opStep pushProgram 1 1 (toMState sh loc) = .running 1 2 st' := by
      simp [opStep, pushProgram, execOp, eval, st', st0, regs1, regs2, hcellEq]
    rw [hst] at hstep
    cases hstep
    have hcell : kcellToCell (sh.cells (h % C)) = viewCell 0 C s (h % C) :=
      hs.hcells (h % C) (Nat.mod_lt _ hC)
    have hdec := push_load_dec (k := k) hi hs hC hpow h hintLe (c := sh.cells (h % C)) hcell
    have hmarkerVal : (sh.cells (h % C)).marker.toNat = (viewCell 0 C s (h % C)).marker := by
      have := congrArg Cell.marker hcell
      simpa [kcellToCell] using this
    have hqpos : m / 2 = slotPos s.R (h % C) C := by
      show (sh.cells (h % C)).marker.toNat / 2 = slotPos s.R (h % C) C
      rw [hmarkerVal]
      exact viewCell_pos 0 C s (h % C)
    have hq63 : m / 2 < 2 ^ 63 := by
      rw [hqpos]
      have hlt := slotPos_lt (R := s.R) (j := h % C) (C := C) (Nat.mod_lt _ hC)
      have h1 : s.R ≤ s.W := hi.hR_le_W
      have h2 : s.W ≤ limit := hi.hlimit
      omega
    have hfull : m / 2 < h → m / 2 + C = h := by
      intro hlt
      by_cases hne : m / 2 + C = h
      · exact hne
      · exfalso
        have hnotready : ¬ (m / 2 = h ∧ m % 2 = 0) := by
          intro hh
          omega
        have hle : h ≤ m / 2 := hdec.2.2 hnotready hne
        omega
    refine ⟨s, sh, { loc.after st' with phase := Phase.running 1 2 },
      ⟨rfl, rfl⟩, ?_, hs, Or.inr ⟨rfl, rfl⟩⟩
    refine PushInv.load h m (m / 2) rfl hintEq hintLe hlim slotEq ?_ ?_ ?_ rfl hq63 hfull
    · show st'.regs rMarker = UInt64.ofNat m
      simp only [st', upd_self]
      exact (UInt64.ofNat_toNat (x := (sh.cells (h % C)).marker)).symm
    · show m < 2 ^ 64
      exact UInt64.toNat_lt _
    · show m ≤ ((Shared.toMem sh).cells (h % C)).marker
      exact Nat.le_refl _
  | load h m q hpc hintEq hintLe hlim slotEq markerEq hm64 markerMono hq hq63 hfull =>
    let st0 := toMState sh loc
    let st' := { st0 with regs := upd (st0.regs) rPos (st0.regs rMarker >>> (1 : UInt64)) }
    have hst : opStep pushProgram 1 2 (toMState sh loc) = .running 1 3 st' := by
      simp [opStep, pushProgram, execOp, eval, st', st0]
    rw [hst] at hstep
    cases hstep
    refine ⟨s, sh, { loc.after st' with phase := Phase.running 1 3 },
      ⟨rfl, rfl⟩, ?_, hs, Or.inr ⟨rfl, rfl⟩⟩
    refine PushInv.pos h m q rfl hintEq hintLe hlim slotEq markerEq markerMono ?_ hq hq63 hfull
    show st'.regs rPos = UInt64.ofNat q
    simp only [st', st0, upd_self, toMState]
    rw [markerEq, hq]
    exact u64_ofNat_shr_one hm64
  | pos h m q hpc hintEq hintLe hlim slotEq markerEq markerMono posEq hq hq63 hfull =>
    have h64 : h < 2 ^ 64 := by have h1 := hi.hlimit; omega
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
      refine ⟨s, sh, { loc.after (toMState sh loc) with phase := Phase.running 2 0 },
        ⟨rfl, rfl⟩, ?_, hs, Or.inr ⟨rfl, rfl⟩⟩
      exact PushInv.readyTest h m q rfl hintEq hintLe hlim slotEq markerEq markerMono posEq hq hq63 hfull qh
    · have hne : (toMState sh loc).regs rPos ≠ (toMState sh loc).regs rHint := by
        show loc.regs rPos ≠ loc.regs rHint
        rw [posEq, hintEq]
        intro hc
        exact qh ((u64_eq_ofNat_iff hq64 h64).mp hc)
      have hst : opStep pushProgram 1 3 (toMState sh loc) = .running 5 0 (toMState sh loc) := by
        simp [opStep, pushProgram, eval, hne]
      rw [hst] at hstep
      cases hstep
      by_cases hlt : q < h
      · refine ⟨s, sh, { loc.after (toMState sh loc) with phase := Phase.running 5 0 },
          ⟨rfl, rfl⟩, ?_, hs, Or.inr ⟨rfl, rfl⟩⟩
        exact PushInv.fullAhead h m q rfl hintEq hintLe hlim slotEq markerEq hq hlt (hfull hlt) posEq
      · have hgt : h < q := by omega
        refine ⟨s, sh, { loc.after (toMState sh loc) with phase := Phase.running 5 0 },
          ⟨rfl, rfl⟩, ?_, hs, Or.inr ⟨rfl, rfl⟩⟩
        exact PushInv.ahead h m q rfl hintEq hintLe hlim slotEq markerEq markerMono hq hq63 hfull hgt posEq
  | readyTest h m q hpc hintEq hintLe hlim slotEq markerEq markerMono posEq hq hq63 hfull qeq =>
    let st0 := toMState sh loc
    let st' := { st0 with regs := upd (st0.regs) rTmp0 (st0.regs rMarker &&& (1 : UInt64)) }
    have hst : opStep pushProgram 2 0 (toMState sh loc) = .running 2 1 st' := by
      simp [opStep, pushProgram, execOp, eval, st', st0]
    rw [hst] at hstep
    cases hstep
    refine ⟨s, sh, { loc.after st' with phase := Phase.running 2 1 },
      ⟨rfl, rfl⟩, ?_, hs, Or.inr ⟨rfl, rfl⟩⟩
    refine PushInv.evenTest h m q rfl hintEq hintLe hlim slotEq markerEq markerMono posEq hq hq63 hfull qeq ?_
    show st'.regs rTmp0 = UInt64.ofNat (m % 2)
    simp only [st', st0, upd_self, toMState]
    rw [markerEq]
    exact u64_ofNat_and_one m
  | evenTest h m q hpc hintEq hintLe hlim slotEq markerEq markerMono posEq hq hq63 hfull qeq tmp0Eq =>
    have hm2 : m % 2 < 2 ^ 64 := by
      have := Nat.mod_lt m (by decide : 0 < 2)
      omega
    by_cases hpar : m % 2 = 0
    · have hcond : (toMState sh loc).regs rTmp0 = 0 := by
        show loc.regs rTmp0 = 0
        rw [tmp0Eq, u64_eq_zero_ofNat hm2, hpar]
      have hst : opStep pushProgram 2 1 (toMState sh loc) = .running 3 0 (toMState sh loc) := by
        simp [opStep, pushProgram, eval, hcond]
      rw [hst] at hstep
      cases hstep
      refine ⟨s, sh, { loc.after (toMState sh loc) with phase := Phase.running 3 0 },
        ⟨rfl, rfl⟩, ?_, hs, Or.inr ⟨rfl, rfl⟩⟩
      exact PushInv.cas0 h m q rfl hintEq hintLe hlim slotEq markerEq markerMono posEq hq hq63 hfull qeq hpar
    · have hodd : m % 2 = 1 := by omega
      have hm_eq : m = 2 * h + 1 := by
        have hdm := Nat.div_add_mod m 2
        omega
      have hmark : 2 * h < ((Shared.toMem sh).cells (h % C)).marker := by
        have hm := markerMono
        omega
      have hcond : ¬ ((toMState sh loc).regs rTmp0 = 0) := by
        show ¬ (loc.regs rTmp0 = 0)
        rw [tmp0Eq]
        intro hc
        exact hpar ((u64_eq_zero_ofNat hm2).mp hc)
      have hst : opStep pushProgram 2 1 (toMState sh loc) = .running 7 0 (toMState sh loc) := by
        simp [opStep, pushProgram, eval, hcond]
      rw [hst] at hstep
      cases hstep
      refine ⟨s, sh, { loc.after (toMState sh loc) with phase := Phase.running 7 0 },
        ⟨rfl, rfl⟩, ?_, hs, Or.inr ⟨rfl, rfl⟩⟩
      exact PushInv.help1 h rfl hintEq hintLe hmark
  | cas0 h m q hpc hintEq hintLe hlim slotEq markerEq markerMono posEq hq hq63 hfull qeq heven =>
    have h63 : h < 2 ^ 63 := by
      have h1 : h ≤ s.w := hintLe
      have h2 : s.w ≤ s.W := hi.hw_le
      have h3 : s.W ≤ limit := hi.hlimit
      omega
    have hm_eq : m = 2 * h := by
      have hdm := Nat.div_add_mod m 2
      omega
    let st0 := toMState sh loc
    let v := (st0.regs rHint <<< (1 : UInt64)) + (1 : UInt64)
    let st' := { st0 with regs := upd (st0.regs) rTmp0 v }
    have hst : opStep pushProgram 3 0 (toMState sh loc) = .running 3 1 st' := by
      simp [opStep, pushProgram, execOp, eval, st', st0, v]
    rw [hst] at hstep
    cases hstep
    refine ⟨s, sh, { loc.after st' with phase := Phase.running 3 1 },
      ⟨rfl, rfl⟩, ?_, hs, Or.inr ⟨rfl, rfl⟩⟩
    refine PushInv.cas1 h rfl hintEq hintLe hlim slotEq ?_ ?_
    · show st'.regs rMarker = UInt64.ofNat (2 * h)
      have hne : rMarker ≠ rTmp0 := by decide
      rw [show st'.regs rMarker = st0.regs rMarker from by
        show upd st0.regs rTmp0 v rMarker = st0.regs rMarker
        exact upd_ne st0.regs rTmp0 rMarker v hne]
      simp only [st0, toMState]
      rw [markerEq, hm_eq]
    · show st'.regs rTmp0 = UInt64.ofNat (2 * h + 1)
      simp only [st', st0, v, upd_self, toMState]
      rw [hintEq, u64_ofNat_shl_one (by omega)]
      show UInt64.ofNat (2 * h) + UInt64.ofNat 1 = UInt64.ofNat (2 * h + 1)
      exact u64_ofNat_add (by omega)
  | cas1 h hpc hintEq hintLe hlim slotEq markerEq desMarker =>
    let st0 := toMState sh loc
    let st' := { st0 with regs := upd (st0.regs) rTmp1 st0.params.value }
    have hst : opStep pushProgram 3 1 (toMState sh loc) = .running 3 2 st' := by
      simp [opStep, pushProgram, execOp, eval, st', st0]
    rw [hst] at hstep
    cases hstep
    refine ⟨s, sh, { loc.after st' with phase := Phase.running 3 2 },
      ⟨rfl, rfl⟩, ?_, hs, Or.inr ⟨rfl, rfl⟩⟩
    refine PushInv.cas h ⟨rfl, hintEq, hintLe, hlim, slotEq, markerEq, desMarker, ?_⟩
    show st'.regs rTmp1 = loc.value
    simp [st', st0, upd_self, toMState]
  | cas h hp =>
    by_cases hsucc : (toMState sh loc).cells ((toMState sh loc).regs rSlot).toNat =
        { marker := (toMState sh loc).regs rMarker, payload := (toMState sh loc).regs rPayload }
    · obtain ⟨st', hst', hev⟩ :=
        pushCas_event_of_success hi hs hC hpow hbound hp.hlim hp hsucc
      let cnew : KCell :=
        { marker := (toMState sh loc).regs rTmp0, payload := (toMState sh loc).regs rTmp1 }
      let st1 : MState := { toMState sh loc with
        cells := upd (toMState sh loc).cells ((toMState sh loc).regs rSlot).toNat cnew,
        regs := upd (toMState sh loc).regs rOk 1 }
      have hst1 : opStep pushProgram 3 2 (toMState sh loc) = .running 3 3 st1 := by
        simp [opStep, pushProgram, execOp, eval, hsucc, st1, cnew]
      rw [hst1] at hst'
      have hstEq : st' = st1 := by
        injection hst' with _ _ h
        exact h.symm
      rw [hst1] at hstep
      cases hstep
      subst hstEq
      have hstate := EventStep.push_state hev
      have hmem := EventStep.push_mem hev
      refine ⟨pushState s loc.value, sh.after st1,
        { loc.after st1 with phase := Phase.running 3 3 },
        ⟨rfl, rfl⟩, ?_, ?_, Or.inl ⟨.push loc.value, .pushed h, hev⟩⟩
      · refine PushInv.casOk h rfl ?_ hp.hintEq ?_ ?_
        · -- rOk ≠ 0
          show st1.regs rOk ≠ 0
          simp [st1]
        · -- h ≤ (pushState s v).w
          simpa [pushState] using hp.hintLe
        · -- hmark in the new shared state
          rw [hmem]
          simp [Mem.setCell, fullCell]
      · have href : Ref 0 C (pushState s loc.value) (Shared.toMem (sh.after st1)) :=
          EventStep.ref hev
        exact SharedRef.after_shared hs href
    · let st1 : MState := { toMState sh loc with regs := upd (toMState sh loc).regs rOk 0 }
      have hst1 : opStep pushProgram 3 2 (toMState sh loc) = .running 3 3 st1 := by
        simp [opStep, pushProgram, execOp, eval, hsucc, st1]
      rw [hst1] at hstep
      cases hstep
      refine ⟨s, sh, { loc.after st1 with phase := Phase.running 3 3 },
        ⟨rfl, rfl⟩, ?_, hs, Or.inr ⟨rfl, rfl⟩⟩
      refine PushInv.casFail rfl ?_
      show st1.regs rOk = 0
      simp [st1]
  | casFail hpc hok =>
    have hcond : (toMState sh loc).regs rOk = 0 := hok
    have hst : opStep pushProgram 3 3 (toMState sh loc) = .running 0 0 (toMState sh loc) := by
      simp [opStep, pushProgram, eval, hcond]
    rw [hst] at hstep
    cases hstep
    exact ⟨s, sh, { loc.after (toMState sh loc) with phase := Phase.running 0 0 },
      ⟨rfl, rfl⟩, PushInv.entry rfl, hs, Or.inr ⟨rfl, rfl⟩⟩
  | casOk h hpc hok hintEq hintLe hmark =>
    have hcond : ¬ ((toMState sh loc).regs rOk = 0) := hok
    have hst : opStep pushProgram 3 3 (toMState sh loc) = .running 4 0 (toMState sh loc) := by
      simp [opStep, pushProgram, eval, hcond]
    rw [hst] at hstep
    cases hstep
    exact ⟨s, sh, { loc.after (toMState sh loc) with phase := Phase.running 4 0 },
      ⟨rfl, rfl⟩, PushInv.hintPath0 h rfl hintEq hintLe hmark, hs, Or.inr ⟨rfl, rfl⟩⟩
  | hintPath0 h hpc hintEq hintLe hmark =>
    let st0 := toMState sh loc
    let st' := { st0 with out0 := st0.regs rHint }
    have hst : opStep pushProgram 4 0 (toMState sh loc) = .running 4 1 st' := by
      simp [opStep, pushProgram, execOp, eval, st', st0]
    rw [hst] at hstep
    cases hstep
    exact ⟨s, sh, { loc.after st' with phase := Phase.running 4 1 },
      ⟨rfl, rfl⟩, PushInv.hintPath1 h rfl hintEq hintLe hmark
        (by simp [Local.after, st', st0, toMState]), hs, Or.inr ⟨rfl, rfl⟩⟩
  | hintPath1 h hpc hintEq hintLe hmark outEq =>
    have h2h1 : h + 1 < 2 ^ 64 := by
      have h1 : h ≤ s.w := hintLe
      have h2 : s.w ≤ s.W := hi.hw_le
      have h3 : s.W ≤ limit := hi.hlimit
      have h4 : limit < 2 ^ 63 := hbound
      omega
    let st0 := toMState sh loc
    let st' := { st0 with regs := upd (st0.regs) rTmp2 (st0.regs rHint + (1 : UInt64)) }
    have hst : opStep pushProgram 4 1 (toMState sh loc) = .running 4 2 st' := by
      simp [opStep, pushProgram, execOp, eval, st', st0]
    rw [hst] at hstep
    cases hstep
    refine ⟨s, sh, { loc.after st' with phase := Phase.running 4 2 },
      ⟨rfl, rfl⟩, ?_, hs, Or.inr ⟨rfl, rfl⟩⟩
    refine PushInv.hintPath2 h rfl ⟨hintEq, hintLe, hmark, ?_⟩
      (by simpa [Local.after, st', st0, upd, rHint, rTmp2, rPayload, rOk, toMState] using outEq)
    show st'.regs rTmp2 = UInt64.ofNat (h + 1)
    simp only [st', st0, upd_self, toMState]
    rw [hintEq]
    show UInt64.ofNat h + UInt64.ofNat 1 = UInt64.ofNat (h + 1)
    exact u64_ofNat_add h2h1
  | hintPath2 h hpc hp outEq =>
    have h64 : h < 2 ^ 64 := by
      have h1 : h ≤ s.w := hp.hintLe
      have h2 : s.w ≤ s.W := hi.hw_le
      have h3 : s.W ≤ limit := hi.hlimit
      have h4 : limit < 2 ^ 63 := hbound
      omega
    have h2h1 : h + 1 < 2 ^ 64 := by
      have h1 : h ≤ s.w := hp.hintLe
      have h2 : s.w ≤ s.W := hi.hw_le
      have h3 : s.W ≤ limit := hi.hlimit
      have h4 : limit < 2 ^ 63 := hbound
      omega
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
        ⟨rfl, rfl⟩, PushInv.hintPath3 h rfl
          (by rw [← hexec]; simp only [Local.after]
              rw [execOp_casHint_regs_of_ne (by decide : rHint ≠ rOk)]
              simpa [toMState] using hp.hintReg)
          (by rw [← hexec]; simp only [Local.after]
              rw [execOp_casHint_out0, execOp_casHint_regs_of_ne (by decide : rHint ≠ rOk)]
              simpa [toMState] using outEq),
        ?_, Or.inl ⟨.helpW, .helped, hev⟩⟩
      have href : Ref 0 C { s with w := s.w + 1 } (Shared.toMem (sh.after st')) :=
        EventStep.ref hev
      exact SharedRef.after_shared hs href
    · let st1 : MState := { toMState sh loc with regs := upd (toMState sh loc).regs rOk 0 }
      have hst : opStep pushProgram 4 2 (toMState sh loc) = .running 4 3 st1 := by
        simp [opStep, pushProgram, execOp, eval, hsucc, st1]
      rw [hst] at hstep
      cases hstep
      exact ⟨s, sh, { loc.after st1 with phase := Phase.running 4 3 },
        ⟨rfl, rfl⟩, PushInv.hintPath3 h rfl
          (by simpa [Local.after, st1, toMState, upd, rHint, rOk] using hp.hintReg)
          (by simpa [Local.after, st1, toMState, upd, rHint, rOk, rPayload, rTmp2] using outEq),
        hs, Or.inr ⟨rfl, rfl⟩⟩
  | hintPath3 h hpc hintEq outEq =>
    have hst : opStep pushProgram 4 3 (toMState sh loc) = .returned 0 (toMState sh loc) := by
      simp [opStep, pushProgram, eval]
    rw [hst] at hstep
    cases hstep
    exact ⟨s, sh, { loc.after (toMState sh loc) with phase := Phase.returned 0 },
      ⟨rfl, rfl⟩, PushInv.ret 0 rfl, hs, Or.inr ⟨rfl, rfl⟩⟩
  | fullAhead h m q hpc hintEq hintLe hlim slotEq markerEq hq hfull hqC posEq =>
    have h64 : h < 2 ^ 64 := by have h1 := hi.hlimit; omega
    have hq64 : q < 2 ^ 64 := by omega
    let st0 := toMState sh loc
    let st' := { st0 with regs := upd (st0.regs) rPos (st0.regs rHint - st0.regs rPos) }
    have hst : opStep pushProgram 5 0 (toMState sh loc) = .running 5 1 st' := by
      simp [opStep, pushProgram, execOp, eval, st', st0]
    rw [hst] at hstep
    cases hstep
    refine ⟨s, sh, { loc.after st' with phase := Phase.running 5 1 },
      ⟨rfl, rfl⟩, ?_, hs, Or.inr ⟨rfl, rfl⟩⟩
    refine PushInv.fullAhead1 h m q rfl hintEq hintLe hlim slotEq markerEq hq hfull hqC ?_
    show st'.regs rPos = UInt64.ofNat (h - q)
    simp only [st', st0, upd_self, toMState]
    rw [hintEq, posEq]
    exact u64_ofNat_sub (by omega) h64
  | fullAhead1 h m q hpc hintEq hintLe hlim slotEq markerEq hq hfull hqC posEq =>
    have hqc : h - q = C := by omega
    have hcond : (toMState sh loc).regs rPos = (toMState sh loc).params.capacity := by
      show loc.regs rPos = sh.params.capacity
      rw [posEq, hs.capacity_eq, hqc]
    have hst : opStep pushProgram 5 1 (toMState sh loc) = .running 6 0 (toMState sh loc) := by
      simp [opStep, pushProgram, eval, hcond]
    rw [hst] at hstep
    cases hstep
    exact ⟨s, sh, { loc.after (toMState sh loc) with phase := Phase.running 6 0 },
      ⟨rfl, rfl⟩, PushInv.full rfl, hs, Or.inr ⟨rfl, rfl⟩⟩
  | ahead h m q hpc hintEq hintLe hlim slotEq markerEq markerMono hq hq63 hfull hltq posEq =>
    have h64 : h < 2 ^ 64 := by
      have h1 : h ≤ s.w := hintLe
      have h2 : s.w ≤ s.W := hi.hw_le
      have h3 : s.W ≤ limit := hi.hlimit
      omega
    have hq64 : q < 2 ^ 64 := by omega
    let st0 := toMState sh loc
    let st' := { st0 with regs := upd (st0.regs) rPos (st0.regs rHint - st0.regs rPos) }
    have hst : opStep pushProgram 5 0 (toMState sh loc) = .running 5 1 st' := by
      simp [opStep, pushProgram, execOp, eval, st', st0]
    rw [hst] at hstep
    cases hstep
    refine ⟨s, sh, { loc.after st' with phase := Phase.running 5 1 },
      ⟨rfl, rfl⟩, ?_, hs, Or.inr ⟨rfl, rfl⟩⟩
    refine PushInv.ahead1 h m q rfl hintEq hintLe hlim slotEq markerEq markerMono hq hq63 hltq ?_
    show st'.regs rPos = UInt64.ofNat (2 ^ 64 - (q - h))
    simp only [st', st0, upd_self, toMState]
    rw [hintEq, posEq]
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_sub, UInt64.toNat_ofNat', UInt64.toNat_ofNat', UInt64.toNat_ofNat',
      Nat.mod_eq_of_lt h64, Nat.mod_eq_of_lt hq64,
      Nat.mod_eq_of_lt (by omega : 2 ^ 64 - (q - h) < 2 ^ 64)]
    have hval : 2 ^ 64 - q + h = 2 ^ 64 - (q - h) := by omega
    rw [hval, Nat.mod_eq_of_lt (by omega : 2 ^ 64 - (q - h) < 2 ^ 64)]
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
    exact ⟨s, sh, { loc.after (toMState sh loc) with phase := Phase.running 8 0 },
      ⟨rfl, rfl⟩, PushInv.help0 h m q rfl hintEq hintLe markerEq markerMono hq hq63 hltq posEq,
      hs, Or.inr ⟨rfl, rfl⟩⟩
  | full hpc =>
    have hst : opStep pushProgram 6 0 (toMState sh loc) = .returned 1 (toMState sh loc) := by
      simp [opStep, pushProgram, eval]
    rw [hst] at hstep
    cases hstep
    exact ⟨s, sh, { loc.after (toMState sh loc) with phase := Phase.returned 1 },
      ⟨rfl, rfl⟩, PushInv.ret 1 rfl, hs, Or.inr ⟨rfl, rfl⟩⟩
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
    exact ⟨s, sh, { loc.after (toMState sh loc) with phase := Phase.running 7 0 },
      ⟨rfl, rfl⟩, PushInv.help1 h rfl hintEq hintLe hmark, hs, Or.inr ⟨rfl, rfl⟩⟩
  | help1 h hpc hintEq hintLe hmark =>
    have h2h1 : h + 1 < 2 ^ 64 := by
      have h1 : h ≤ s.w := hintLe
      have h2 : s.w ≤ s.W := hi.hw_le
      have h3 : s.W ≤ limit := hi.hlimit
      have h4 : limit < 2 ^ 63 := hbound
      omega
    let st0 := toMState sh loc
    let st' := { st0 with regs := upd (st0.regs) rTmp2 (st0.regs rHint + (1 : UInt64)) }
    have hst : opStep pushProgram 7 0 (toMState sh loc) = .running 7 1 st' := by
      simp [opStep, pushProgram, execOp, eval, st', st0]
    rw [hst] at hstep
    cases hstep
    refine ⟨s, sh, { loc.after st' with phase := Phase.running 7 1 },
      ⟨rfl, rfl⟩, ?_, hs, Or.inr ⟨rfl, rfl⟩⟩
    refine PushInv.help2 h rfl ⟨hintEq, hintLe, hmark, ?_⟩
    show st'.regs rTmp2 = UInt64.ofNat (h + 1)
    simp only [st', st0, upd_self, toMState]
    rw [hintEq]
    show UInt64.ofNat h + UInt64.ofNat 1 = UInt64.ofNat (h + 1)
    exact u64_ofNat_add (by omega)
  | help2 h hpc hp =>
    have h64 : h < 2 ^ 64 := by
      have h1 : h ≤ s.w := hp.hintLe
      have h2 : s.w ≤ s.W := hi.hw_le
      have h3 : s.W ≤ limit := hi.hlimit
      have h4 : limit < 2 ^ 63 := hbound
      omega
    have h2h1 : h + 1 < 2 ^ 64 := by
      have h1 : h ≤ s.w := hp.hintLe
      have h2 : s.w ≤ s.W := hi.hw_le
      have h3 : s.W ≤ limit := hi.hlimit
      have h4 : limit < 2 ^ 63 := hbound
      omega
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
        ⟨rfl, rfl⟩, PushInv.help3 rfl, ?_, Or.inl ⟨.helpW, .helped, hev⟩⟩
      have href : Ref 0 C { s with w := s.w + 1 } (Shared.toMem (sh.after st')) :=
        EventStep.ref hev
      exact SharedRef.after_shared hs href
    · let st1 : MState := { toMState sh loc with regs := upd (toMState sh loc).regs rOk 0 }
      have hst : opStep pushProgram 7 1 (toMState sh loc) = .running 7 2 st1 := by
        simp [opStep, pushProgram, execOp, eval, hsucc, st1]
      rw [hst] at hstep
      cases hstep
      exact ⟨s, sh, { loc.after st1 with phase := Phase.running 7 2 },
        ⟨rfl, rfl⟩, PushInv.help3 rfl, hs, Or.inr ⟨rfl, rfl⟩⟩
  | help3 hpc =>
    have hst : opStep pushProgram 7 2 (toMState sh loc) = .running 0 0 (toMState sh loc) := by
      simp [opStep, pushProgram]
    rw [hst] at hstep
    cases hstep
    exact ⟨s, sh, { loc.after (toMState sh loc) with phase := Phase.running 0 0 },
      ⟨rfl, rfl⟩, PushInv.entry rfl, hs, Or.inr ⟨rfl, rfl⟩⟩
  | exhausted hpc =>
    have hst : opStep pushProgram 9 0 (toMState sh loc) = .returned 3 (toMState sh loc) := by
      simp [opStep, pushProgram, eval]
    rw [hst] at hstep
    cases hstep
    exact ⟨s, sh, { loc.after (toMState sh loc) with phase := Phase.returned 3 },
      ⟨rfl, rfl⟩, PushInv.ret 3 rfl, hs, Or.inr ⟨rfl, rfl⟩⟩

/-! ## The pop local step

The same dispatch for the pop program.  The extra hypothesis `C ≤ 2^24`
is required by `popCas_event_of_success` as stated in `KernelClassify`
(it is not actually used in that proof, but it is part of its
interface). -/

theorem pop_local_step {C limit k : Nat} {s : AbsState UInt64} {sh : Shared} {loc : Local}
    {pc oi : Nat} {r : OpResult}
    (hi : Inv C limit s) (hs : SharedRef C limit s sh)
    (hC : 0 < C) (hpow : C = 2 ^ k) (hCmax : C ≤ 2 ^ 24) (hbound : limit < 2 ^ 63)
    (hlimitC : limit + C ≤ 2 ^ 63)
    (hphase : loc.phase = Phase.running pc oi)
    (hinv : PopInv C limit s sh loc (Phase.running pc oi))
    (hstep : opStep popProgram pc oi (toMState sh loc) = r) :
    ∃ (s' : AbsState UInt64) (sh' : Shared) (loc' : Local),
      After sh loc r sh' loc' ∧
      PopInv C limit s' sh' loc' loc'.phase ∧
      SharedRef C limit s' sh' ∧
      ((∃ a res, EventStep 0 C limit hC s (Shared.toMem sh) (some a) (some res) s' (Shared.toMem sh'))
        ∨ (s' = s ∧ sh' = sh)) := by
  cases hinv with
  | entry hpc =>
    have hst : opStep popProgram 0 0 (toMState sh loc) =
        .running 0 1 { toMState sh loc with
          regs := upd (toMState sh loc).regs rHint (toMState sh loc).hintR } := by
      simp [opStep, popProgram, execOp]
    rw [hst] at hstep
    cases hstep
    refine ⟨s, sh, { loc.after { toMState sh loc with
        regs := upd (toMState sh loc).regs rHint (toMState sh loc).hintR } with
      phase := Phase.running 0 1 }, ⟨rfl, rfl⟩, ?_, hs, Or.inr ⟨rfl, rfl⟩⟩
    refine PopInv.hint (h := sh.hintR.toNat) rfl ?_ ?_
    · show (upd (toMState sh loc).regs rHint (toMState sh loc).hintR) rHint =
        UInt64.ofNat sh.hintR.toNat
      rw [upd_self]
      exact (UInt64.ofNat_toNat (x := sh.hintR)).symm
    · show sh.hintR.toNat ≤ s.r
      exact Nat.le_of_eq hs.hr
  | hint h hpc hintEq hintLe =>
    have h64 : h < 2 ^ 64 := by
      have h1 : h ≤ s.r := hintLe
      have h2 : s.r ≤ s.R := hi.hr_le
      have h3 : s.R ≤ s.W := hi.hR_le_W
      have h4 : s.W ≤ limit := hi.hlimit
      omega
    have hlim64 : limit < 2 ^ 64 := by omega
    by_cases hlt : h < limit
    · have hcond : (toMState sh loc).regs rHint < (toMState sh loc).params.limit := by
        show loc.regs rHint < sh.params.limit
        rw [hintEq, hs.limit_eq]
        exact (u64_lt_ofNat_iff h64 hlim64).mpr hlt
      have hst : opStep popProgram 0 1 (toMState sh loc) = .running 1 0 (toMState sh loc) := by
        simp [opStep, popProgram, eval, hcond]
      rw [hst] at hstep
      cases hstep
      exact ⟨s, sh, { loc.after (toMState sh loc) with phase := Phase.running 1 0 },
        ⟨rfl, rfl⟩, PopInv.check h rfl hintEq hintLe hlt, hs, Or.inr ⟨rfl, rfl⟩⟩
    · have hcond : ¬ ((toMState sh loc).regs rHint < (toMState sh loc).params.limit) := by
        intro hc
        apply hlt
        have hc2 : UInt64.ofNat h < UInt64.ofNat limit := by
          have hcc := hc
          simp [toMState, hintEq, hs.limit_eq] at hcc
          exact hcc
        exact (u64_lt_ofNat_iff h64 hlim64).mp hc2
      have hst : opStep popProgram 0 1 (toMState sh loc) = .running 8 0 (toMState sh loc) := by
        simp [opStep, popProgram, eval, hcond]
      rw [hst] at hstep
      cases hstep
      exact ⟨s, sh, { loc.after (toMState sh loc) with phase := Phase.running 8 0 },
        ⟨rfl, rfl⟩, PopInv.exhausted rfl, hs, Or.inr ⟨rfl, rfl⟩⟩
  | check h hpc hintEq hintLe hlim =>
    have h64 : h < 2 ^ 64 := by
      have h1 : h ≤ s.r := hintLe
      have h2 : s.r ≤ s.R := hi.hr_le
      have h3 : s.R ≤ s.W := hi.hR_le_W
      have h4 : s.W ≤ limit := hi.hlimit
      omega
    have hC64 : C < 2 ^ 64 := by
      have h1 : limit < 2 ^ 63 := hbound
      omega
    let st0 := toMState sh loc
    let st' := { st0 with regs := upd (st0.regs) rSlot (st0.regs rHint &&& st0.params.mask) }
    have hst : opStep popProgram 1 0 (toMState sh loc) = .running 1 1 st' := by
      simp [opStep, popProgram, execOp, eval, st', st0]
    rw [hst] at hstep
    cases hstep
    refine ⟨s, sh, { loc.after st' with phase := Phase.running 1 1 },
      ⟨rfl, rfl⟩, ?_, hs, Or.inr ⟨rfl, rfl⟩⟩
    refine PopInv.slot h rfl hintEq hintLe hlim ?_
    show st'.regs rSlot = UInt64.ofNat (h % C)
    simp only [st', st0, upd_self, toMState]
    rw [hintEq, hs.mask_eq]
    exact u64_ofNat_and_mask hpow hC64 h64
  | slot h hpc hintEq hintLe hlim slotEq =>
    have h64 : h < 2 ^ 64 := by
      have h1 : h ≤ s.r := hintLe
      have h2 : s.r ≤ s.R := hi.hr_le
      have h3 : s.R ≤ s.W := hi.hR_le_W
      have h4 : s.W ≤ limit := hi.hlimit
      omega
    have hmodle : h % C ≤ h := Nat.mod_le h C
    have hmod64 : h % C < 2 ^ 64 := by omega
    have hslotNat : (loc.regs rSlot).toNat = h % C := by
      rw [slotEq]
      exact uint64_toNat_ofNat_of_lt hmod64
    let m := (sh.cells (h % C)).marker.toNat
    let st0 := toMState sh loc
    let regs1 := upd (st0.regs) rMarker (sh.cells (h % C)).marker
    let regs2 := upd regs1 rPayload (sh.cells (h % C)).payload
    let st' := { st0 with regs := regs2 }
    have hcellEq : (toMState sh loc).cells ((toMState sh loc).regs rSlot).toNat
        = sh.cells (h % C) := by
      show sh.cells (loc.regs rSlot).toNat = sh.cells (h % C)
      rw [hslotNat]
    have hst : opStep popProgram 1 1 (toMState sh loc) = .running 1 2 st' := by
      simp [opStep, popProgram, execOp, eval, st', st0, regs1, regs2, hcellEq]
    rw [hst] at hstep
    cases hstep
    have hcell : kcellToCell (sh.cells (h % C)) = viewCell 0 C s (h % C) :=
      hs.hcells (h % C) (Nat.mod_lt _ hC)
    have hdec := pop_load_dec (k := k) (sh := sh) hi hC h hintLe (c := sh.cells (h % C)) hcell
    have hmarkerVal : (sh.cells (h % C)).marker.toNat = (viewCell 0 C s (h % C)).marker := by
      have := congrArg Cell.marker hcell
      simpa [kcellToCell] using this
    have hqpos : m / 2 = slotPos s.R (h % C) C := by
      show (sh.cells (h % C)).marker.toNat / 2 = slotPos s.R (h % C) C
      rw [hmarkerVal]
      exact viewCell_pos 0 C s (h % C)
    have hq63 : m / 2 < 2 ^ 63 := by
      rw [hqpos]
      have hlt := slotPos_lt (R := s.R) (j := h % C) (C := C) (Nat.mod_lt _ hC)
      have h1 : s.R ≤ s.W := hi.hR_le_W
      have h2 : s.W ≤ limit := hi.hlimit
      omega
    refine ⟨s, sh, { loc.after st' with phase := Phase.running 1 2 },
      ⟨rfl, rfl⟩, ?_, hs, Or.inr ⟨rfl, rfl⟩⟩
    refine PopInv.load h m (m / 2) rfl hintEq hintLe hlim slotEq ?_ ?_ ?_ rfl hq63 ?_
    · show st'.regs rMarker = UInt64.ofNat m
      simp only [st', st0, regs1, regs2, upd_self]
      exact (UInt64.ofNat_toNat (x := (sh.cells (h % C)).marker)).symm
    · show m < 2 ^ 64
      exact UInt64.toNat_lt _
    · show m ≤ ((Shared.toMem sh).cells (h % C)).marker
      exact Nat.le_refl _
    · show h ≤ m / 2
      exact hdec.2.2
  | load h m q hpc hintEq hintLe hlim slotEq markerEq hm64 markerMono hq hq63 hle_q =>
    let st0 := toMState sh loc
    let st' := { st0 with regs := upd (st0.regs) rPos (st0.regs rMarker >>> (1 : UInt64)) }
    have hst : opStep popProgram 1 2 (toMState sh loc) = .running 1 3 st' := by
      simp [opStep, popProgram, execOp, eval, st', st0]
    rw [hst] at hstep
    cases hstep
    refine ⟨s, sh, { loc.after st' with phase := Phase.running 1 3 },
      ⟨rfl, rfl⟩, ?_, hs, Or.inr ⟨rfl, rfl⟩⟩
    refine PopInv.pos h m q rfl hintEq hintLe hlim slotEq markerEq hm64 markerMono ?_ hq hq63 hle_q
    show st'.regs rPos = UInt64.ofNat q
    simp only [st', st0, upd_self, toMState]
    rw [markerEq, hq]
    exact u64_ofNat_shr_one hm64
  | pos h m q hpc hintEq hintLe hlim slotEq markerEq hm64 markerMono posEq hq hq63 hle_q =>
    have h64 : h < 2 ^ 64 := by
      have h1 : h ≤ s.r := hintLe
      have h2 : s.r ≤ s.R := hi.hr_le
      have h3 : s.R ≤ s.W := hi.hR_le_W
      have h4 : s.W ≤ limit := hi.hlimit
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
      exact ⟨s, sh, { loc.after (toMState sh loc) with phase := Phase.running 2 0 },
        ⟨rfl, rfl⟩, PopInv.readyTest h m q rfl hintEq hintLe hlim slotEq markerEq markerMono posEq hq hq63 hle_q qh, hs, Or.inr ⟨rfl, rfl⟩⟩
    · have hne : (toMState sh loc).regs rPos ≠ (toMState sh loc).regs rHint := by
        show loc.regs rPos ≠ loc.regs rHint
        rw [posEq, hintEq]
        intro hc
        exact qh ((u64_eq_ofNat_iff hq64 h64).mp hc)
      have hst : opStep popProgram 1 3 (toMState sh loc) = .running 5 0 (toMState sh loc) := by
        simp [opStep, popProgram, eval, hne]
      rw [hst] at hstep
      cases hstep
      exact ⟨s, sh, { loc.after (toMState sh loc) with phase := Phase.running 5 0 },
        ⟨rfl, rfl⟩, PopInv.ahead h m q rfl hintEq hintLe hlim slotEq markerEq markerMono hq hq63 hle_q qh posEq, hs, Or.inr ⟨rfl, rfl⟩⟩
  | readyTest h m q hpc hintEq hintLe hlim slotEq markerEq markerMono posEq hq hq63 hle_q qeq =>
    let st0 := toMState sh loc
    let st' := { st0 with regs := upd (st0.regs) rTmp0 (st0.regs rMarker &&& (1 : UInt64)) }
    have hst : opStep popProgram 2 0 (toMState sh loc) = .running 2 1 st' := by
      simp [opStep, popProgram, execOp, eval, st', st0]
    rw [hst] at hstep
    cases hstep
    refine ⟨s, sh, { loc.after st' with phase := Phase.running 2 1 },
      ⟨rfl, rfl⟩, ?_, hs, Or.inr ⟨rfl, rfl⟩⟩
    refine PopInv.evenTest h m q rfl hintEq hintLe hlim slotEq markerEq markerMono posEq hq hq63 hle_q qeq ?_
    show st'.regs rTmp0 = UInt64.ofNat (m % 2)
    simp only [st', st0, upd_self, toMState]
    rw [markerEq]
    exact u64_ofNat_and_one m
  | evenTest h m q hpc hintEq hintLe hlim slotEq markerEq markerMono posEq hq hq63 hle_q qeq tmp0Eq =>
    have hm2 : m % 2 < 2 ^ 64 := by
      have := Nat.mod_lt m (by decide : 0 < 2)
      omega
    by_cases hpar : m % 2 = 0
    · have hcond : (toMState sh loc).regs rTmp0 = 0 := by
        show loc.regs rTmp0 = 0
        rw [tmp0Eq, u64_eq_zero_ofNat hm2, hpar]
      have hst : opStep popProgram 2 1 (toMState sh loc) = .running 3 0 (toMState sh loc) := by
        simp [opStep, popProgram, eval, hcond]
      rw [hst] at hstep
      cases hstep
      exact ⟨s, sh, { loc.after (toMState sh loc) with phase := Phase.running 3 0 },
        ⟨rfl, rfl⟩, PopInv.empty rfl, hs, Or.inr ⟨rfl, rfl⟩⟩
    · have hodd : m % 2 = 1 := by omega
      have hm_eq : m = 2 * h + 1 := by
        have hdm := Nat.div_add_mod m 2
        omega
      have hcond : ¬ ((toMState sh loc).regs rTmp0 = 0) := by
        show ¬ (loc.regs rTmp0 = 0)
        rw [tmp0Eq]
        intro hc
        exact hpar ((u64_eq_zero_ofNat hm2).mp hc)
      have hst : opStep popProgram 2 1 (toMState sh loc) = .running 7 0 (toMState sh loc) := by
        simp [opStep, popProgram, eval, hcond]
      rw [hst] at hstep
      cases hstep
      refine ⟨s, sh, { loc.after (toMState sh loc) with phase := Phase.running 7 0 },
        ⟨rfl, rfl⟩, ?_, hs, Or.inr ⟨rfl, rfl⟩⟩
      refine PopInv.cas0 h rfl hintEq hintLe hlim slotEq ?_
      show loc.regs rMarker = UInt64.ofNat (2 * h + 1)
      rw [markerEq, hm_eq]
  | empty hpc =>
    have hst : opStep popProgram 3 0 (toMState sh loc) = .returned 2 (toMState sh loc) := by
      simp [opStep, popProgram, eval]
    rw [hst] at hstep
    cases hstep
    exact ⟨s, sh, { loc.after (toMState sh loc) with phase := Phase.returned 2 },
      ⟨rfl, rfl⟩, PopInv.ret 2 rfl, hs, Or.inr ⟨rfl, rfl⟩⟩
  | cas0 h hpc hintEq hintLe hlim slotEq markerEq =>
    have h63 : h < 2 ^ 63 := by
      have h1 : h ≤ s.r := hintLe
      have h2 : s.r ≤ s.R := hi.hr_le
      have h3 : s.R ≤ s.W := hi.hR_le_W
      have h4 : s.W ≤ limit := hi.hlimit
      omega
    let st0 := toMState sh loc
    let v := ((st0.regs rHint + st0.params.capacity) <<< (1 : UInt64))
    let st' := { st0 with regs := upd (st0.regs) rTmp0 v }
    have hst : opStep popProgram 7 0 (toMState sh loc) = .running 7 1 st' := by
      simp [opStep, popProgram, execOp, eval, st', st0, v]
    rw [hst] at hstep
    cases hstep
    refine ⟨s, sh, { loc.after st' with phase := Phase.running 7 1 },
      ⟨rfl, rfl⟩, ?_, hs, Or.inr ⟨rfl, rfl⟩⟩
    refine PopInv.cas1 h rfl hintEq hintLe hlim slotEq markerEq ?_
    show st'.regs rTmp0 = UInt64.ofNat (2 * (h + C))
    simp only [st', st0, v, upd_self, toMState]
    rw [hintEq, hs.capacity_eq]
    rw [u64_ofNat_add (by omega)]
    show UInt64.ofNat (h + C) <<< (1 : UInt64) = UInt64.ofNat (2 * (h + C))
    exact u64_ofNat_shl_one (by omega)
  | cas1 h hpc hintEq hintLe hlim slotEq markerEq desMarker =>
    let st0 := toMState sh loc
    let st' := { st0 with regs := upd (st0.regs) rTmp1 (0 : UInt64) }
    have hst : opStep popProgram 7 1 (toMState sh loc) = .running 7 2 st' := by
      simp [opStep, popProgram, execOp, eval, st', st0]
    rw [hst] at hstep
    cases hstep
    refine ⟨s, sh, { loc.after st' with phase := Phase.running 7 2 },
      ⟨rfl, rfl⟩, ?_, hs, Or.inr ⟨rfl, rfl⟩⟩
    refine PopInv.cas h ⟨rfl, hintEq, hintLe, hlim, slotEq, markerEq, desMarker, ?_⟩
    show st'.regs rTmp1 = 0
    simp [st', st0, upd_self]
  | cas h hp =>
    by_cases hsucc : (toMState sh loc).cells ((toMState sh loc).regs rSlot).toNat =
        { marker := (toMState sh loc).regs rMarker, payload := (toMState sh loc).regs rPayload }
    · obtain ⟨st', hst', hev, hpay⟩ :=
        popCas_event_of_success (k := k) hi hs hC hCmax hbound hlimitC hp.hlim hp hsucc
      let cnew : KCell :=
        { marker := (toMState sh loc).regs rTmp0, payload := (toMState sh loc).regs rTmp1 }
      let st1 : MState := { toMState sh loc with
        cells := upd (toMState sh loc).cells ((toMState sh loc).regs rSlot).toNat cnew,
        regs := upd (toMState sh loc).regs rOk 1 }
      have hst1 : opStep popProgram 7 2 (toMState sh loc) = .running 7 3 st1 := by
        simp [opStep, popProgram, execOp, eval, hsucc, st1, cnew]
      rw [hst1] at hst'
      have hstEq : st' = st1 := by
        injection hst' with _ _ h
        exact h.symm
      rw [hst1] at hstep
      cases hstep
      subst hstEq
      have hmem := EventStep.pop_mem hev
      refine ⟨popState s, sh.after st1,
        { loc.after st1 with phase := Phase.running 7 3 },
        ⟨rfl, rfl⟩, ?_, ?_,
        Or.inl ⟨.pop, .popped h ((s.val h).getD 0), hev⟩⟩
      · refine PopInv.casOk h rfl ?_ hp.hintEq ?_ ?_
        · show st1.regs rOk ≠ 0
          simp [st1]
        · show h ≤ (popState s).r
          simpa [popState] using hp.hintLe
        · rw [hmem]
          simp [Mem.setCell, emptyCell]
          omega
      · have href : Ref 0 C (popState s) (Shared.toMem (sh.after st1)) :=
          EventStep.ref hev
        exact SharedRef.after_shared hs href
    · let st1 : MState := { toMState sh loc with regs := upd (toMState sh loc).regs rOk 0 }
      have hst1 : opStep popProgram 7 2 (toMState sh loc) = .running 7 3 st1 := by
        simp [opStep, popProgram, execOp, eval, hsucc, st1]
      rw [hst1] at hstep
      cases hstep
      refine ⟨s, sh, { loc.after st1 with phase := Phase.running 7 3 },
        ⟨rfl, rfl⟩, ?_, hs, Or.inr ⟨rfl, rfl⟩⟩
      refine PopInv.casFail rfl ?_
      show st1.regs rOk = 0
      simp [st1]
  | casFail hpc hok =>
    have hcond : (toMState sh loc).regs rOk = 0 := hok
    have hst : opStep popProgram 7 3 (toMState sh loc) = .running 0 0 (toMState sh loc) := by
      simp [opStep, popProgram, eval, hcond]
    rw [hst] at hstep
    cases hstep
    exact ⟨s, sh, { loc.after (toMState sh loc) with phase := Phase.running 0 0 },
      ⟨rfl, rfl⟩, PopInv.entry rfl, hs, Or.inr ⟨rfl, rfl⟩⟩
  | casOk h hpc hok hintEq hintLe hmark =>
    have hcond : ¬ ((toMState sh loc).regs rOk = 0) := hok
    have hst : opStep popProgram 7 3 (toMState sh loc) = .running 4 0 (toMState sh loc) := by
      simp [opStep, popProgram, eval, hcond]
    rw [hst] at hstep
    cases hstep
    exact ⟨s, sh, { loc.after (toMState sh loc) with phase := Phase.running 4 0 },
      ⟨rfl, rfl⟩, PopInv.out0 h rfl hintEq hintLe hmark, hs, Or.inr ⟨rfl, rfl⟩⟩
  | out0 h hpc hintEq hintLe hmark =>
    let st0 := toMState sh loc
    let st' := { st0 with out0 := st0.regs rPayload }
    have hst : opStep popProgram 4 0 (toMState sh loc) = .running 4 1 st' := by
      simp [opStep, popProgram, execOp, eval, st', st0]
    rw [hst] at hstep
    cases hstep
    exact ⟨s, sh, { loc.after st' with phase := Phase.running 4 1 },
      ⟨rfl, rfl⟩, PopInv.out1 h rfl hintEq hintLe hmark
        (by simp [Local.after, st', st0, toMState]), hs, Or.inr ⟨rfl, rfl⟩⟩
  | out1 h hpc hintEq hintLe hmark out0Eq =>
    let st0 := toMState sh loc
    let st' := { st0 with out1 := st0.regs rHint }
    have hst : opStep popProgram 4 1 (toMState sh loc) = .running 4 2 st' := by
      simp [opStep, popProgram, execOp, eval, st', st0]
    rw [hst] at hstep
    cases hstep
    exact ⟨s, sh, { loc.after st' with phase := Phase.running 4 2 },
      ⟨rfl, rfl⟩, PopInv.out2 h rfl hintEq hintLe hmark
        (by simpa [Local.after, st', st0, toMState] using out0Eq)
        (by simp [Local.after, st', st0, toMState]), hs, Or.inr ⟨rfl, rfl⟩⟩
  | out2 h hpc hintEq hintLe hmark out0Eq out1Eq =>
    have h2h1 : h + 1 < 2 ^ 64 := by
      have h1 : h ≤ s.r := hintLe
      have h2 : s.r ≤ s.R := hi.hr_le
      have h3 : s.R ≤ s.W := hi.hR_le_W
      have h4 : s.W ≤ limit := hi.hlimit
      have h5 : limit < 2 ^ 63 := hbound
      omega
    let st0 := toMState sh loc
    let st' := { st0 with regs := upd (st0.regs) rTmp2 (st0.regs rHint + (1 : UInt64)) }
    have hst : opStep popProgram 4 2 (toMState sh loc) = .running 4 3 st' := by
      simp [opStep, popProgram, execOp, eval, st', st0]
    rw [hst] at hstep
    cases hstep
    refine ⟨s, sh, { loc.after st' with phase := Phase.running 4 3 },
      ⟨rfl, rfl⟩, ?_, hs, Or.inr ⟨rfl, rfl⟩⟩
    refine PopInv.out3 h rfl ⟨hintEq, hintLe, hmark, ?_⟩
      (by simpa [Local.after, st', st0, upd, rHint, rTmp2, rPayload, rOk, toMState] using out0Eq)
      (by simpa [Local.after, st', st0, upd, rHint, rTmp2, rPayload, rOk, toMState] using out1Eq)
    show st'.regs rTmp2 = UInt64.ofNat (h + 1)
    simp only [st', st0, upd_self, toMState]
    rw [hintEq]
    show UInt64.ofNat h + UInt64.ofNat 1 = UInt64.ofNat (h + 1)
    exact u64_ofNat_add h2h1
  | out3 h hpc hp out0Eq out1Eq =>
    have h64 : h < 2 ^ 64 := by
      have h1 : h ≤ s.r := hp.hintLe
      have h2 : s.r ≤ s.R := hi.hr_le
      have h3 : s.R ≤ s.W := hi.hR_le_W
      have h4 : s.W ≤ limit := hi.hlimit
      omega
    have h2h1 : h + 1 < 2 ^ 64 := by
      have h1 : h ≤ s.r := hp.hintLe
      have h2 : s.r ≤ s.R := hi.hr_le
      have h3 : s.R ≤ s.W := hi.hR_le_W
      have h4 : s.W ≤ limit := hi.hlimit
      have h5 : limit < 2 ^ 63 := hbound
      omega
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
        ⟨rfl, rfl⟩, PopInv.out4 h rfl
          (by rw [← hexec]; simp only [Local.after]
              rw [execOp_casHint_regs_of_ne (by decide : rHint ≠ rOk)]
              simpa [toMState] using hp.hintReg)
          (by rw [← hexec]; simp only [Local.after]
              rw [execOp_casHint_out0, execOp_casHint_regs_of_ne (by decide : rPayload ≠ rOk)]
              simpa [toMState] using out0Eq)
          (by rw [← hexec]; simp only [Local.after]
              rw [execOp_casHint_out1, execOp_casHint_regs_of_ne (by decide : rHint ≠ rOk)]
              simpa [toMState] using out1Eq),
        ?_, Or.inl ⟨.helpR, .helped, hev⟩⟩
      have href : Ref 0 C { s with r := s.r + 1 } (Shared.toMem (sh.after st')) :=
        EventStep.ref hev
      exact SharedRef.after_shared hs href
    · let st1 : MState := { toMState sh loc with regs := upd (toMState sh loc).regs rOk 0 }
      have hst : opStep popProgram 4 3 (toMState sh loc) = .running 4 4 st1 := by
        simp [opStep, popProgram, execOp, eval, hsucc, st1]
      rw [hst] at hstep
      cases hstep
      exact ⟨s, sh, { loc.after st1 with phase := Phase.running 4 4 },
        ⟨rfl, rfl⟩, PopInv.out4 h rfl
          (by simpa [Local.after, st1, toMState, upd, rHint, rOk] using hp.hintReg)
          (by simpa [Local.after, st1, toMState, upd, rHint, rOk, rPayload, rTmp2] using out0Eq)
          (by simpa [Local.after, st1, toMState, upd, rHint, rOk, rPayload, rTmp2] using out1Eq),
        hs, Or.inr ⟨rfl, rfl⟩⟩
  | out4 h hpc hintEq out0Eq out1Eq =>
    have hst : opStep popProgram 4 4 (toMState sh loc) = .returned 0 (toMState sh loc) := by
      simp [opStep, popProgram, eval]
    rw [hst] at hstep
    cases hstep
    exact ⟨s, sh, { loc.after (toMState sh loc) with phase := Phase.returned 0 },
      ⟨rfl, rfl⟩, PopInv.ret 0 rfl, hs, Or.inr ⟨rfl, rfl⟩⟩
  | ahead h m q hpc hintEq hintLe hlim slotEq markerEq markerMono hq hq63 hle_q qne posEq =>
    have h64 : h < 2 ^ 64 := by
      have h1 : h ≤ s.r := hintLe
      have h2 : s.r ≤ s.R := hi.hr_le
      have h3 : s.R ≤ s.W := hi.hR_le_W
      have h4 : s.W ≤ limit := hi.hlimit
      omega
    have hq64 : q < 2 ^ 64 := by omega
    let st0 := toMState sh loc
    let st' := { st0 with regs := upd (st0.regs) rPos (st0.regs rPos - st0.regs rHint) }
    have hst : opStep popProgram 5 0 (toMState sh loc) = .running 5 1 st' := by
      simp [opStep, popProgram, execOp, eval, st', st0]
    rw [hst] at hstep
    cases hstep
    refine ⟨s, sh, { loc.after st' with phase := Phase.running 5 1 },
      ⟨rfl, rfl⟩, ?_, hs, Or.inr ⟨rfl, rfl⟩⟩
    refine PopInv.ahead1 h m q rfl hintEq hintLe hlim slotEq markerEq markerMono hq hq63 hle_q qne ?_
    show st'.regs rPos = UInt64.ofNat (q - h)
    simp only [st', st0, upd_self, toMState]
    rw [posEq, hintEq]
    exact u64_ofNat_sub hle_q hq64
  | ahead1 h m q hpc hintEq hintLe hlim slotEq markerEq markerMono hq hq63 hle_q qne posEq =>
    have hq64 : q < 2 ^ 64 := by omega
    have hcond : (toMState sh loc).regs rPos < (half : UInt64) := by
      show loc.regs rPos < UInt64.ofNat (2 ^ 63)
      rw [posEq]
      exact (u64_lt_ofNat_iff (by omega : q - h < 2 ^ 64) (by decide : 2 ^ 63 < 2 ^ 64)).mpr (by omega)
    have hmark : 2 * h + 1 < ((Shared.toMem sh).cells (h % C)).marker := by
      have hm := markerMono
      have h2q : 2 * q ≤ m := by
        rw [hq, Nat.mul_comm]
        exact Nat.div_mul_le_self m 2
      omega
    have hst : opStep popProgram 5 1 (toMState sh loc) = .running 6 0 (toMState sh loc) := by
      simp [opStep, popProgram, eval, hcond]
    rw [hst] at hstep
    cases hstep
    exact ⟨s, sh, { loc.after (toMState sh loc) with phase := Phase.running 6 0 },
      ⟨rfl, rfl⟩, PopInv.help0 h rfl hintEq hintLe hmark, hs, Or.inr ⟨rfl, rfl⟩⟩
  | help0 h hpc hintEq hintLe hmark =>
    have h2h1 : h + 1 < 2 ^ 64 := by
      have h1 : h ≤ s.r := hintLe
      have h2 : s.r ≤ s.R := hi.hr_le
      have h3 : s.R ≤ s.W := hi.hR_le_W
      have h4 : s.W ≤ limit := hi.hlimit
      have h5 : limit < 2 ^ 63 := hbound
      omega
    let st0 := toMState sh loc
    let st' := { st0 with regs := upd (st0.regs) rTmp2 (st0.regs rHint + (1 : UInt64)) }
    have hst : opStep popProgram 6 0 (toMState sh loc) = .running 6 1 st' := by
      simp [opStep, popProgram, execOp, eval, st', st0]
    rw [hst] at hstep
    cases hstep
    refine ⟨s, sh, { loc.after st' with phase := Phase.running 6 1 },
      ⟨rfl, rfl⟩, ?_, hs, Or.inr ⟨rfl, rfl⟩⟩
    refine PopInv.help1 h rfl ⟨hintEq, hintLe, hmark, ?_⟩
    show st'.regs rTmp2 = UInt64.ofNat (h + 1)
    simp only [st', st0, upd_self, toMState]
    rw [hintEq]
    show UInt64.ofNat h + UInt64.ofNat 1 = UInt64.ofNat (h + 1)
    exact u64_ofNat_add h2h1
  | help1 h hpc hp =>
    have h64 : h < 2 ^ 64 := by
      have h1 : h ≤ s.r := hp.hintLe
      have h2 : s.r ≤ s.R := hi.hr_le
      have h3 : s.R ≤ s.W := hi.hR_le_W
      have h4 : s.W ≤ limit := hi.hlimit
      omega
    have h2h1 : h + 1 < 2 ^ 64 := by
      have h1 : h ≤ s.r := hp.hintLe
      have h2 : s.r ≤ s.R := hi.hr_le
      have h3 : s.R ≤ s.W := hi.hR_le_W
      have h4 : s.W ≤ limit := hi.hlimit
      have h5 : limit < 2 ^ 63 := hbound
      omega
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
        ⟨rfl, rfl⟩, PopInv.help2 rfl, ?_, Or.inl ⟨.helpR, .helped, hev⟩⟩
      have href : Ref 0 C { s with r := s.r + 1 } (Shared.toMem (sh.after st')) :=
        EventStep.ref hev
      exact SharedRef.after_shared hs href
    · let st1 : MState := { toMState sh loc with regs := upd (toMState sh loc).regs rOk 0 }
      have hst : opStep popProgram 6 1 (toMState sh loc) = .running 6 2 st1 := by
        simp [opStep, popProgram, execOp, eval, hsucc, st1]
      rw [hst] at hstep
      cases hstep
      exact ⟨s, sh, { loc.after st1 with phase := Phase.running 6 2 },
        ⟨rfl, rfl⟩, PopInv.help2 rfl, hs, Or.inr ⟨rfl, rfl⟩⟩
  | help2 hpc =>
    have hst : opStep popProgram 6 2 (toMState sh loc) = .running 0 0 (toMState sh loc) := by
      simp [opStep, popProgram]
    rw [hst] at hstep
    cases hstep
    exact ⟨s, sh, { loc.after (toMState sh loc) with phase := Phase.running 0 0 },
      ⟨rfl, rfl⟩, PopInv.entry rfl, hs, Or.inr ⟨rfl, rfl⟩⟩
  | exhausted hpc =>
    have hst : opStep popProgram 8 0 (toMState sh loc) = .returned 3 (toMState sh loc) := by
      simp [opStep, popProgram, eval]
    rw [hst] at hstep
    cases hstep
    exact ⟨s, sh, { loc.after (toMState sh loc) with phase := Phase.returned 3 },
      ⟨rfl, rfl⟩, PopInv.ret 3 rfl, hs, Or.inr ⟨rfl, rfl⟩⟩

/-! ## Monotonicity under interference

The stage invariants depend on the shared state only through `s.w`, `s.r`
and the cell markers.  All three grow along an `EventStep`, so a thread
that does not move keeps its invariant while other threads act. -/

theorem PushInv.mono {C limit : Nat} {s s' : AbsState UInt64} {sh sh' : Shared}
    {loc : Local} {pc oi : Nat}
    (h : PushInv C limit s sh loc (Phase.running pc oi))
    (hw : s.w ≤ s'.w)
    (hm : ∀ j, ((Shared.toMem sh).cells j).marker ≤ ((Shared.toMem sh').cells j).marker) :
    PushInv C limit s' sh' loc (Phase.running pc oi) := by
  cases h with
  | entry hpc => exact PushInv.entry hpc
  | hint h hpc hintEq hintLe =>
      exact PushInv.hint h hpc hintEq (Nat.le_trans hintLe hw)
  | check h hpc hintEq hintLe hlim =>
      exact PushInv.check h hpc hintEq (Nat.le_trans hintLe hw) hlim
  | slot h hpc hintEq hintLe hlim slotEq =>
      exact PushInv.slot h hpc hintEq (Nat.le_trans hintLe hw) hlim slotEq
  | load h m q hpc hintEq hintLe hlim slotEq markerEq hm64 markerMono hq hq63 hfull =>
      exact PushInv.load h m q hpc hintEq (Nat.le_trans hintLe hw) hlim slotEq markerEq hm64
        (Nat.le_trans markerMono (hm (h % C))) hq hq63 hfull
  | pos h m q hpc hintEq hintLe hlim slotEq markerEq markerMono posEq hq hq63 hfull =>
      exact PushInv.pos h m q hpc hintEq (Nat.le_trans hintLe hw) hlim slotEq markerEq
        (Nat.le_trans markerMono (hm (h % C))) posEq hq hq63 hfull
  | readyTest h m q hpc hintEq hintLe hlim slotEq markerEq markerMono posEq hq hq63 hfull qeq =>
      exact PushInv.readyTest h m q hpc hintEq (Nat.le_trans hintLe hw) hlim slotEq markerEq
        (Nat.le_trans markerMono (hm (h % C))) posEq hq hq63 hfull qeq
  | evenTest h m q hpc hintEq hintLe hlim slotEq markerEq markerMono posEq hq hq63 hfull qeq tmp0Eq =>
      exact PushInv.evenTest h m q hpc hintEq (Nat.le_trans hintLe hw) hlim slotEq markerEq
        (Nat.le_trans markerMono (hm (h % C))) posEq hq hq63 hfull qeq tmp0Eq
  | cas0 h m q hpc hintEq hintLe hlim slotEq markerEq markerMono posEq hq hq63 hfull qeq heven =>
      exact PushInv.cas0 h m q hpc hintEq (Nat.le_trans hintLe hw) hlim slotEq markerEq
        (Nat.le_trans markerMono (hm (h % C))) posEq hq hq63 hfull qeq heven
  | cas1 h hpc hintEq hintLe hlim slotEq markerEq desMarker =>
      exact PushInv.cas1 h hpc hintEq (Nat.le_trans hintLe hw) hlim slotEq markerEq desMarker
  | cas h hp =>
      exact PushInv.cas h ⟨hp.hpc, hp.hintEq, Nat.le_trans hp.hintLe hw, hp.hlim,
        hp.slotEq, hp.markerEq, hp.desMarker, hp.desPayload⟩
  | casFail hpc hok => exact PushInv.casFail hpc hok
  | casOk h hpc hok hintEq hintLe hmark =>
      exact PushInv.casOk h hpc hok hintEq (Nat.le_trans hintLe hw)
        (Nat.le_trans hmark (hm (h % C)))
  | hintPath0 h hpc hintEq hintLe hmark =>
      exact PushInv.hintPath0 h hpc hintEq (Nat.le_trans hintLe hw)
        (Nat.le_trans hmark (hm (h % C)))
  | hintPath1 h hpc hintEq hintLe hmark outEq =>
      exact PushInv.hintPath1 h hpc hintEq (Nat.le_trans hintLe hw)
        (Nat.le_trans hmark (hm (h % C))) outEq
  | hintPath2 h hpc hp outEq =>
      exact PushInv.hintPath2 h hpc ⟨hp.hintReg, Nat.le_trans hp.hintLe hw,
        Nat.le_trans hp.hmark (hm (h % C)), hp.desHint⟩ outEq
  | hintPath3 h hpc hintEq outEq => exact PushInv.hintPath3 h hpc hintEq outEq
  | fullAhead h m q hpc hintEq hintLe hlim slotEq markerEq hq hfull hqC posEq =>
      exact PushInv.fullAhead h m q hpc hintEq (Nat.le_trans hintLe hw) hlim slotEq markerEq
        hq hfull hqC posEq
  | fullAhead1 h m q hpc hintEq hintLe hlim slotEq markerEq hq hfull hqC posEq =>
      exact PushInv.fullAhead1 h m q hpc hintEq (Nat.le_trans hintLe hw) hlim slotEq markerEq
        hq hfull hqC posEq
  | ahead h m q hpc hintEq hintLe hlim slotEq markerEq markerMono hq hq63 hfull hltq posEq =>
      exact PushInv.ahead h m q hpc hintEq (Nat.le_trans hintLe hw) hlim slotEq markerEq
        (Nat.le_trans markerMono (hm (h % C))) hq hq63 hfull hltq posEq
  | ahead1 h m q hpc hintEq hintLe hlim slotEq markerEq markerMono hq hq63 hltq posEq =>
      exact PushInv.ahead1 h m q hpc hintEq (Nat.le_trans hintLe hw) hlim slotEq markerEq
        (Nat.le_trans markerMono (hm (h % C))) hq hq63 hltq posEq
  | full hpc => exact PushInv.full hpc
  | help0 h m q hpc hintEq hintLe markerEq markerMono hq hq63 hltq posEq =>
      exact PushInv.help0 h m q hpc hintEq (Nat.le_trans hintLe hw) markerEq
        (Nat.le_trans markerMono (hm (h % C))) hq hq63 hltq posEq
  | help1 h hpc hintEq hintLe hmark =>
      exact PushInv.help1 h hpc hintEq (Nat.le_trans hintLe hw)
        (Nat.le_trans hmark (hm (h % C)))
  | help2 h hpc hp =>
      exact PushInv.help2 h hpc ⟨hp.hintReg, Nat.le_trans hp.hintLe hw,
        Nat.le_trans hp.hmark (hm (h % C)), hp.desHint⟩
  | help3 hpc => exact PushInv.help3 hpc
  | exhausted hpc => exact PushInv.exhausted hpc

theorem PopInv.mono {C limit : Nat} {s s' : AbsState UInt64} {sh sh' : Shared}
    {loc : Local} {pc oi : Nat}
    (h : PopInv C limit s sh loc (Phase.running pc oi))
    (hr : s.r ≤ s'.r)
    (hm : ∀ j, ((Shared.toMem sh).cells j).marker ≤ ((Shared.toMem sh').cells j).marker) :
    PopInv C limit s' sh' loc (Phase.running pc oi) := by
  cases h with
  | entry hpc => exact PopInv.entry hpc
  | hint h hpc hintEq hintLe =>
      exact PopInv.hint h hpc hintEq (Nat.le_trans hintLe hr)
  | check h hpc hintEq hintLe hlim =>
      exact PopInv.check h hpc hintEq (Nat.le_trans hintLe hr) hlim
  | slot h hpc hintEq hintLe hlim slotEq =>
      exact PopInv.slot h hpc hintEq (Nat.le_trans hintLe hr) hlim slotEq
  | load h m q hpc hintEq hintLe hlim slotEq markerEq hm64 markerMono hq hq63 hle_q =>
      exact PopInv.load h m q hpc hintEq (Nat.le_trans hintLe hr) hlim slotEq markerEq hm64
        (Nat.le_trans markerMono (hm (h % C))) hq hq63 hle_q
  | pos h m q hpc hintEq hintLe hlim slotEq markerEq hm64 markerMono posEq hq hq63 hle_q =>
      exact PopInv.pos h m q hpc hintEq (Nat.le_trans hintLe hr) hlim slotEq markerEq hm64
        (Nat.le_trans markerMono (hm (h % C))) posEq hq hq63 hle_q
  | readyTest h m q hpc hintEq hintLe hlim slotEq markerEq markerMono posEq hq hq63 hle_q qeq =>
      exact PopInv.readyTest h m q hpc hintEq (Nat.le_trans hintLe hr) hlim slotEq markerEq
        (Nat.le_trans markerMono (hm (h % C))) posEq hq hq63 hle_q qeq
  | evenTest h m q hpc hintEq hintLe hlim slotEq markerEq markerMono posEq hq hq63 hle_q qeq tmp0Eq =>
      exact PopInv.evenTest h m q hpc hintEq (Nat.le_trans hintLe hr) hlim slotEq markerEq
        (Nat.le_trans markerMono (hm (h % C))) posEq hq hq63 hle_q qeq tmp0Eq
  | empty hpc => exact PopInv.empty hpc
  | cas0 h hpc hintEq hintLe hlim slotEq markerEq =>
      exact PopInv.cas0 h hpc hintEq (Nat.le_trans hintLe hr) hlim slotEq markerEq
  | cas1 h hpc hintEq hintLe hlim slotEq markerEq desMarker =>
      exact PopInv.cas1 h hpc hintEq (Nat.le_trans hintLe hr) hlim slotEq markerEq desMarker
  | cas h hp =>
      exact PopInv.cas h ⟨hp.hpc, hp.hintEq, Nat.le_trans hp.hintLe hr, hp.hlim,
        hp.slotEq, hp.markerEq, hp.desMarker, hp.desPayload⟩
  | casFail hpc hok => exact PopInv.casFail hpc hok
  | casOk h hpc hok hintEq hintLe hmark =>
      exact PopInv.casOk h hpc hok hintEq (Nat.le_trans hintLe hr)
        (Nat.le_trans hmark (hm (h % C)))
  | out0 h hpc hintEq hintLe hmark =>
      exact PopInv.out0 h hpc hintEq (Nat.le_trans hintLe hr)
        (Nat.le_trans hmark (hm (h % C)))
  | out1 h hpc hintEq hintLe hmark out0Eq =>
      exact PopInv.out1 h hpc hintEq (Nat.le_trans hintLe hr)
        (Nat.le_trans hmark (hm (h % C))) out0Eq
  | out2 h hpc hintEq hintLe hmark out0Eq out1Eq =>
      exact PopInv.out2 h hpc hintEq (Nat.le_trans hintLe hr)
        (Nat.le_trans hmark (hm (h % C))) out0Eq out1Eq
  | out3 h hpc hp out0Eq out1Eq =>
      exact PopInv.out3 h hpc ⟨hp.hintReg, Nat.le_trans hp.hintLe hr,
        Nat.le_trans hp.hmark (hm (h % C)), hp.desHint⟩ out0Eq out1Eq
  | out4 h hpc hintEq out0Eq out1Eq => exact PopInv.out4 h hpc hintEq out0Eq out1Eq
  | ahead h m q hpc hintEq hintLe hlim slotEq markerEq markerMono hq hq63 hle_q qne posEq =>
      exact PopInv.ahead h m q hpc hintEq (Nat.le_trans hintLe hr) hlim slotEq markerEq
        (Nat.le_trans markerMono (hm (h % C))) hq hq63 hle_q qne posEq
  | ahead1 h m q hpc hintEq hintLe hlim slotEq markerEq markerMono hq hq63 hle_q qne posEq =>
      exact PopInv.ahead1 h m q hpc hintEq (Nat.le_trans hintLe hr) hlim slotEq markerEq
        (Nat.le_trans markerMono (hm (h % C))) hq hq63 hle_q qne posEq
  | help0 h hpc hintEq hintLe hmark =>
      exact PopInv.help0 h hpc hintEq (Nat.le_trans hintLe hr)
        (Nat.le_trans hmark (hm (h % C)))
  | help1 h hpc hp =>
      exact PopInv.help1 h hpc ⟨hp.hintReg, Nat.le_trans hp.hintLe hr,
        Nat.le_trans hp.hmark (hm (h % C)), hp.desHint⟩
  | help2 hpc => exact PopInv.help2 hpc
  | exhausted hpc => exact PopInv.exhausted hpc

/-! ## The global refinement relation

A `GRef` bundles the shared refinement with the stage invariant of every
thread.  The per-thread invariant is selected by the thread's immutable
role. -/

/-- The stage invariant of one thread, selected by its role.  Returned and
trapped threads have no obligations. -/
def ThreadInv (C limit : Nat) (s : AbsState UInt64) (sh : Shared) (loc : Local)
    (k : Kind) : Prop :=
  match k with
  | .push =>
      match loc.phase with
      | .running pc oi => PushInv C limit s sh loc (.running pc oi)
      | .returned _ => True
      | .trapped => True
  | .pop =>
      match loc.phase with
      | .running pc oi => PopInv C limit s sh loc (.running pc oi)
      | .returned _ => True
      | .trapped => True

theorem ThreadInv.mono {C limit : Nat} {s s' : AbsState UInt64} {sh sh' : Shared}
    {loc : Local} {k : Kind}
    (h : ThreadInv C limit s sh loc k)
    (hw : s.w ≤ s'.w) (hr : s.r ≤ s'.r)
    (hm : ∀ j, ((Shared.toMem sh).cells j).marker ≤ ((Shared.toMem sh').cells j).marker) :
    ThreadInv C limit s' sh' loc k := by
  cases k with
  | push =>
      cases hp : loc.phase with
      | running pc oi =>
          have h' : PushInv C limit s sh loc (.running pc oi) := by
            simpa [ThreadInv, hp] using h
          simpa [ThreadInv, hp] using PushInv.mono h' hw hm
      | returned v => simp [ThreadInv, hp]
      | trapped => simp [ThreadInv, hp]
  | pop =>
      cases hp : loc.phase with
      | running pc oi =>
          have h' : PopInv C limit s sh loc (.running pc oi) := by
            simpa [ThreadInv, hp] using h
          simpa [ThreadInv, hp] using PopInv.mono h' hr hm
      | returned v => simp [ThreadInv, hp]
      | trapped => simp [ThreadInv, hp]

/-- Global refinement: the shared memory refines the abstract state and
every thread is at a legal stage. -/
structure GRef {n : Nat} (C limit : Nat) (kind : Fin n → Kind)
    (s : AbsState UInt64) (g : GState n) : Prop where
  hshared : SharedRef C limit s g.shared
  hlocal : ∀ i, ThreadInv C limit s g.shared (g.locals i) (kind i)

/-- The monotonicity facts supplied by one local step: either an event (all
three measures grow) or a stutter (they are unchanged). -/
theorem step_mono {C limit : Nat} {hC : 0 < C} {s s' : AbsState UInt64} {sh sh' : Shared}
    (h : (∃ a res : _,
            EventStep 0 C limit hC s (Shared.toMem sh) (some a) (some res) s' (Shared.toMem sh'))
          ∨ (s' = s ∧ sh' = sh)) :
    s.w ≤ s'.w ∧ s.r ≤ s'.r ∧
      ∀ j, ((Shared.toMem sh).cells j).marker ≤ ((Shared.toMem sh').cells j).marker := by
  rcases h with ⟨a, res, hev⟩ | ⟨rfl, rfl⟩
  · exact ⟨EventStep.w_mono hev, EventStep.r_mono hev,
      fun j => EventStep.cell_marker_mono hev j⟩
  · exact ⟨Nat.le_refl _, Nat.le_refl _, fun j => Nat.le_refl _⟩

/-- One global step simulates an abstract event (or a stutter) and preserves
the global refinement relation. -/
theorem gstep_sim {n C limit k : Nat} {kind : Fin n → Kind} {s : AbsState UInt64}
    {g g' : GState n} {i : Fin n}
    (hi : Inv C limit s) (hg : GRef C limit kind s g)
    (hC : 0 < C) (hpow : C = 2 ^ k) (hCmax : C ≤ 2 ^ 24)
    (hbound : limit < 2 ^ 63) (hlimitC : limit + C ≤ 2 ^ 63)
    (hstep : GStep kind g i g') :
    ∃ s' : AbsState UInt64,
      GRef C limit kind s' g' ∧
      ((∃ a res : _, EventStep 0 C limit hC s (Shared.toMem g.shared) (some a) (some res)
          s' (Shared.toMem g'.shared))
        ∨ (s' = s ∧ g'.shared = g.shared)) := by
  cases hk : kind i with
  | push =>
    cases hp : (g.locals i).phase with
    | running pc oi =>
      have hpinv : PushInv C limit s g.shared (g.locals i) (.running pc oi) := by
        have h1 := hg.hlocal i
        simp only [ThreadInv, hk, hp] at h1
        exact h1
      cases hr : opStep pushProgram pc oi (toMState g.shared (g.locals i)) with
      | running pc' oi' st' =>
        obtain ⟨s', sh', loc', hafter, hinv', hsh', hev⟩ :=
          push_local_step hi hg.hshared hC hpow hbound hlimitC hp hpinv hr
        obtain ⟨hshEq, hlocEq⟩ := hafter
        subst hshEq
        subst hlocEq
        have hmono := step_mono hev
        let newloc : Local := { (g.locals i).after st' with phase := Phase.running pc' oi' }
        have hg' : g' = { shared := g.shared.after st', locals := updLocal g.locals i newloc } := by
          have hs := hstep
          simp only [GStep, programOf, hk, hp, hr] at hs
          exact hs
        refine ⟨s', ?_, ?_⟩
        · constructor
          · rw [hg']; exact hsh'
          · intro j
            rw [hg']
            by_cases hj : j = i
            · subst hj
              simpa [ThreadInv, hk, newloc, updLocal] using hinv'
            · have hji : ¬ (j = i) := hj
              simp only [updLocal, if_neg hji]
              exact ThreadInv.mono (hg.hlocal j) hmono.1 hmono.2.1 hmono.2.2
        · rw [hg']
          exact hev
      | returned v st' =>
        obtain ⟨s', sh', loc', hafter, hinv', hsh', hev⟩ :=
          push_local_step hi hg.hshared hC hpow hbound hlimitC hp hpinv hr
        obtain ⟨hshEq, hlocEq⟩ := hafter
        subst hshEq
        subst hlocEq
        have hmono := step_mono hev
        let newloc : Local := { (g.locals i).after st' with phase := Phase.returned v }
        have hg' : g' = { shared := g.shared.after st', locals := updLocal g.locals i newloc } := by
          have hs := hstep
          simp only [GStep, programOf, hk, hp, hr] at hs
          exact hs
        refine ⟨s', ?_, ?_⟩
        · constructor
          · rw [hg']; exact hsh'
          · intro j
            rw [hg']
            by_cases hj : j = i
            · subst hj
              simpa [ThreadInv, hk, newloc, updLocal] using hinv'
            · have hji : ¬ (j = i) := hj
              simp only [updLocal, if_neg hji]
              exact ThreadInv.mono (hg.hlocal j) hmono.1 hmono.2.1 hmono.2.2
        · rw [hg']
          exact hev
      | trapped st' =>
        obtain ⟨s', sh', loc', hafter, hinv', hsh', hev⟩ :=
          push_local_step hi hg.hshared hC hpow hbound hlimitC hp hpinv hr
        obtain ⟨hshEq, hlocEq⟩ := hafter
        subst hshEq
        subst hlocEq
        have hmono := step_mono hev
        let newloc : Local := { (g.locals i).after st' with phase := Phase.trapped }
        have hg' : g' = { shared := g.shared.after st', locals := updLocal g.locals i newloc } := by
          have hs := hstep
          simp only [GStep, programOf, hk, hp, hr] at hs
          exact hs
        refine ⟨s', ?_, ?_⟩
        · constructor
          · rw [hg']; exact hsh'
          · intro j
            rw [hg']
            by_cases hj : j = i
            · subst hj
              simpa [ThreadInv, hk, newloc, updLocal] using hinv'
            · have hji : ¬ (j = i) := hj
              simp only [updLocal, if_neg hji]
              exact ThreadInv.mono (hg.hlocal j) hmono.1 hmono.2.1 hmono.2.2
        · rw [hg']
          exact hev
    | returned v =>
      have hs := hstep
      simp only [GStep, hk, hp] at hs
    | trapped =>
      have hs := hstep
      simp only [GStep, hk, hp] at hs
  | pop =>
    cases hp : (g.locals i).phase with
    | running pc oi =>
      have hpinv : PopInv C limit s g.shared (g.locals i) (.running pc oi) := by
        have h1 := hg.hlocal i
        simp only [ThreadInv, hk, hp] at h1
        exact h1
      cases hr : opStep popProgram pc oi (toMState g.shared (g.locals i)) with
      | running pc' oi' st' =>
        obtain ⟨s', sh', loc', hafter, hinv', hsh', hev⟩ :=
          pop_local_step hi hg.hshared hC hpow hCmax hbound hlimitC hp hpinv hr
        obtain ⟨hshEq, hlocEq⟩ := hafter
        subst hshEq
        subst hlocEq
        have hmono := step_mono hev
        let newloc : Local := { (g.locals i).after st' with phase := Phase.running pc' oi' }
        have hg' : g' = { shared := g.shared.after st', locals := updLocal g.locals i newloc } := by
          have hs := hstep
          simp only [GStep, programOf, hk, hp, hr] at hs
          exact hs
        refine ⟨s', ?_, ?_⟩
        · constructor
          · rw [hg']; exact hsh'
          · intro j
            rw [hg']
            by_cases hj : j = i
            · subst hj
              simpa [ThreadInv, hk, newloc, updLocal] using hinv'
            · have hji : ¬ (j = i) := hj
              simp only [updLocal, if_neg hji]
              exact ThreadInv.mono (hg.hlocal j) hmono.1 hmono.2.1 hmono.2.2
        · rw [hg']
          exact hev
      | returned v st' =>
        obtain ⟨s', sh', loc', hafter, hinv', hsh', hev⟩ :=
          pop_local_step hi hg.hshared hC hpow hCmax hbound hlimitC hp hpinv hr
        obtain ⟨hshEq, hlocEq⟩ := hafter
        subst hshEq
        subst hlocEq
        have hmono := step_mono hev
        let newloc : Local := { (g.locals i).after st' with phase := Phase.returned v }
        have hg' : g' = { shared := g.shared.after st', locals := updLocal g.locals i newloc } := by
          have hs := hstep
          simp only [GStep, programOf, hk, hp, hr] at hs
          exact hs
        refine ⟨s', ?_, ?_⟩
        · constructor
          · rw [hg']; exact hsh'
          · intro j
            rw [hg']
            by_cases hj : j = i
            · subst hj
              simpa [ThreadInv, hk, newloc, updLocal] using hinv'
            · have hji : ¬ (j = i) := hj
              simp only [updLocal, if_neg hji]
              exact ThreadInv.mono (hg.hlocal j) hmono.1 hmono.2.1 hmono.2.2
        · rw [hg']
          exact hev
      | trapped st' =>
        obtain ⟨s', sh', loc', hafter, hinv', hsh', hev⟩ :=
          pop_local_step hi hg.hshared hC hpow hCmax hbound hlimitC hp hpinv hr
        obtain ⟨hshEq, hlocEq⟩ := hafter
        subst hshEq
        subst hlocEq
        have hmono := step_mono hev
        let newloc : Local := { (g.locals i).after st' with phase := Phase.trapped }
        have hg' : g' = { shared := g.shared.after st', locals := updLocal g.locals i newloc } := by
          have hs := hstep
          simp only [GStep, programOf, hk, hp, hr] at hs
          exact hs
        refine ⟨s', ?_, ?_⟩
        · constructor
          · rw [hg']; exact hsh'
          · intro j
            rw [hg']
            by_cases hj : j = i
            · subst hj
              simpa [ThreadInv, hk, newloc, updLocal] using hinv'
            · have hji : ¬ (j = i) := hj
              simp only [updLocal, if_neg hji]
              exact ThreadInv.mono (hg.hlocal j) hmono.1 hmono.2.1 hmono.2.2
        · rw [hg']
          exact hev
    | returned v =>
      have hs := hstep
      simp only [GStep, hk, hp] at hs
    | trapped =>
      have hs := hstep
      simp only [GStep, hk, hp] at hs

/-! ## The retry fallback blocks are unreachable

The only branch that could enter the fallback block is the trailing-marker
test.  From the stage invariant its condition is always true, so the
program always takes the help branch. -/

theorem push_step8_running {C limit : Nat} {s : AbsState UInt64} {sh : Shared} {loc : Local}
    (hinv : PushInv C limit s sh loc (Phase.running 8 0)) :
    opStep pushProgram 8 0 (toMState sh loc) = .running 7 0 (toMState sh loc) := by
  cases hinv with
  | help0 h m q hpc hintEq hintLe markerEq markerMono hq hq63 hltq posEq =>
    have hcond : (half : UInt64) < (toMState sh loc).regs rPos := by
      show UInt64.ofNat (2 ^ 63) < loc.regs rPos
      rw [posEq]
      exact (u64_lt_ofNat_iff (by decide : 2 ^ 63 < 2 ^ 64)
        (by omega : 2 ^ 64 - (q - h) < 2 ^ 64)).mpr (by omega)
    simp [opStep, pushProgram, eval, hcond]

theorem pop_step5_running {C limit : Nat} {s : AbsState UInt64} {sh : Shared} {loc : Local}
    (hinv : PopInv C limit s sh loc (Phase.running 5 1)) :
    opStep popProgram 5 1 (toMState sh loc) = .running 6 0 (toMState sh loc) := by
  cases hinv with
  | ahead1 h m q hpc hintEq hintLe hlim slotEq markerEq markerMono hq hq63 hle_q qne posEq =>
    have hq64 : q < 2 ^ 64 := by omega
    have hcond : (toMState sh loc).regs rPos < (half : UInt64) := by
      show loc.regs rPos < UInt64.ofNat (2 ^ 63)
      rw [posEq]
      exact (u64_lt_ofNat_iff (by omega : q - h < 2 ^ 64)
        (by decide : 2 ^ 63 < 2 ^ 64)).mpr (by omega)
    simp [opStep, popProgram, eval, hcond]

end Mpmc
