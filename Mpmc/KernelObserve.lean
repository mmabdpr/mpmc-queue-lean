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
  Legal-failure guards at the classification point.

  A failed push/pop can be linearized at the cell load (or at the hint
  horizon test) even if the queue changes before the kernel returns.  These
  lemmas expose the abstract guard at exactly that point.
-/

import Mpmc.KernelSim

namespace Mpmc

open Mpmc.Kernel

/-- At a push cell load, a full snapshot for `h - C` certifies that the
queue is full at the load instant. -/
theorem push_slot_full_guard {C limit k : Nat} {s : AbsState UInt64} {sh : Shared}
    (hi : Inv C limit s) (hs : SharedRef C limit s sh)
    (hC : 0 < C) (hpow : C = 2 ^ k) {h : Nat}
    (hintLe : h ≤ s.w)
    (hq : (sh.cells (h % C)).marker.toNat / 2 + C = h) :
    s.W - s.R = C := by
  have hj : h % C < C := Nat.mod_lt h hC
  have hcell : kcellToCell (sh.cells (h % C)) = viewCell 0 C s (h % C) :=
    hs.hcells (h % C) hj
  exact ((push_load_dec hi hs hC hpow h hintLe hcell).2.1 hq).2

/-- At a pop cell load, an empty snapshot for `h` certifies that the queue
is empty at the load instant. -/
theorem pop_slot_empty_guard {C limit k : Nat} {s : AbsState UInt64} {sh : Shared}
    (hi : Inv C limit s) (hs : SharedRef C limit s sh)
    (hC : 0 < C) (hpow : C = 2 ^ k) {h : Nat}
    (hintLe : h ≤ s.r)
    (hq : (sh.cells (h % C)).marker.toNat / 2 = h)
    (heven : (sh.cells (h % C)).marker.toNat % 2 = 0) :
    s.R = s.W := by
  have hj : h % C < C := Nat.mod_lt h hC
  have hcell : kcellToCell (sh.cells (h % C)) = viewCell 0 C s (h % C) :=
    hs.hcells (h % C) hj
  exact (pop_load_dec (sh := sh) (k := k) hi hC h hintLe (c := sh.cells (h % C)) hcell).2.1 ⟨hq, heven⟩

/-- A push hint at or beyond the horizon certifies publication exhaustion at
the hint test instant. -/
theorem push_hint_exhausted_guard {C limit : Nat} {s : AbsState UInt64}
    (hi : Inv C limit s) {h : Nat}
    (hintLe : h ≤ s.w) (hge : limit ≤ h) :
    s.W = limit := by
  have hle := hi.hw_le
  have hlim := hi.hlimit
  omega

/-- A pop hint at or beyond the horizon certifies consumption exhaustion at
the hint test instant. -/
theorem pop_hint_exhausted_guard {C limit : Nat} {s : AbsState UInt64}
    (hi : Inv C limit s) {h : Nat}
    (hintLe : h ≤ s.r) (hge : limit ≤ h) :
    s.R = limit := by
  have hle := hi.hr_le
  have hRle := hi.hR_le_W
  have hlim := hi.hlimit
  omega

end Mpmc
