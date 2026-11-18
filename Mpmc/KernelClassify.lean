/-
  Copyright (c) 2026 Mohammad Mahdi Abdollahpour.
  The contents of this file are subject to the Common Public Attribution
  License Version 1.0 (the "License"); you may not use this file except in
  compliance with the License. You may obtain a copy of the License at
  https://opensource.org/license/cpal-1-0.
  The Original Code is mpmc-lean. The Initial Developer is Mohammad Mahdi
  Abdollahpour. See LICENSE and NOTICE.
-/
import Mpmc.KernelConcurrent

namespace Mpmc

open Mpmc.Kernel

/-- With the same residue modulo `C`, a value at most one lap below `h` is
either `h - C` or at least `h`.  No upper bound is needed for stale hints. -/
theorem mod_eq_lower {C h sp : Nat} (hC : 0 < C)
    (hmod : sp % C = h % C) (hge : h - C ≤ sp) :
    sp = h - C ∨ h ≤ sp := by
  by_cases hsp : sp < h
  · left
    have hdvd : C ∣ h - sp :=
      Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq hmod.symm)
    have hsuble : h - sp ≤ C := by omega
    have hpos : 0 < h - sp := by omega
    have hgeC : C ≤ h - sp := Nat.le_of_dvd hpos hdvd
    omega
  · right
    exact Nat.le_of_not_lt hsp

/-- Classification of the push kernel's cell load.  The cell is the current
one, so this is the load-time (linearization-time) classification, not a
statement about a stale snapshot.  The three outcomes are exactly the three
routes taken by blocks 2/3/5/8. -/
theorem push_load_dec {C limit k : Nat} {s : AbsState UInt64} {sh : Shared}
    (hi : Inv C limit s) (hs : SharedRef C limit s sh) (hC : 0 < C)
    (hpow : C = 2 ^ k) (h : Nat) (hle : h ≤ s.w) {c : KCell}
    (hcell : kcellToCell c = viewCell 0 C s (h % C)) :
    (c.marker.toNat / 2 = h ∧ c.marker.toNat % 2 = 0 →
        c.payload = 0 ∧ s.W = h ∧ s.W - s.R < C) ∧
    (c.marker.toNat / 2 + C = h → s.W = h ∧ s.W - s.R = C) ∧
    (¬ (c.marker.toNat / 2 = h ∧ c.marker.toNat % 2 = 0) →
      ¬ (c.marker.toNat / 2 + C = h) → h ≤ c.marker.toNat / 2) := by
  let sp := slotPos s.R (h % C) C
  have hjC : h % C < C := Nat.mod_lt h hC
  have hspmod : sp % C = h % C := slotPos_mod (R := s.R) (j := h % C) (C := C) hjC
  have hspge : s.R ≤ sp := slotPos_ge (R := s.R) (j := h % C) (C := C) hC
  have hsplt : sp < s.R + C := slotPos_lt (R := s.R) (j := h % C) (C := C) hjC
  have hWR : s.W ≤ s.R + C := by
    have h := (Nat.sub_le_iff_le_add (a := s.W) (b := s.R) (c := C)).mp hi.hocc
    omega
  have hleW : h ≤ s.W := Nat.le_trans hle hi.hw_le
  have hspGe : h - C ≤ sp := by omega
  have hcases : sp = h - C ∨ h ≤ sp := mod_eq_lower hC hspmod hspGe
  by_cases hlt : sp < s.W
  · -- the current lap is full at `sp`
    have hcell' : kcellToCell c = fullCell sp ((s.val sp).getD 0) := by
      rw [hcell, viewCell, if_pos hlt]
    have hmarker : c.marker.toNat = 2 * sp + 1 := by
      have := congrArg Cell.marker hcell'
      simpa [kcellToCell, fullCell] using this
    have hq : c.marker.toNat / 2 = sp := by rw [hmarker]; omega
    constructor
    · intro hr
      have hodd : c.marker.toNat % 2 = 1 := by rw [hmarker]; omega
      omega
    constructor
    · intro hfull
      have hsp : sp = h - C := by omega
      have hRle : s.R ≤ h - C := by omega
      have hW : s.W = h := by
        by_cases hWh : s.W ≤ h
        · exact Nat.le_antisymm hWh hleW
        · have hWh' : h + 1 ≤ s.W := by omega
          have hhC : C ≤ h := by omega
          have hRleC : s.R + C ≤ (h - C) + C := Nat.add_le_add_right hRle C
          have hhsub : (h - C) + C = h := Nat.sub_add_cancel hhC
          omega
      have hocc : s.W - s.R = C := by
        have hRge : s.R ≥ h - C := by omega
        omega
      exact ⟨hW, hocc⟩
    · intro hnotready hnotfull
      rcases hcases with hsp | hsp
      · by_cases hCh : C ≤ h
        · have hqC : c.marker.toNat / 2 + C = h := by
            rw [hq, hsp]
            exact Nat.sub_add_cancel hCh
          exact (hnotfull hqC).elim
        · have hhlt : h < C := Nat.lt_of_not_le hCh
          have hh0 : h = 0 := by
            have hsub0 : h - C = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_lt hhlt)
            have hmod := hspmod
            rw [hsp, hsub0] at hmod
            simpa [Nat.mod_eq_of_lt hhlt] using hmod.symm
          omega
      · simpa [hq] using hsp
  · -- the current lap is empty at `sp`
    have hcell' : kcellToCell c = emptyCell 0 sp := by
      rw [hcell, viewCell, if_neg hlt]
    have hmarker : c.marker.toNat = 2 * sp := by
      have := congrArg Cell.marker hcell'
      simpa [kcellToCell, emptyCell] using this
    have hq : c.marker.toNat / 2 = sp := by rw [hmarker]; omega
    have hp : c.payload = 0 := by
      have := congrArg Cell.payload hcell'
      simpa [kcellToCell, emptyCell] using this
    constructor
    · intro hr
      have hsp : sp = h := by omega
      have hleW : h ≤ s.W := Nat.le_trans hle hi.hw_le
      have hW : s.W = h := by omega
      have hocc : s.W - s.R < C := by
        by_cases hfull : s.W - s.R = C
        · have hR : s.R = h - C := by omega
          have hhC : C ≤ h := by omega
          have hRmod : s.R % C = h % C := by
            have hsub : h % C = (h - C) % C :=
              Nat.mod_eq_sub_mod (a := h) (b := C) hhC
            rw [hR]
            exact hsub.symm
          have huniq : s.R = sp :=
            slotPos_unique (R := s.R) (j := h % C) (C := C) hC hjC
              (Nat.le_refl _) (by omega) hRmod
          omega
        · have hocc := hi.hocc
          omega
      exact ⟨hp, hW, hocc⟩
    constructor
    · intro hfull
      have hsp : sp = h - C := by omega
      have hleW : h ≤ s.W := Nat.le_trans hle hi.hw_le
      omega
    · intro hnotready hnotfull
      rcases hcases with hsp | hsp
      · by_cases hCh : C ≤ h
        · have hqC : c.marker.toNat / 2 + C = h := by
            rw [hq, hsp]
            exact Nat.sub_add_cancel hCh
          exact (hnotfull hqC).elim
        · have hhlt : h < C := Nat.lt_of_not_le hCh
          have hh0 : h = 0 := by
            have hsub0 : h - C = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_lt hhlt)
            have hmod := hspmod
            rw [hsp, hsub0] at hmod
            simpa [Nat.mod_eq_of_lt hhlt] using hmod.symm
          omega
      · simpa [hq] using hsp

/-- Classification of the pop kernel's cell load. -/
theorem pop_load_dec {C limit k : Nat} {s : AbsState UInt64} {sh : Shared}
    (hi : Inv C limit s) (hC : 0 < C) (h : Nat) (hle : h ≤ s.r)
    {c : KCell} (hcell : kcellToCell c = viewCell 0 C s (h % C)) :
    (c.marker.toNat / 2 = h ∧ c.marker.toNat % 2 = 1 →
        c.payload = (s.val h).getD 0 ∧ s.R = h ∧ h < s.W) ∧
    (c.marker.toNat / 2 = h ∧ c.marker.toNat % 2 = 0 → s.R = s.W) ∧
    h ≤ c.marker.toNat / 2 := by
  let sp := slotPos s.R (h % C) C
  have hjC : h % C < C := Nat.mod_lt h hC
  have hspmod : sp % C = h % C := slotPos_mod (R := s.R) (j := h % C) (C := C) hjC
  have hspge : s.R ≤ sp := slotPos_ge (R := s.R) (j := h % C) (C := C) hC
  have hsplt : sp < s.R + C := slotPos_lt (R := s.R) (j := h % C) (C := C) hjC
  have hRle : h ≤ s.R := Nat.le_trans hle hi.hr_le
  have hleSp : h ≤ sp := Nat.le_trans hRle hspge
  by_cases hlt : sp < s.W
  · have hcell' : kcellToCell c = fullCell sp ((s.val sp).getD 0) := by
      rw [hcell, viewCell, if_pos hlt]
    have hmarker : c.marker.toNat = 2 * sp + 1 := by
      have := congrArg Cell.marker hcell'
      simpa [kcellToCell, fullCell] using this
    have hq : c.marker.toNat / 2 = sp := by rw [hmarker]; omega
    constructor
    · intro hr
      have hsp : sp = h := by omega
      have hR : s.R = h := by omega
      have hltW : h < s.W := by omega
      have hp : c.payload = (s.val h).getD 0 := by
        have := congrArg Cell.payload hcell'
        simpa [kcellToCell, fullCell, hsp] using this
      exact ⟨hp, hR, hltW⟩
    constructor
    · intro hr
      have hodd : c.marker.toNat % 2 = 1 := by rw [hmarker]; omega
      omega
    · simpa [hq] using hleSp
  · have hcell' : kcellToCell c = emptyCell 0 sp := by
      rw [hcell, viewCell, if_neg hlt]
    have hmarker : c.marker.toNat = 2 * sp := by
      have := congrArg Cell.marker hcell'
      simpa [kcellToCell, emptyCell] using this
    have hq : c.marker.toNat / 2 = sp := by rw [hmarker]; omega
    constructor
    · intro hr
      have hodd : c.marker.toNat % 2 = 0 := by rw [hmarker]; omega
      omega
    constructor
    · intro hr
      have hsp : sp = h := by omega
      have hRleW : s.R ≤ s.W := hi.hR_le_W
      omega
    · simpa [hq] using hleSp

/-- Register shape immediately before the push cell CAS.  Unlike
`PushCasReady`, this does not assume the loaded snapshot still equals the
current cell: a failed CAS is a stutter, and a successful one supplies that
equality. -/
structure PushCasPre (C limit : Nat) (s : AbsState UInt64) (sh : Shared)
    (loc : Local) (h : Nat) : Prop where
  hpc : loc.phase = .running 3 2
  hintEq : loc.regs rHint = UInt64.ofNat h
  hintLe : h ≤ s.w
  hlim : h < limit
  slotEq : loc.regs rSlot = UInt64.ofNat (h % C)
  markerEq : loc.regs rMarker = UInt64.ofNat (2 * h)
  desMarker : loc.regs rTmp0 = UInt64.ofNat (2 * h + 1)
  desPayload : loc.regs rTmp1 = loc.value

/-- Register shape immediately before the pop cell CAS. -/
structure PopCasPre (C limit : Nat) (s : AbsState UInt64) (sh : Shared)
    (loc : Local) (h : Nat) : Prop where
  hpc : loc.phase = .running 7 2
  hintEq : loc.regs rHint = UInt64.ofNat h
  hintLe : h ≤ s.r
  hlim : h < limit
  slotEq : loc.regs rSlot = UInt64.ofNat (h % C)
  markerEq : loc.regs rMarker = UInt64.ofNat (2 * h + 1)
  desMarker : loc.regs rTmp0 = UInt64.ofNat (2 * (h + C))
  desPayload : loc.regs rTmp1 = 0

/-- Register shape immediately before a push hint CAS.  `hintEq` (the CAS
success condition) is supplied separately by the case split. -/
structure PushHintPre (C limit : Nat) (s : AbsState UInt64) (sh : Shared)
    (loc : Local) (h : Nat) : Prop where
  hintReg : loc.regs rHint = UInt64.ofNat h
  hintLe : h ≤ s.w
  hmark : 2 * h < ((Shared.toMem sh).cells (h % C)).marker
  desHint : loc.regs rTmp2 = UInt64.ofNat (h + 1)

/-- Register shape immediately before a pop hint CAS. -/
structure PopHintPre (C limit : Nat) (s : AbsState UInt64) (sh : Shared)
    (loc : Local) (h : Nat) : Prop where
  hintReg : loc.regs rHint = UInt64.ofNat h
  hintLe : h ≤ s.r
  hmark : 2 * h + 1 < ((Shared.toMem sh).cells (h % C)).marker
  desHint : loc.regs rTmp2 = UInt64.ofNat (h + 1)

/-- A successful push cell CAS is the abstract push event.  The success
equation is supplied by the caller; the load decoder converts it into the
`PushCasReady` shape. -/
theorem pushCas_event_of_success {C limit k : Nat} {s : AbsState UInt64}
    {sh : Shared} {loc : Local} {h : Nat}
    (hi : Inv C limit s) (hs : SharedRef C limit s sh) (hC : 0 < C)
    (hpow : C = 2 ^ k) (hbound : limit < 2 ^ 63) (hlim : h < limit)
    (hp : PushCasPre C limit s sh loc h)
    (hsuccess :
      (toMState sh loc).cells ((toMState sh loc).regs rSlot).toNat =
        { marker := (toMState sh loc).regs rMarker,
          payload := (toMState sh loc).regs rPayload }) :
    ∃ st', opStep pushProgram 3 2 (toMState sh loc) = .running 3 3 st' ∧
      EventStep 0 C limit hC s (Shared.toMem sh)
        (some (.push loc.value)) (some (.pushed h))
        (pushState s loc.value) (Shared.toMem (sh.after st')) := by
  have hmodle : h % C ≤ h := Nat.mod_le h C
  have hmodbound : h % C < 2 ^ 64 := Nat.lt_of_le_of_lt hmodle (by omega)
  have hslotNat : (loc.regs rSlot).toNat = h % C := by
    rw [hp.slotEq, uint64_toNat_ofNat_of_lt hmodbound]
  have h2h : 2 * h < 2 ^ 64 := by omega
  have hmarkerNat : (loc.regs rMarker).toNat = 2 * h := by
    rw [hp.markerEq, uint64_toNat_ofNat_of_lt h2h]
  have h2h1 : 2 * h + 1 < 2 ^ 64 := by omega
  have hsuccess' : sh.cells (h % C) = ⟨UInt64.ofNat (2 * h), loc.regs rPayload⟩ := by
    have := hsuccess
    simpa [toMState, hslotNat, hp.markerEq] using this
  have hview : kcellToCell (sh.cells (h % C)) = viewCell 0 C s (h % C) :=
    hs.hcells (h % C) (Nat.mod_lt _ hC)
  have hmarkerC : (sh.cells (h % C)).marker.toNat = 2 * h := by
    rw [hsuccess']
    exact uint64_toNat_ofNat_of_lt h2h
  have hq : (sh.cells (h % C)).marker.toNat / 2 = h := by
    rw [hmarkerC]
    omega
  have heven : (sh.cells (h % C)).marker.toNat % 2 = 0 := by
    rw [hmarkerC]
    omega
  have hdec := (push_load_dec (k := k) hi hs hC hpow h hp.hintLe
    (c := sh.cells (h % C)) hview).1 ⟨hq, heven⟩
  obtain ⟨hpayload, hW, hocc⟩ := hdec
  have hpayloadReg : loc.regs rPayload = 0 := by
    have := hpayload
    rw [hsuccess'] at this
    simpa using this
  have hcellEq : sh.cells (h % C) = ⟨UInt64.ofNat (2 * h), 0⟩ := by
    rw [hsuccess', hpayloadReg]
  exact pushCas_event hi hs hC (by omega) ⟨hp.hpc, hp.hintEq, hp.hintLe,
    hp.hlim, hp.slotEq, hp.markerEq, hpayloadReg, hp.desMarker,
    hp.desPayload, hcellEq⟩

/-- A successful pop cell CAS is the abstract pop event. -/
theorem popCas_event_of_success {C limit k : Nat} {s : AbsState UInt64}
    {sh : Shared} {loc : Local} {h : Nat}
    (hi : Inv C limit s) (hs : SharedRef C limit s sh) (hC : 0 < C)
    (hCmax : C ≤ 2 ^ 24) (hbound : limit < 2 ^ 63)
    (hlimitC : limit + C ≤ 2 ^ 63) (hlim : h < limit)
    (hp : PopCasPre C limit s sh loc h)
    (hsuccess :
      (toMState sh loc).cells ((toMState sh loc).regs rSlot).toNat =
        { marker := (toMState sh loc).regs rMarker,
          payload := (toMState sh loc).regs rPayload }) :
    ∃ st', opStep popProgram 7 2 (toMState sh loc) = .running 7 3 st' ∧
      EventStep 0 C limit hC s (Shared.toMem sh)
        (some .pop) (some (.popped h ((s.val h).getD 0)))
        (popState s) (Shared.toMem (sh.after st')) ∧
      loc.regs rPayload = (s.val h).getD 0 := by
  have hmodle : h % C ≤ h := Nat.mod_le h C
  have hmodbound : h % C < 2 ^ 64 := Nat.lt_of_le_of_lt hmodle (by omega)
  have hslotNat : (loc.regs rSlot).toNat = h % C := by
    rw [hp.slotEq, uint64_toNat_ofNat_of_lt hmodbound]
  have h2h1 : 2 * h + 1 < 2 ^ 64 := by omega
  have hmarkerNat : (loc.regs rMarker).toNat = 2 * h + 1 := by
    rw [hp.markerEq, uint64_toNat_ofNat_of_lt h2h1]
  have hsuccess' : sh.cells (h % C) =
      ⟨UInt64.ofNat (2 * h + 1), loc.regs rPayload⟩ := by
    have := hsuccess
    simpa [toMState, hslotNat, hp.markerEq] using this
  have hview : kcellToCell (sh.cells (h % C)) = viewCell 0 C s (h % C) :=
    hs.hcells (h % C) (Nat.mod_lt _ hC)
  have hmarkerC : (sh.cells (h % C)).marker.toNat = 2 * h + 1 := by
    rw [hsuccess']
    exact uint64_toNat_ofNat_of_lt h2h1
  have hq : (sh.cells (h % C)).marker.toNat / 2 = h := by
    rw [hmarkerC]
    omega
  have hodd : (sh.cells (h % C)).marker.toNat % 2 = 1 := by
    rw [hmarkerC]
    omega
  have hdec := (pop_load_dec (k := k) (sh := sh) hi hC h hp.hintLe
    (c := sh.cells (h % C)) hview).1 ⟨hq, hodd⟩
  obtain ⟨hpayload, hR, hlt⟩ := hdec
  have hpayloadReg : loc.regs rPayload = (s.val h).getD 0 := by
    simpa [hsuccess'] using hpayload
  have hcellEq : sh.cells (h % C) =
      ⟨UInt64.ofNat (2 * h + 1), (s.val h).getD 0⟩ := by
    rw [hsuccess', hpayloadReg]
  have h2h_bound : 2 * h + 1 < 2 ^ 64 := by omega
  have h2c_bound : 2 * (h + C) < 2 ^ 64 := by
    have hh : h + C < 2 ^ 63 := by omega
    omega
  obtain ⟨st', hstep, hev⟩ := popCas_event hi hs hC h2h_bound h2c_bound
    ⟨hp.hpc, hp.hintEq, hp.hintLe, hp.hlim, hp.slotEq, hp.markerEq,
      hpayloadReg, hp.desMarker, hp.desPayload, hcellEq⟩
  exact ⟨st', hstep, hev, hpayloadReg⟩

/-- A successful push hint CAS is the abstract `helpW` event. -/
theorem pushHint_event_of_success {C limit : Nat} {s : AbsState UInt64}
    {sh : Shared} {loc : Local} {h : Nat}
    (hi : Inv C limit s) (hs : SharedRef C limit s sh) (hC : 0 < C)
    (hp : PushHintPre C limit s sh loc h)
    (hintEq : sh.hintW.toNat = h) (h2h1 : h + 1 < 2 ^ 64) :
    ∃ st', execOp (.casHint rOk .write (.var rHint) (.var rTmp2) .release)
        (toMState sh loc) = st' ∧
      EventStep 0 C limit hC s (Shared.toMem sh)
        (some .helpW) (some .helped) { s with w := s.w + 1 }
        (Shared.toMem (sh.after st')) :=
  pushHint_event hi hs hC h2h1
    ⟨hintEq, hp.hintReg, hp.hintLe, hp.hmark, hp.desHint⟩

/-- A successful pop hint CAS is the abstract `helpR` event. -/
theorem popHint_event_of_success {C limit : Nat} {s : AbsState UInt64}
    {sh : Shared} {loc : Local} {h : Nat}
    (hi : Inv C limit s) (hs : SharedRef C limit s sh) (hC : 0 < C)
    (hp : PopHintPre C limit s sh loc h)
    (hintEq : sh.hintR.toNat = h) (h2h1 : h + 1 < 2 ^ 64) :
    ∃ st', execOp (.casHint rOk .read (.var rHint) (.var rTmp2) .release)
        (toMState sh loc) = st' ∧
      EventStep 0 C limit hC s (Shared.toMem sh)
        (some .helpR) (some .helped) { s with r := s.r + 1 }
        (Shared.toMem (sh.after st')) :=
  popHint_event hi hs hC h2h1
    ⟨hintEq, hp.hintReg, hp.hintLe, hp.hmark, hp.desHint⟩

end Mpmc
