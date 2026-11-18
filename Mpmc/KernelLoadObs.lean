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
  A legal failed-push observation at the cell load.

  Consider a push thread whose next kernel step is the cell load of block 1
  (`Phase.running 1 1`).  The load only writes the thread's registers, so the
  shared state does not change.  If the loaded snapshot is the full marker
  for the thread's hint, `m / 2 + C = h`, then the queue is full at that
  instant (`push_slot_full_guard`), and the load step is a legal place to
  linearize the failed push: the step has the tagged effect `.obs .pushFull`
  and leaves both the abstract state and the shared memory unchanged.

  The main result is `push_load_full_effect`.  It is the observation
  companion of `push_local_step` / `gstep_sim`: those produce plain stutters,
  this one refines the load stutter to the failure observation the history
  construction needs.
-/

import Mpmc.Effect

namespace Mpmc

open Mpmc.Kernel

/-- At the push cell load (`running 1 1`), a full loaded marker for the
thread's hint yields an `.obs .pushFull` tagged effect.  The load step leaves
the abstract state and the shared memory unchanged, and it preserves the
global refinement relation.

`hfull` is stated in terms of the thread's own registers so that the caller
does not need to know the hint `h`: the loaded cell is
`g.shared.cells ((g.locals i).regs rSlot).toNat`, and `h` is the value of
`(g.locals i).regs rHint` (recovered below from `PushInv.slot`). -/
theorem push_load_full_effect {n C limit k : Nat} {kind : Fin n → Kind}
    {s : AbsState UInt64} {g g' : GState n} {i : Fin n}
    (hi : Inv C limit s) (hg : GRef C limit kind s g)
    (hC : 0 < C) (hpow : C = 2 ^ k) (hCmax : C ≤ 2 ^ 24)
    (hbound : limit < 2 ^ 63) (hlimitC : limit + C ≤ 2 ^ 63)
    (hk : kind i = .push)
    (hp : (g.locals i).phase = Phase.running 1 1)
    (hstep : GStep kind g i g')
    (hfull : (g.shared.cells (((g.locals i).regs rSlot).toNat)).marker.toNat / 2 + C
      = ((g.locals i).regs rHint).toNat) :
    ∃ (s' : AbsState UInt64) (tag : StepTag UInt64),
      GRef C limit kind s' g' ∧ Inv C limit s' ∧
      Effect 0 C limit hC s (Shared.toMem g.shared) s' (Shared.toMem g'.shared) tag ∧
      tag = .obs .pushFull := by
  -- The stage invariant at the load point is `PushInv.slot`; recover the hint.
  have hpinv : PushInv C limit s g.shared (g.locals i) (Phase.running 1 1) := by
    have h1 := hg.hlocal i
    simp only [ThreadInv, hk, hp] at h1
    exact h1
  cases hpinv with
  | slot h hpc hintEq hintLe hlim slotEq =>
    -- Bounds needed to move the register equations to `Nat`.
    have h64 : h < 2 ^ 64 := by
      have hb := hbound
      have h1 := hi.hlimit
      omega
    have hmod64 : h % C < 2 ^ 64 := by
      have := Nat.mod_lt h hC
      omega
    have hslotNat : ((g.locals i).regs rSlot).toNat = h % C := by
      rw [slotEq]
      exact uint64_toNat_ofNat_of_lt hmod64
    -- The external full hypothesis, in terms of the hint `h`.
    have hfullH : (g.shared.cells (h % C)).marker.toNat / 2 + C = h := by
      have h1 := hfull
      rw [hslotNat] at h1
      rw [hintEq, uint64_toNat_ofNat_of_lt h64] at h1
      exact h1
    -- The load step: only the marker and payload registers change.
    let st0 : MState := toMState g.shared (g.locals i)
    let regs1 : Nat → UInt64 := upd st0.regs rMarker (g.shared.cells (h % C)).marker
    let regs2 : Nat → UInt64 := upd regs1 rPayload (g.shared.cells (h % C)).payload
    let st' : MState := { st0 with regs := regs2 }
    have hcellEq : (toMState g.shared (g.locals i)).cells
        ((toMState g.shared (g.locals i)).regs rSlot).toNat = g.shared.cells (h % C) := by
      show g.shared.cells (((g.locals i).regs rSlot).toNat) = g.shared.cells (h % C)
      rw [hslotNat]
    have hst : opStep pushProgram 1 1 (toMState g.shared (g.locals i))
        = .running 1 2 st' := by
      simp [opStep, pushProgram, execOp, eval, st', st0, regs1, regs2, hcellEq]
    -- Read off the global step equation.
    let newloc : Local := { (g.locals i).after st' with phase := Phase.running 1 2 }
    have hg' : g' = { shared := g.shared.after st', locals := updLocal g.locals i newloc } := by
      have hs := hstep
      simp only [GStep, programOf, hk, hp, st0, hst] at hs
      exact hs
    -- The load does not touch the shared state.
    have hafter : g.shared.after st' = g.shared := by
      simp [Shared.after, st', st0, toMState]
    have hshared : g'.shared = g.shared := by
      rw [hg']
      exact hafter
    have hmem : Shared.toMem g'.shared = Shared.toMem g.shared := by
      rw [hshared]
    -- The next stage invariant: the loaded marker is full for `h`.
    have hqlt : (g.shared.cells (h % C)).marker.toNat / 2 < h := by omega
    have hq63 : (g.shared.cells (h % C)).marker.toNat / 2 < 2 ^ 63 := by
      have hw := hi.hw_le
      have hW := hi.hlimit
      omega
    have hloadInv : PushInv C limit s g.shared newloc (Phase.running 1 2) := by
      refine PushInv.load h ((g.shared.cells (h % C)).marker.toNat)
        ((g.shared.cells (h % C)).marker.toNat / 2) rfl hintEq hintLe hlim slotEq ?_ ?_ ?_ rfl hq63 ?_
      · show st'.regs rMarker = UInt64.ofNat ((g.shared.cells (h % C)).marker.toNat)
        exact (UInt64.ofNat_toNat (x := (g.shared.cells (h % C)).marker)).symm
      · show (g.shared.cells (h % C)).marker.toNat < 2 ^ 64
        exact UInt64.toNat_lt _
      · show (g.shared.cells (h % C)).marker.toNat
          ≤ ((Shared.toMem g.shared).cells (h % C)).marker
        exact Nat.le_refl _
      · intro _
        exact hfullH
    -- Rebuild the global refinement for the post-load state.
    have hgref' : GRef C limit kind s g' := by
      rw [hg', hafter]
      change GRef C limit kind s
        { shared := g.shared, locals := updLocal g.locals i newloc }
      constructor
      · exact hg.hshared
      · intro j
        change ThreadInv C limit s g.shared (updLocal g.locals i newloc j) (kind j)
        by_cases hj : j = i
        · subst hj
          have hloc : updLocal g.locals j newloc j = newloc := by simp [updLocal]
          rw [hloc]
          simpa [ThreadInv, hk, newloc] using hloadInv
        · have hloc : updLocal g.locals i newloc j = g.locals j := by
            simp [updLocal, hj]
          rw [hloc]
          exact hg.hlocal j
    -- The guard and the tagged observation.
    have hguard : ObsGuard C limit s .pushFull :=
      push_slot_full_guard hi hg.hshared hC hpow hintLe hfullH
    exact ⟨s, .obs .pushFull, hgref', hi,
      Effect.obs .pushFull (SharedRef.ref hg.hshared) hguard rfl hmem, rfl⟩

end Mpmc

namespace Mpmc

open Mpmc.Kernel

/-- At the pop cell load (`running 1 1`), an empty loaded marker for the
thread's hint yields a `.obs .popEmpty` tagged effect.  The load leaves the
abstract state and the shared memory unchanged. -/
theorem pop_load_empty_effect {n C limit k : Nat} {kind : Fin n → Kind}
    {s : AbsState UInt64} {g g' : GState n} {i : Fin n}
    (hi : Inv C limit s) (hg : GRef C limit kind s g)
    (hC : 0 < C) (hpow : C = 2 ^ k) (hCmax : C ≤ 2 ^ 24)
    (hbound : limit < 2 ^ 63) (hlimitC : limit + C ≤ 2 ^ 63)
    (hk : kind i = .pop)
    (hp : (g.locals i).phase = Phase.running 1 1)
    (hstep : GStep kind g i g')
    (hempty : (g.shared.cells (((g.locals i).regs rSlot).toNat)).marker.toNat / 2
      = ((g.locals i).regs rHint).toNat)
    (heven : (g.shared.cells (((g.locals i).regs rSlot).toNat)).marker.toNat % 2 = 0) :
    ∃ (s' : AbsState UInt64) (tag : StepTag UInt64),
      GRef C limit kind s' g' ∧ Inv C limit s' ∧
      Effect 0 C limit hC s (Shared.toMem g.shared) s' (Shared.toMem g'.shared) tag ∧
      tag = .obs .popEmpty := by
  have hpinv : PopInv C limit s g.shared (g.locals i) (Phase.running 1 1) := by
    have h1 := hg.hlocal i
    simp only [ThreadInv, hk, hp] at h1
    exact h1
  cases hpinv with
  | slot h hpc hintEq hintLe hlim slotEq =>
    have h64 : h < 2 ^ 64 := by
      have hb := hbound
      have h1 := hi.hlimit
      omega
    have hmod64 : h % C < 2 ^ 64 := by
      have := Nat.mod_lt h hC
      omega
    have hslotNat : ((g.locals i).regs rSlot).toNat = h % C := by
      rw [slotEq]
      exact uint64_toNat_ofNat_of_lt hmod64
    have hqH : (g.shared.cells (h % C)).marker.toNat / 2 = h := by
      have h1 := hempty
      rw [hslotNat] at h1
      rw [hintEq, uint64_toNat_ofNat_of_lt h64] at h1
      exact h1
    have hevenH : (g.shared.cells (h % C)).marker.toNat % 2 = 0 := by
      have h1 := heven
      rw [hslotNat] at h1
      exact h1
    let st0 : MState := toMState g.shared (g.locals i)
    let regs1 : Nat → UInt64 := upd st0.regs rMarker (g.shared.cells (h % C)).marker
    let regs2 : Nat → UInt64 := upd regs1 rPayload (g.shared.cells (h % C)).payload
    let st' : MState := { st0 with regs := regs2 }
    have hcellEq : (toMState g.shared (g.locals i)).cells
        ((toMState g.shared (g.locals i)).regs rSlot).toNat = g.shared.cells (h % C) := by
      show g.shared.cells (((g.locals i).regs rSlot).toNat) = g.shared.cells (h % C)
      rw [hslotNat]
    have hst : opStep popProgram 1 1 (toMState g.shared (g.locals i))
        = .running 1 2 st' := by
      simp [opStep, popProgram, execOp, eval, st', st0, regs1, regs2, hcellEq]
    let newloc : Local := { (g.locals i).after st' with phase := Phase.running 1 2 }
    have hg' : g' = { shared := g.shared.after st', locals := updLocal g.locals i newloc } := by
      have hs := hstep
      simp only [GStep, programOf, hk, hp, st0, hst] at hs
      exact hs
    have hafter : g.shared.after st' = g.shared := by
      simp [Shared.after, st', st0, toMState]
    have hshared : g'.shared = g.shared := by
      rw [hg']
      exact hafter
    have hmem : Shared.toMem g'.shared = Shared.toMem g.shared := by
      rw [hshared]
    have hle_q : h ≤ (g.shared.cells (h % C)).marker.toNat / 2 := by omega
    have hq63 : (g.shared.cells (h % C)).marker.toNat / 2 < 2 ^ 63 := by
      have h1 := hi.hlimit
      omega
    have hloadInv : PopInv C limit s g.shared newloc (Phase.running 1 2) := by
      refine PopInv.load h ((g.shared.cells (h % C)).marker.toNat)
        ((g.shared.cells (h % C)).marker.toNat / 2) rfl hintEq hintLe hlim slotEq ?_ ?_ ?_ rfl hq63 hle_q
      · show st'.regs rMarker = UInt64.ofNat ((g.shared.cells (h % C)).marker.toNat)
        exact (UInt64.ofNat_toNat (x := (g.shared.cells (h % C)).marker)).symm
      · show (g.shared.cells (h % C)).marker.toNat < 2 ^ 64
        exact UInt64.toNat_lt _
      · show (g.shared.cells (h % C)).marker.toNat
          ≤ ((Shared.toMem g.shared).cells (h % C)).marker
        exact Nat.le_refl _
    have hgref' : GRef C limit kind s g' := by
      rw [hg', hafter]
      change GRef C limit kind s
        { shared := g.shared, locals := updLocal g.locals i newloc }
      constructor
      · exact hg.hshared
      · intro j
        change ThreadInv C limit s g.shared (updLocal g.locals i newloc j) (kind j)
        by_cases hj : j = i
        · subst hj
          have hloc : updLocal g.locals j newloc j = newloc := by simp [updLocal]
          rw [hloc]
          simpa [ThreadInv, hk, newloc] using hloadInv
        · have hloc : updLocal g.locals i newloc j = g.locals j := by
            simp [updLocal, hj]
          rw [hloc]
          exact hg.hlocal j
    have hguard : ObsGuard C limit s .popEmpty :=
      pop_slot_empty_guard hi hg.hshared hC hpow hintLe hqH hevenH
    exact ⟨s, .obs .popEmpty, hgref', hi,
      Effect.obs .popEmpty (SharedRef.ref hg.hshared) hguard rfl hmem, rfl⟩

end Mpmc

namespace Mpmc

open Mpmc.Kernel

/-- At the push horizon test, `limit ≤ hint` certifies publication exhaustion
and the branch step can be relabeled as `.obs .pushExhausted`. -/
theorem push_horizon_exhausted_effect {n C limit k : Nat} {kind : Fin n → Kind}
    {s : AbsState UInt64} {g g' : GState n} {i : Fin n}
    (hi : Inv C limit s) (hg : GRef C limit kind s g)
    (hC : 0 < C) (hpow : C = 2 ^ k) (hCmax : C ≤ 2 ^ 24)
    (hbound : limit < 2 ^ 63) (hlimitC : limit + C ≤ 2 ^ 63)
    (hk : kind i = .push)
    (hp : (g.locals i).phase = Phase.running 0 1)
    (hstep : GStep kind g i g')
    (hge : limit ≤ ((g.locals i).regs rHint).toNat) :
    ∃ (s' : AbsState UInt64) (tag : StepTag UInt64),
      GRef C limit kind s' g' ∧ Inv C limit s' ∧
      Effect 0 C limit hC s (Shared.toMem g.shared) s' (Shared.toMem g'.shared) tag ∧
      tag = .obs .pushExhausted := by
  have hpinv : PushInv C limit s g.shared (g.locals i) (Phase.running 0 1) := by
    have h1 := hg.hlocal i
    simp only [ThreadInv, hk, hp] at h1
    exact h1
  cases hpinv with
  | hint h hpc hintEq hintLe =>
    have hle : h ≤ limit := Nat.le_trans hintLe (Nat.le_trans hi.hw_le hi.hlimit)
    have h64 : h < 2 ^ 64 := by have := hbound; omega
    have hgeH : limit ≤ h := by
      rw [hintEq] at hge
      simpa [uint64_toNat_ofNat_of_lt h64] using hge
    let st0 : MState := toMState g.shared (g.locals i)
    have hlim : st0.params.limit.toNat = limit := hg.hshared.hlimit
    have hintNat : ((st0.regs rHint).toNat) = h := by
      change ((g.locals i).regs rHint).toNat = h
      rw [hintEq]
      exact uint64_toNat_ofNat_of_lt h64
    have hnot : ¬ ((st0.regs rHint) < st0.params.limit) := by
      intro hlt
      have hlt' := (UInt64.lt_iff_toNat_lt).mp hlt
      rw [hlim, hintNat] at hlt'
      omega
    have hst : opStep pushProgram 0 1 st0 = .running 9 0 st0 := by
      simp [opStep, pushProgram, eval, hnot, st0]
    let newloc : Local := { (g.locals i).after st0 with phase := Phase.running 9 0 }
    have hg' : g' = { shared := g.shared.after st0, locals := updLocal g.locals i newloc } := by
      have hs := hstep
      simp only [GStep, programOf, hk, hp, st0, hst] at hs
      exact hs
    have hafter : g.shared.after st0 = g.shared := by
      simp [Shared.after, st0, toMState]
    have hmem : Shared.toMem g'.shared = Shared.toMem g.shared := by
      rw [hg', hafter]
    have hinv' : PushInv C limit s g.shared newloc (Phase.running 9 0) :=
      PushInv.exhausted rfl
    have hgref' : GRef C limit kind s g' := by
      rw [hg', hafter]
      change GRef C limit kind s
        { shared := g.shared, locals := updLocal g.locals i newloc }
      constructor
      · exact hg.hshared
      · intro j
        change ThreadInv C limit s g.shared (updLocal g.locals i newloc j) (kind j)
        by_cases hj : j = i
        · subst hj
          have hloc : updLocal g.locals j newloc j = newloc := by simp [updLocal]
          rw [hloc]
          simpa [ThreadInv, hk, newloc] using hinv'
        · have hloc : updLocal g.locals i newloc j = g.locals j := by
            simp [updLocal, hj]
          rw [hloc]
          exact hg.hlocal j
    have hguard : ObsGuard C limit s .pushExhausted :=
      push_hint_exhausted_guard hi hintLe hgeH
    exact ⟨s, .obs .pushExhausted, hgref', hi,
      Effect.obs .pushExhausted (SharedRef.ref hg.hshared) hguard rfl hmem, rfl⟩

/-- At the pop horizon test, `limit ≤ hint` certifies consumption exhaustion
and the branch step can be relabeled as `.obs .popExhausted`. -/
theorem pop_horizon_exhausted_effect {n C limit k : Nat} {kind : Fin n → Kind}
    {s : AbsState UInt64} {g g' : GState n} {i : Fin n}
    (hi : Inv C limit s) (hg : GRef C limit kind s g)
    (hC : 0 < C) (hpow : C = 2 ^ k) (hCmax : C ≤ 2 ^ 24)
    (hbound : limit < 2 ^ 63) (hlimitC : limit + C ≤ 2 ^ 63)
    (hk : kind i = .pop)
    (hp : (g.locals i).phase = Phase.running 0 1)
    (hstep : GStep kind g i g')
    (hge : limit ≤ ((g.locals i).regs rHint).toNat) :
    ∃ (s' : AbsState UInt64) (tag : StepTag UInt64),
      GRef C limit kind s' g' ∧ Inv C limit s' ∧
      Effect 0 C limit hC s (Shared.toMem g.shared) s' (Shared.toMem g'.shared) tag ∧
      tag = .obs .popExhausted := by
  have hpinv : PopInv C limit s g.shared (g.locals i) (Phase.running 0 1) := by
    have h1 := hg.hlocal i
    simp only [ThreadInv, hk, hp] at h1
    exact h1
  cases hpinv with
  | hint h hpc hintEq hintLe =>
    have hle : h ≤ limit := Nat.le_trans hintLe (Nat.le_trans hi.hr_le
      (Nat.le_trans hi.hR_le_W hi.hlimit))
    have h64 : h < 2 ^ 64 := by have := hbound; omega
    have hgeH : limit ≤ h := by
      rw [hintEq] at hge
      simpa [uint64_toNat_ofNat_of_lt h64] using hge
    let st0 : MState := toMState g.shared (g.locals i)
    have hlim : st0.params.limit.toNat = limit := hg.hshared.hlimit
    have hintNat : ((st0.regs rHint).toNat) = h := by
      change ((g.locals i).regs rHint).toNat = h
      rw [hintEq]
      exact uint64_toNat_ofNat_of_lt h64
    have hnot : ¬ ((st0.regs rHint) < st0.params.limit) := by
      intro hlt
      have hlt' := (UInt64.lt_iff_toNat_lt).mp hlt
      rw [hlim, hintNat] at hlt'
      omega
    have hst : opStep popProgram 0 1 st0 = .running 8 0 st0 := by
      simp [opStep, popProgram, eval, hnot, st0]
    let newloc : Local := { (g.locals i).after st0 with phase := Phase.running 8 0 }
    have hg' : g' = { shared := g.shared.after st0, locals := updLocal g.locals i newloc } := by
      have hs := hstep
      simp only [GStep, programOf, hk, hp, st0, hst] at hs
      exact hs
    have hafter : g.shared.after st0 = g.shared := by
      simp [Shared.after, st0, toMState]
    have hmem : Shared.toMem g'.shared = Shared.toMem g.shared := by
      rw [hg', hafter]
    have hinv' : PopInv C limit s g.shared newloc (Phase.running 8 0) :=
      PopInv.exhausted rfl
    have hgref' : GRef C limit kind s g' := by
      rw [hg', hafter]
      change GRef C limit kind s
        { shared := g.shared, locals := updLocal g.locals i newloc }
      constructor
      · exact hg.hshared
      · intro j
        change ThreadInv C limit s g.shared (updLocal g.locals i newloc j) (kind j)
        by_cases hj : j = i
        · subst hj
          have hloc : updLocal g.locals j newloc j = newloc := by simp [updLocal]
          rw [hloc]
          simpa [ThreadInv, hk, newloc] using hinv'
        · have hloc : updLocal g.locals i newloc j = g.locals j := by
            simp [updLocal, hj]
          rw [hloc]
          exact hg.hlocal j
    have hguard : ObsGuard C limit s .popExhausted :=
      pop_hint_exhausted_guard hi hintLe hgeH
    exact ⟨s, .obs .popExhausted, hgref', hi,
      Effect.obs .popExhausted (SharedRef.ref hg.hshared) hguard rfl hmem, rfl⟩

end Mpmc
