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
  Tagged kernel effects: data-level labels for stutters, events, legal
  observations, and returns.

  This base module defines `StepTag` and `Effect`; the execution relation and
  the kernel-step bridge live in `Mpmc.KernelEffect`.
-/

import Mpmc.KernelObserve
import Mpmc.Observed

namespace Mpmc

open Mpmc.Kernel

/-- The observable label of one kernel step. -/
inductive StepTag (V : Type) where
  /-- No shared-memory change and no observation. -/
  | stutter
  /-- One abstract push, pop, hint help, or other event. -/
  | event (a : Action V) (r : Result V)
  /-- A legal failure observation. -/
  | obs (k : ObsKind)
  /-- A returned operation with its status value. -/
  | ret (status : UInt64)

/-- A tagged one-step effect.  Stutters and observations leave both the
abstract state and shared memory unchanged; events are exactly `EventStep`. -/
inductive Effect (z : V) (C limit : Nat) (hC : 0 < C) :
    AbsState V → Mem V → AbsState V → Mem V → StepTag V → Prop
  | stutter {s : AbsState V} {m : Mem V} {s' : AbsState V} {m' : Mem V}
      (hm : Ref z C s m) (hs : s' = s) (hmem : m' = m) :
      Effect z C limit hC s m s' m' .stutter
  | event {s : AbsState V} {m : Mem V} {s' : AbsState V} {m' : Mem V}
      (a : Action V) (r : Result V)
      (h : EventStep z C limit hC s m (some a) (some r) s' m') :
      Effect z C limit hC s m s' m' (.event a r)
  | obs {s : AbsState V} {m : Mem V} {s' : AbsState V} {m' : Mem V}
      (k : ObsKind) (hm : Ref z C s m) (guard : ObsGuard C limit s k)
      (hs : s' = s) (hmem : m' = m) :
      Effect z C limit hC s m s' m' (.obs k)
  | ret {s : AbsState V} {m : Mem V} {s' : AbsState V} {m' : Mem V}
      (status : UInt64) (hm : Ref z C s m)
      (hs : s' = s) (hmem : m' = m) :
      Effect z C limit hC s m s' m' (.ret status)

/-- Whether a tag is a successful cell operation (push or pop), as opposed
to a hint-help event. -/
def StepTag.isCellEvent : StepTag V → Bool
  | .event (.push _) _ => true
  | .event .pop _ => true
  | _ => false

/-- A non-cell tag leaves every cell marker unchanged. -/
theorem Effect.cell_marker_eq_of_not_cellEvent {z : V} {C limit : Nat} {hC : 0 < C}
    {s m s' m' : _} {tag : StepTag V}
    (h : Effect z C limit hC s m s' m' tag)
    (hnot : tag.isCellEvent = false) (j : Nat) :
    (m'.cells j).marker = (m.cells j).marker := by
  cases h with
  | stutter hm hs hmem =>
      cases hmem
      rfl
  | obs k hm guard hs hmem =>
      cases hmem
      rfl
  | ret status hm hs hmem =>
      cases hmem
      rfl
  | event a r hev =>
      cases hev with
      | push v hi hm hprov hlim hcell =>
          simp [StepTag.isCellEvent] at hnot
      | pop hi hm hprov hlim p hcell =>
          simp [StepTag.isCellEvent] at hnot
      | helpW hi hm hw hW => rfl
      | helpR hi hm hr hR => rfl

/-- Every tagged effect is an `ObservedStep` with the expected labels. -/
theorem Effect.toObserved {z : V} {C limit : Nat} {hC : 0 < C}
    {s m s' m' : _} {tag : StepTag V}
    (h : Effect z C limit hC s m s' m' tag) :
    ObservedStep z C limit hC s m
      (match tag with | .event a _ => some a | _ => none)
      (match tag with | .event _ r => some r | _ => none) s' m' := by
  cases h with
  | stutter hm hs hmem =>
      cases hs
      cases hmem
      exact ObservedStep.event (EventStep.stutter hm)
  | event a r hev =>
      simpa using ObservedStep.event hev
  | obs k hm guard hs hmem =>
      cases hs
      cases hmem
      exact ObservedStep.obs k hm guard
  | ret status hm hs hmem =>
      cases hs
      cases hmem
      exact ObservedStep.event (EventStep.stutter hm)

/-- The action label of a tag, if any. -/
def StepTag.action? {V : Type} : StepTag V → Option (Action V)
  | .event a _ => some a
  | _ => none

/-- The result label of a tag, if any. -/
def StepTag.result? {V : Type} : StepTag V → Option (Result V)
  | .event _ r => some r
  | _ => none

/-- A tagged effect preserves the abstract invariant. -/
theorem Effect.inv {z : V} {C limit : Nat} {hC : 0 < C}
    {s m s' m' : _} {tag : StepTag V}
    (hi : Inv C limit s) (h : Effect z C limit hC s m s' m' tag) :
    Inv C limit s' := by
  cases h with
  | stutter hm hs hmem =>
      cases hmem
      simpa [hs] using hi
  | event a r hev => exact Inv.step hi (EventStep.step hev)
  | obs k hm guard hs hmem =>
      cases hmem
      simpa [hs] using hi
  | ret status hm hs hmem =>
      cases hmem
      simpa [hs] using hi

/-- `Effect` at the type level implies the tagged labels are an
`ObservedStep`.  This is the bridge used by `Exec`. -/
theorem effect_toObserved {z : V} {C limit : Nat} {hC : 0 < C}
    {s m s' m' : _} {tag : StepTag V}
    (h : Effect z C limit hC s m s' m' tag) :
    ObservedStep z C limit hC s m (tag.action?) (tag.result?) s' m' := by
  cases tag with
  | stutter => exact h.toObserved
  | event a r => exact h.toObserved
  | obs k => exact h.toObserved
  | ret status => exact h.toObserved

/-- A stutter can be relabeled as a legal observation when the guard holds at
the current abstract state. -/
theorem Effect.stutter_to_obs {z : V} {C limit : Nat} {hC : 0 < C}
    {s m s' m' : _} {k : ObsKind}
    (hst : Effect z C limit hC s m s' m' .stutter)
    (hm : Ref z C s m) (guard : ObsGuard C limit s k) :
    Effect z C limit hC s m s' m' (.obs k) := by
  cases hst with
  | stutter hm' hs hmem => exact Effect.obs k hm guard hs hmem

/-- At a push cell load with a full snapshot for `h - C`, the load step can
be relabeled as a `FULL` observation. -/
theorem push_load_full_effect_of_stutter {C limit k : Nat} {s : AbsState UInt64}
    {sh : Shared} {h : Nat} {hC : 0 < C}
    (hi : Inv C limit s) (hs : SharedRef C limit s sh)
    (hpow : C = 2 ^ k)
    (hintLe : h ≤ s.w)
    (hq : (sh.cells (h % C)).marker.toNat / 2 + C = h)
    (hst : Effect 0 C limit hC s (Shared.toMem sh) s (Shared.toMem sh) .stutter) :
    Effect 0 C limit hC s (Shared.toMem sh) s (Shared.toMem sh) (.obs .pushFull) := by
  exact Effect.stutter_to_obs hst (SharedRef.ref hs)
    (push_slot_full_guard hi hs hC hpow hintLe hq)

/-- At a pop cell load with an empty snapshot for `h`, the load step can be
relabeled as an `EMPTY` observation. -/
theorem pop_load_empty_effect_of_stutter {C limit k : Nat} {s : AbsState UInt64}
    {sh : Shared} {h : Nat} {hC : 0 < C}
    (hi : Inv C limit s) (hs : SharedRef C limit s sh)
    (hpow : C = 2 ^ k)
    (hintLe : h ≤ s.r)
    (hq : (sh.cells (h % C)).marker.toNat / 2 = h)
    (heven : (sh.cells (h % C)).marker.toNat % 2 = 0)
    (hst : Effect 0 C limit hC s (Shared.toMem sh) s (Shared.toMem sh) .stutter) :
    Effect 0 C limit hC s (Shared.toMem sh) s (Shared.toMem sh) (.obs .popEmpty) := by
  exact Effect.stutter_to_obs hst (SharedRef.ref hs)
    (pop_slot_empty_guard hi hs hC hpow hintLe hq heven)

/-- At a push hint at or beyond the horizon, the hint test can be relabeled
as a `pushExhausted` observation. -/
theorem push_hint_exhausted_effect_of_stutter {C limit : Nat} {s : AbsState UInt64}
    {sh : Shared} {h : Nat} {hC : 0 < C}
    (hi : Inv C limit s) (hs : SharedRef C limit s sh)
    (hintLe : h ≤ s.w) (hge : limit ≤ h)
    (hst : Effect 0 C limit hC s (Shared.toMem sh) s (Shared.toMem sh) .stutter) :
    Effect 0 C limit hC s (Shared.toMem sh) s (Shared.toMem sh) (.obs .pushExhausted) := by
  exact Effect.stutter_to_obs hst (SharedRef.ref hs)
    (push_hint_exhausted_guard hi hintLe hge)

/-- At a pop hint at or beyond the horizon, the hint test can be relabeled
as a `popExhausted` observation. -/
theorem pop_hint_exhausted_effect_of_stutter {C limit : Nat} {s : AbsState UInt64}
    {sh : Shared} {h : Nat} {hC : 0 < C}
    (hi : Inv C limit s) (hs : SharedRef C limit s sh)
    (hintLe : h ≤ s.r) (hge : limit ≤ h)
    (hst : Effect 0 C limit hC s (Shared.toMem sh) s (Shared.toMem sh) .stutter) :
    Effect 0 C limit hC s (Shared.toMem sh) s (Shared.toMem sh) (.obs .popExhausted) := by
  exact Effect.stutter_to_obs hst (SharedRef.ref hs)
    (pop_hint_exhausted_guard hi hintLe hge)


end Mpmc
