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
  Kernel trace composition: a finite global interleaving of kernel steps is
  an abstract event trace, so the FIFO theorem applies to any actual run.
-/

import Mpmc.KernelSim
import Mpmc.Linearizable
import Mpmc.Potential

namespace Mpmc

open Mpmc.Kernel

/-- Every event preserves the abstract invariant. -/
theorem EventStep.inv_some {z : V} {C limit : Nat} {hC : 0 < C}
    {s m s' m' : _} {a : Action V} {r : Result V}
    (hi : Inv C limit s)
    (h : EventStep z C limit hC s m (some a) (some r) s' m') :
    Inv C limit s' :=
  Inv.step hi (EventStep.step h)

/-- Every event, including a stutter, preserves the abstract invariant. -/
theorem EventStep.inv {z : V} {C limit : Nat} {hC : 0 < C}
    {s m s' m' : _} {a : Option (Action V)} {r : Option (Result V)}
    (hi : Inv C limit s)
    (h : EventStep z C limit hC s m a r s' m') :
    Inv C limit s' := by
  cases h with
  | stutter => exact hi
  | push hi' hm hprov hlim hcell v =>
      exact EventStep.inv_some (hC := hC) hi
        (EventStep.push (hC := hC) hi' hm hprov hlim hcell v)
  | pop hi' hm hprov hlim p hcell =>
      exact EventStep.inv_some (hC := hC) hi
        (EventStep.pop (hC := hC) hi' hm hprov hlim p hcell)
  | helpW hi' hm hw hW =>
      exact EventStep.inv_some (hC := hC) hi
        (EventStep.helpW (hC := hC) hi' hm hw hW)
  | helpR hi' hm hr hR =>
      exact EventStep.inv_some (hC := hC) hi
        (EventStep.helpR (hC := hC) hi' hm hr hR)

/-- A fresh local register file for an operation invocation. -/
def freshLocal (v : UInt64) : Local :=
  { phase := .running 0 0, value := v, regs := fun _ => 0, out0 := 0, out1 := 0 }

def invokeLocal (_loc : Local) (v : UInt64) : Local := freshLocal v

/-- The local state before the first call: no operation is active.  Encoding
this as `returned 0` lets every call start with an explicit `GInvoke`, which
is exactly the C API boundary (`mpmc_push`/`mpmc_pop`). -/
def startLocal (v : UInt64) : Local :=
  { phase := .returned 0, value := v, regs := fun _ => 0, out0 := 0, out1 := 0 }

/-- Reset a returned thread to the entry of a fresh operation.  This is the
invocation side of the C API: the caller writes the value and starts the
kernel at block 0. -/
def GInvoke {n : Nat} (g : GState n) (i : Fin n)
    (v : UInt64) (g' : GState n) : Prop :=
  ∃ r : UInt64,
    (g.locals i).phase = .returned r ∧
    g' = { g with locals := updLocal g.locals i (invokeLocal (g.locals i) v) }

/-- An invocation does not change the shared memory refinement. -/
theorem GInvoke.gref {n C limit : Nat} {kind : Fin n → Kind}
    {s : AbsState UInt64} {g g' : GState n} {i : Fin n} {v : UInt64}
    (hg : GRef C limit kind s g) (h : GInvoke g i v g') :
    GRef C limit kind s g' := by
  rcases h with ⟨r, hphase, rfl⟩
  refine ⟨hg.hshared, ?_⟩
  intro j
  by_cases hj : j = i
  · subst j
    have hlocals : (updLocal g.locals i (invokeLocal (g.locals i) v)) i =
        invokeLocal (g.locals i) v := by
      simp [updLocal]
    dsimp only [GState.locals, GState.shared]
    rw [hlocals]
    cases kind i with
    | push => exact PushInv.entry rfl
    | pop => exact PopInv.entry rfl
  · simpa [updLocal, hj] using hg.hlocal j

/-- The initial global state used by the C `mpmc_create` layout, with one
value register per thread. -/
def initialGState {n : Nat} (C limit : Nat) (vals : Fin n → UInt64) : GState n :=
  { shared := initShared C limit
    locals := fun i => startLocal (vals i) }

/-- The initial global state refines the abstract initial state. -/
theorem initialGRef {n C limit : Nat} (kind : Fin n → Kind)
    (vals : Fin n → UInt64)
    (hC : 0 < C) (hCmax : C ≤ 2 ^ 24) (hlimit : limit < 2 ^ 63) :
    GRef C limit kind (initial UInt64) (initialGState C limit vals) := by
  refine ⟨initShared_ref hC hCmax hlimit, ?_⟩
  intro i
  cases kind i <;> simp [ThreadInv, startLocal, initialGState]

/-- A finite sequence of global kernel steps, including operation
invocations after a return. -/
inductive GPath {n : Nat} (kind : Fin n → Kind) :
    GState n → GState n → Prop
  | refl (g : GState n) : GPath kind g g
  | step {g g' g'' : GState n} (i : Fin n) (h : GStep kind g i g')
      (hs : GPath kind g' g'') : GPath kind g g''
  | invoke {g g' g'' : GState n} (i : Fin n) (v : UInt64)
      (h : GInvoke g i v g') (hs : GPath kind g' g'') :
      GPath kind g g''

/-- Any finite global kernel run refines an abstract event trace. -/
theorem GPath.events {n C limit : Nat} {kind : Fin n → Kind} {g g' : GState n}
    (hp : GPath kind g g')
    (s : AbsState UInt64) (hi : Inv C limit s) (hg : GRef C limit kind s g)
    (hC : 0 < C) (k : Nat) (hpow : C = 2 ^ k) (hCmax : C ≤ 2 ^ 24)
    (hbound : limit < 2 ^ 63) (hlimitC : limit + C ≤ 2 ^ 63) :
    ∃ s' as rs,
      GRef C limit kind s' g' ∧
      EventSteps 0 C limit hC s (Shared.toMem g.shared) as rs s' (Shared.toMem g'.shared) := by
  induction hp generalizing s with
  | refl g =>
      exact ⟨s, [], [], hg, EventSteps.nil⟩
  | step i h hs ih =>
      obtain ⟨s1, hg1, hev⟩ :=
        gstep_sim hi hg hC hpow hCmax hbound hlimitC h
      rcases hev with hev | ⟨hs_eq, hshared⟩
      · obtain ⟨a, res, hev⟩ := hev
        have hi1 := EventStep.inv_some (hC := hC) hi hev
        obtain ⟨s2, as, rs, hg2, hevents⟩ := ih s1 hi1 hg1
        exact ⟨s2, a :: as, res :: rs, hg2, EventSteps.step hev hevents⟩
      · subst s1
        have hst := EventStep.stutter (z := (0 : UInt64)) (C := C) (limit := limit)
          (hC := hC) (SharedRef.ref hg.hshared)
        obtain ⟨s2, as, rs, hg2, hevents⟩ := ih s hi hg1
        have hevents' := by
          simpa [hshared] using hevents
        exact ⟨s2, as, rs, hg2, EventSteps.stutter hst hevents'⟩
  | invoke i v h hs ih =>
      rcases h with ⟨r, hphase, rfl⟩
      have hg' := GInvoke.gref (v := v) hg ⟨r, hphase, rfl⟩
      have hst := EventStep.stutter (z := (0 : UInt64)) (C := C) (limit := limit)
        (hC := hC) (SharedRef.ref hg.hshared)
      obtain ⟨s2, as, rs, hg2, hevents⟩ := ih s hi hg'
      exact ⟨s2, as, rs, hg2, EventSteps.stutter hst hevents⟩

/-- Any finite global kernel run has the FIFO labels and values of its
abstract event trace. -/
theorem GPath.fifo {n C limit : Nat} {kind : Fin n → Kind} {g g' : GState n}
    (hp : GPath kind g g')
    (s : AbsState UInt64) (hi : Inv C limit s) (hg : GRef C limit kind s g)
    (hC : 0 < C) (k : Nat) (hpow : C = 2 ^ k) (hCmax : C ≤ 2 ^ 24)
    (hbound : limit < 2 ^ 63) (hlimitC : limit + C ≤ 2 ^ 63) :
    ∃ s' as rs,
      GRef C limit kind s' g' ∧
      pushLabels rs = List.range' s.W (s'.W - s.W) ∧
      popLabels rs = List.range' s.R (s'.R - s.R) ∧
      (pushValues as).map some =
        (List.range' s.W (s'.W - s.W)).map (fun i => s'.val i) ∧
      (popValues rs).map some =
        (List.range' s.R (s'.R - s.R)).map (fun i => s'.val i) := by
  obtain ⟨s', as, rs, hg', hev⟩ :=
    GPath.events hp s hi hg hC k hpow hCmax hbound hlimitC
  have hsteps : Steps C limit s as s' rs := EventSteps.steps (hC := hC) hev
  have hf := trace_fifo hsteps hi
  exact ⟨s', as, rs, hg', hf.1, hf.2.1, hf.2.2.1, hf.2.2.2⟩

/-- A finite global kernel run has at most `psi` growth many abstract events.
This is a finite progress bound, not a scheduler-liveness theorem. -/
theorem GPath.events_bounded {n C limit k : Nat} {kind : Fin n → Kind}
    {g g' : GState n}
    (hp : GPath kind g g')
    (s : AbsState UInt64) (hi : Inv C limit s) (hg : GRef C limit kind s g)
    (hC : 0 < C) (hpow : C = 2 ^ k) (hCmax : C ≤ 2 ^ 24)
    (hbound : limit < 2 ^ 63) (hlimitC : limit + C ≤ 2 ^ 63) :
    ∃ s' as rs,
      GRef C limit kind s' g' ∧
      EventSteps 0 C limit hC s (Shared.toMem g.shared) as rs s' (Shared.toMem g'.shared) ∧
      as.length ≤ psi s' - psi s := by
  obtain ⟨s', as, rs, hg', hev⟩ :=
    GPath.events hp s hi hg hC k hpow hCmax hbound hlimitC
  exact ⟨s', as, rs, hg', hev, EventSteps.length_le_psi hev⟩

/-- A cell-marker change along a finite global kernel path witnesses at
least one abstract event.  This is the kernel-level form of the retry-charge
premise. -/
theorem GPath.event_of_cell_change {n C limit k : Nat} {kind : Fin n → Kind}
    {g g' : GState n}
    (hp : GPath kind g g')
    (s : AbsState UInt64) (hi : Inv C limit s) (hg : GRef C limit kind s g)
    (hC : 0 < C) (hpow : C = 2 ^ k) (hCmax : C ≤ 2 ^ 24)
    (hbound : limit < 2 ^ 63) (hlimitC : limit + C ≤ 2 ^ 63)
    {j : Nat}
    (hchange : ((Shared.toMem g.shared).cells j).marker ≠
      ((Shared.toMem g'.shared).cells j).marker) :
    ∃ s' as rs,
      GRef C limit kind s' g' ∧
      EventSteps 0 C limit hC s (Shared.toMem g.shared) as rs s' (Shared.toMem g'.shared) ∧
      as ≠ [] := by
  obtain ⟨s', as, rs, hg', hev⟩ :=
    GPath.events hp s hi hg hC k hpow hCmax hbound hlimitC
  exact ⟨s', as, rs, hg', hev, EventSteps.event_of_cell_change hev hchange⟩

/-- FIFO from the concrete initial state of the C library. -/
theorem initial_fifo {n C limit k : Nat} {kind : Fin n → Kind}
    {vals : Fin n → UInt64} {g' : GState n}
    (hp : GPath kind (initialGState C limit vals) g')
    (hC : 0 < C) (hpow : C = 2 ^ k) (hCmax : C ≤ 2 ^ 24)
    (hbound : limit < 2 ^ 63) (hlimitC : limit + C ≤ 2 ^ 63) :
    ∃ s' as rs,
      GRef C limit kind s' g' ∧
      pushLabels rs = List.range' 0 s'.W ∧
      popLabels rs = List.range' 0 s'.R ∧
      (pushValues as).map some = (List.range' 0 s'.W).map (fun i => s'.val i) ∧
      (popValues rs).map some = (List.range' 0 s'.R).map (fun i => s'.val i) := by
  obtain ⟨s', as, rs, hg', hpush, hpop, hpushv, hpopv⟩ :=
    GPath.fifo hp (initial UInt64) (initial_inv C limit)
      (initialGRef kind vals hC hCmax hbound) hC k hpow hCmax hbound hlimitC
  exact ⟨s', as, rs, hg',
    by simpa [initial] using hpush,
    by simpa [initial] using hpop, hpushv, hpopv⟩

end Mpmc
