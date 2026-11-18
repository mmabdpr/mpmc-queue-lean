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
  Failure observations: the composition layer above `EventStep`.

  `EventStep` has no constructor for an operation that fails
  legally (push to a full queue, pop from an empty queue, or either
  operation at the publication horizon).  Such a failure is an
  observable event: it linearizes at the point where the guard holds and
  leaves both the abstract queue and the shared memory unchanged.

  `ObservedStep` adds exactly that constructor, carrying the memory
  refinement and the legality guard, so that a trace can mix shared events
  with failed observations.  `ObservedSteps` is the corresponding list
  relation; its abstract projection simply drops the observations, and its
  `Ref` preservation follows from the memory refinement carried by every
  observation.
-/

import Mpmc.Concurrent

namespace Mpmc

variable {V : Type}

/-! ## Legal-failure guards -/

/-- A push that fails because the queue is full is legal exactly at
`W - R = C`. -/
theorem obsGuard_pushFull (C limit : Nat) (s : AbsState V) :
    ObsGuard C limit s .pushFull ↔ s.W - s.R = C :=
  Iff.rfl

/-- A pop that fails because the queue is empty is legal exactly at
`R = W`. -/
theorem obsGuard_popEmpty (C limit : Nat) (s : AbsState V) :
    ObsGuard C limit s .popEmpty ↔ s.R = s.W :=
  Iff.rfl

/-- A push that fails because the publication horizon is reached is legal
exactly at `W = limit`. -/
theorem obsGuard_pushExhausted (C limit : Nat) (s : AbsState V) :
    ObsGuard C limit s .pushExhausted ↔ s.W = limit :=
  Iff.rfl

/-- A pop that fails because the publication horizon is reached is legal
exactly at `R = limit`. -/
theorem obsGuard_popExhausted (C limit : Nat) (s : AbsState V) :
    ObsGuard C limit s .popExhausted ↔ s.R = limit :=
  Iff.rfl

/-! ## Steps -/

/-- One observable atomic step: either an admissible shared event, or a
legally failed operation that changes nothing.

`EventStep` has no failed-operation constructor; that absence is why the
FIFO trace theory is unchanged.  Failures are observations, not abstract
transitions, so they appear here with `none`/`none` labels. -/
inductive ObservedStep (z : V) (C limit : Nat) (hC : 0 < C) :
    AbsState V → Mem V → Option (Action V) → Option (Result V) →
      AbsState V → Mem V → Prop
  | event {s : AbsState V} {m : Mem V} {s' : AbsState V} {m' : Mem V}
      {a : Option (Action V)} {r : Option (Result V)}
      (h : EventStep z C limit hC s m a r s' m') :
      ObservedStep z C limit hC s m a r s' m'
  | obs {s : AbsState V} {m : Mem V}
      (kind : ObsKind) (hm : Ref z C s m) (legal : ObsGuard C limit s kind) :
      ObservedStep z C limit hC s m none none s m

/-- A non-stutter observed step is exactly one abstract transition.

A `some`/`some` step cannot be an observation, so the `obs` case is
impossible. -/
theorem ObservedStep.steps {z : V} {C limit : Nat} {hC : 0 < C}
    {s : AbsState V} {m : Mem V} {s' : AbsState V} {m' : Mem V}
    {a : Action V} {r : Result V}
    (h : ObservedStep z C limit hC s m (some a) (some r) s' m') :
    Step C limit s a s' r := by
  cases h with
  | event h => exact EventStep.step h

/-- Every observed step preserves the memory refinement. -/
theorem ObservedStep.ref {z : V} {C limit : Nat} {hC : 0 < C}
    {s : AbsState V} {m : Mem V} {s' : AbsState V} {m' : Mem V}
    {a : Option (Action V)} {r : Option (Result V)}
    (hm : Ref z C s m) (h : ObservedStep z C limit hC s m a r s' m') :
    Ref z C s' m' := by
  cases h with
  | event h => exact EventStep.ref h
  | obs kind _ legal => exact hm

/-! ## Traces -/

/-- A finite list of observed steps with its abstract action/result trace.

Failed observations are stutters on both the abstract and the concrete
side, so they contribute no labels. -/
inductive ObservedSteps (z : V) (C limit : Nat) (hC : 0 < C) :
    AbsState V → Mem V → List (Action V) → List (Result V) →
      AbsState V → Mem V → Prop
  | nil {s : AbsState V} {m : Mem V} :
      ObservedSteps z C limit hC s m [] [] s m
  | stutter {s : AbsState V} {m : Mem V} {s' : AbsState V} {m' : Mem V}
      {as : List (Action V)} {rs : List (Result V)} {s'' : AbsState V} {m'' : Mem V}
      (h : ObservedStep z C limit hC s m none none s' m')
      (hs : ObservedSteps z C limit hC s' m' as rs s'' m'') :
      ObservedSteps z C limit hC s m as rs s'' m''
  | step {s : AbsState V} {m : Mem V} {s' : AbsState V} {m' : Mem V}
      {a : Action V} {r : Result V} {as : List (Action V)} {rs : List (Result V)}
      {s'' : AbsState V} {m'' : Mem V}
      (h : ObservedStep z C limit hC s m (some a) (some r) s' m')
      (hs : ObservedSteps z C limit hC s' m' as rs s'' m'') :
      ObservedSteps z C limit hC s m (a :: as) (r :: rs) s'' m''

/-- Every observed trace refines an abstract transition trace.

A `none`/`none` observed step is either an event stutter or a failed
observation; both leave the abstract state unchanged, so the tail's
abstract trace is already the whole story. -/
theorem ObservedSteps.steps {z : V} {C limit : Nat} {hC : 0 < C}
    {s : AbsState V} {m : Mem V} {s' : AbsState V} {m' : Mem V}
    {as : List (Action V)} {rs : List (Result V)}
    (hs : ObservedSteps z C limit hC s m as rs s' m') :
    Steps C limit s as s' rs := by
  induction hs with
  | nil => exact Steps.nil
  | stutter h _ ih =>
      cases h with
      | event h => cases h; exact ih
      | obs kind hm legal => exact ih
  | step h _ ih => exact Steps.cons (ObservedStep.steps h) ih

/-- Every observed trace preserves the memory refinement. -/
theorem ObservedSteps.ref {z : V} {C limit : Nat} {hC : 0 < C}
    {s : AbsState V} {m : Mem V} {s' : AbsState V} {m' : Mem V}
    {as : List (Action V)} {rs : List (Result V)}
    (hm : Ref z C s m) (hs : ObservedSteps z C limit hC s m as rs s' m') :
    Ref z C s' m' := by
  revert hm
  induction hs with
  | nil => intro hm; exact hm
  | stutter h _ ih =>
      intro hm
      exact ih (ObservedStep.ref hm h)
  | step h _ ih =>
      intro hm
      exact ih (ObservedStep.ref hm h)

/-- Erase observations from a trace: every failed observation becomes an
`EventStep` stutter, so `ObservedSteps` is a conservative extension of the
shared-event layer. -/
theorem ObservedSteps.toEventSteps {z : V} {C limit : Nat} {hC : 0 < C}
    {s : AbsState V} {m : Mem V} {s' : AbsState V} {m' : Mem V}
    {as : List (Action V)} {rs : List (Result V)}
    (hs : ObservedSteps z C limit hC s m as rs s' m') :
    EventSteps z C limit hC s m as rs s' m' := by
  induction hs with
  | nil => exact EventSteps.nil
  | stutter h _ ih =>
      cases h with
      | event h =>
          cases h with
          | stutter hm => exact EventSteps.stutter (EventStep.stutter hm) ih
      | obs kind hm legal => exact EventSteps.stutter (EventStep.stutter hm) ih
  | step h _ ih =>
      cases h with
      | event h => exact EventSteps.step h ih

end Mpmc
