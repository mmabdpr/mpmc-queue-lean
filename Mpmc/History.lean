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
  Real-time history packaging.

  The kernel simulation produces atomic observations (shared events or legal
  failure observations).  Each completed invocation is represented by a
  `TimedOp`: its invocation index, its linearization index, and its response
  index, together with the abstract action/result chosen at linearization.

  The only real-time obligation is the index inequality
  `lin ∈ [inv, ret]`; it immediately implies that a response-before-invocation
  pair is also ordered at the linearization points.  The abstract trace is
  kept as a separate `Steps` premise so this file does not duplicate the
  queue specification.
-/

import Mpmc.Linearizable
import Mpmc.Observed

namespace Mpmc

variable {V : Type}

/-- A completed invocation with its real-time interval and its abstract
linearization action/result. -/
structure TimedOp (V : Type) where
  inv : Nat
  lin : Nat
  ret : Nat
  action : Action V
  result : Result V
  inv_le_lin : inv ≤ lin
  lin_le_ret : lin ≤ ret

/-- Real-time order is respected at the linearization points. -/
theorem TimedOp.lin_lt_of_ret_lt_inv (a b : TimedOp V) (h : a.ret < b.inv) :
    a.lin < b.lin := by
  have h1 := a.inv_le_lin
  have h2 := a.lin_le_ret
  have h3 := b.inv_le_lin
  omega

/-- A real-time history: operations listed in linearization order. -/
structure History (V : Type) where
  ops : List (TimedOp V)
  lin_sorted : ops.Pairwise (fun a b => a.lin < b.lin)

/-- The action sequence in linearization order. -/
def History.actions (h : History V) : List (Action V) :=
  h.ops.map (fun op => op.action)

/-- The result sequence in linearization order. -/
def History.results (h : History V) : List (Result V) :=
  h.ops.map (fun op => op.result)

/-- The history is linearizable when its actions/results form an abstract
queue trace from `s₀`.  The caller supplies the abstract initial and final
states; this keeps the history layer independent of the queue invariant. -/
def History.Linearizes (h : History V) (C limit : Nat) (s₀ s' : AbsState V) : Prop :=
  Steps C limit s₀ h.actions s' h.results

/-- Every pair of operations in a history respects real-time order at their
linearization points. -/
theorem History.real_time_order (_h : History V) {a b : TimedOp V}
    (hrt : a.ret < b.inv) : a.lin < b.lin :=
  TimedOp.lin_lt_of_ret_lt_inv a b hrt

end Mpmc
