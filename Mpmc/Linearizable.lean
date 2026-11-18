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
  FIFO / linearizability facts for the abstract machine.

  `pushLabels_eq_range'` and `popLabels_eq_range'` (in `Mpmc.Abstract`) show
  that successful pushes return 0, 1, 2, ... and successful pops consume
  0, 1, 2, ... in order.  This file adds the value half: the values pushed
  are exactly the final values at positions `s0.W, s0.W+1, ...`, the value
  returned by the n-th successful pop is exactly the value stored at
  position n, and a value at a published position is never rewritten.

  Together these are the functional content of linearizability: the trace
  order is a legal sequential FIFO history, and each operation's response is
  the one that history assigns to it.  Real-time order is a property of the
  concrete execution (every operation's cell CAS happens between its call and
  its return); see `docs/proof.md`.
-/

import Mpmc.Abstract

namespace Mpmc

variable {V : Type}

/-- A transition never changes a value below the write counter. -/
theorem Step.val_lt_W {C limit : Nat} {s s' : AbsState V}
    {a : Action V} {r : Result V} (h : Step C limit s a s' r)
    {i : Nat} (hi : i < s.W) : s'.val i = s.val i := by
  cases h with
  | push hw hocc hlim =>
      dsimp
      have hne : i ≠ s.W := by omega
      simp [hne]
  | pop => rfl
  | helpW => rfl
  | helpR => rfl

/-- A whole run never changes a value below its starting write counter. -/
theorem Steps.val_lt_W {C limit : Nat} {s s' : AbsState V}
    {as : List (Action V)} {rs : List (Result V)}
    (h : Steps C limit s as s' rs) (i : Nat) (hi : i < s.W) :
    s'.val i = s.val i := by
  induction h with
  | nil => rfl
  | cons hstep htail ih =>
      rename_i s0' s1' sf' act res as' rs'
      have hi1 : i < s1'.W := Nat.lt_of_lt_of_le hi hstep.W_mono
      rw [ih hi1]
      exact hstep.val_lt_W hi

/-- A transition never changes a value below the read counter. -/
theorem Step.val_stable {C limit : Nat} {s s' : AbsState V}
    {a : Action V} {r : Result V} (hinv : Inv C limit s)
    (h : Step C limit s a s' r) {i : Nat} (hi : i < s.R) :
    s'.val i = s.val i := by
  cases h with
  | push hw hocc hlim =>
      dsimp
      have hne : i ≠ s.W := by
        have hRW := hinv.hR_le_W
        omega
      simp [hne]
  | pop => rfl
  | helpW => rfl
  | helpR => rfl

/-- A whole run never changes a value below its starting read counter. -/
theorem Steps.val_stable {C limit : Nat} {s s' : AbsState V}
    {as : List (Action V)} {rs : List (Result V)}
    (h : Steps C limit s as s' rs) (hinv : Inv C limit s)
    (i : Nat) (hi : i < s.R) : s'.val i = s.val i := by
  induction h with
  | nil => rfl
  | cons hstep htail ih =>
      rename_i s0' s1' sf' act res as' rs'
      have hinv1 : Inv C limit s1' := hinv.step hstep
      have hi1 : i < s1'.R := Nat.lt_of_lt_of_le hi hstep.R_mono
      rw [ih hinv1 hi1]
      exact hstep.val_stable hinv hi

/-- The values pushed by a run, in trace order. -/
def pushValues (as : List (Action V)) : List V :=
  as.filterMap fun
    | .push v => some v
    | _ => none

/-- The values returned by successful pops are exactly the values at
positions `s0.R, s0.R+1, ...` in the final state, in order. -/
theorem popValues_eq_map {C limit : Nat} {s0 sf : AbsState V}
    {as : List (Action V)} {rs : List (Result V)}
    (h : Steps C limit s0 as sf rs) (hinv : Inv C limit s0) :
    (popValues rs).map some =
      (List.range' s0.R (sf.R - s0.R)).map (fun i => sf.val i) := by
  induction h with
  | nil => simp [popValues]
  | cons hstep htail ih =>
      rename_i s0' s1' sf' act res as' rs'
      have hinv1 : Inv C limit s1' := hinv.step hstep
      simp only [popValues] at ih
      cases hstep with
      | push hw hocc hlim =>
          simp only [popValues, List.filterMap_cons]
          simpa using ih hinv1
      | helpW h =>
          simp only [popValues, List.filterMap_cons]
          simpa using ih hinv1
      | helpR h =>
          simp only [popValues, List.filterMap_cons]
          simpa using ih hinv1
      | pop hr hne hval =>
          simp only [popValues, List.filterMap_cons, List.map_cons]
          rw [ih hinv1]
          -- The tail starts at `s0'.R + 1`; peel the head of the range.
          have hmono : s0'.R + 1 ≤ sf'.R := htail.R_mono
          have hsub : sf'.R - s0'.R = (sf'.R - (s0'.R + 1)) + 1 := by omega
          rw [hsub]
          -- `List.range' s (n+1) = s :: List.range' (s+1) n`
          simp only [List.range', List.map_cons]
          -- The head value is stable under the rest of the run.
          have hstable : sf'.val s0'.R = s0'.val s0'.R := by
            exact Steps.val_stable (C := C) (limit := limit)
              (s := { s0' with R := s0'.R + 1 }) (s' := sf')
              (as := as') (rs := rs') htail hinv1 s0'.R
              (Nat.lt_succ_self _)
          rw [hstable, hval]

/-- A successful push stores its value at the position it publishes. -/
theorem Step.push_val {C limit : Nat} {s s' : AbsState V} {v : V}
    {r : Result V} (h : Step C limit s (.push v) s' r) :
    s'.val s.W = some v := by
  cases h with
  | push => simp

/-- The values pushed by a run are exactly the values at positions
`s0.W, s0.W+1, ...` in the final state, in order. -/
theorem pushValues_eq_map {C limit : Nat} {s0 sf : AbsState V}
    {as : List (Action V)} {rs : List (Result V)}
    (h : Steps C limit s0 as sf rs) (hinv : Inv C limit s0) :
    (pushValues as).map some =
      (List.range' s0.W (sf.W - s0.W)).map (fun i => sf.val i) := by
  induction h with
  | nil => simp [pushValues]
  | cons hstep htail ih =>
      rename_i s0' s1' sf' act res as' rs'
      have hinv1 : Inv C limit s1' := hinv.step hstep
      simp only [pushValues] at ih
      cases act with
      | push v =>
          simp only [pushValues, List.filterMap_cons, List.map_cons]
          rw [ih hinv1]
          have hW : s1'.W = s0'.W + 1 := by cases hstep; rfl
          have hmono : s1'.W ≤ sf'.W := htail.W_mono
          have hsub : sf'.W - s0'.W = (sf'.W - s1'.W) + 1 := by omega
          rw [hsub]
          simp only [List.range', List.map_cons]
          have hhead : sf'.val s0'.W = some v := by
            have hstable := Steps.val_lt_W htail s0'.W (by omega)
            rw [hstable]
            exact hstep.push_val
          rw [hhead, hW]
      | pop =>
          have hW : s1'.W = s0'.W := by cases hstep; rfl
          simp only [pushValues, List.filterMap_cons]
          simpa [hW] using ih hinv1
      | helpW =>
          have hW : s1'.W = s0'.W := by cases hstep; rfl
          simp only [pushValues, List.filterMap_cons]
          simpa [hW] using ih hinv1
      | helpR =>
          have hW : s1'.W = s0'.W := by cases hstep; rfl
          simp only [pushValues, List.filterMap_cons]
          simpa [hW] using ih hinv1

/-- FIFO, in one statement: push positions and pop positions are the
consecutive ranges starting from the initial counters. -/
theorem trace_fifo {C limit : Nat} {s0 sf : AbsState V}
    {as : List (Action V)} {rs : List (Result V)}
    (h : Steps C limit s0 as sf rs) (hinv : Inv C limit s0) :
    pushLabels rs = List.range' s0.W (sf.W - s0.W) ∧
      popLabels rs = List.range' s0.R (sf.R - s0.R) ∧
      (pushValues as).map some =
        (List.range' s0.W (sf.W - s0.W)).map (fun i => sf.val i) ∧
      (popValues rs).map some =
        (List.range' s0.R (sf.R - s0.R)).map (fun i => sf.val i) :=
  ⟨pushLabels_eq_range' h, popLabels_eq_range' h,
   pushValues_eq_map h hinv, popValues_eq_map h hinv⟩

end Mpmc
