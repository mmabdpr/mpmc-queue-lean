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
  Retry-charge counting lemma: a pending thread's failed cell compare-exchanges
  are charged to successful cell compare-exchanges by other threads.

  This is a conditional combinatorial core used in the lock-freedom argument,
  independent of the queue's payload and of the kernel control flow.  It is not
  itself a lock-freedom theorem; the chain premises must be instantiated from a
  kernel execution.

  * a thread loads the cell marker and later attempts a whole-cell CAS;
  * in the intended kernel instantiation, a failed attempt means the marker
    changed since the load, so at least one successful cell CAS on that slot
    happened in between;
  * after a failure the thread reloads, so the next failure needs a *later*
    successful CAS.  The intervals are disjoint, and therefore

        number of failed attempts <= number of successes by others.

  `Attempt.loaded` is the global count of successful cell CASes by other
  threads when the thread last loaded its slot; `Attempt.successes` is the
  count when the attempt is made.  `Attempt.ok` records the CAS outcome.
-/

namespace Mpmc

/-- One cell-CAS attempt by a pending thread. -/
structure Attempt where
  /-- Number of successful cell CASes by other threads at the last load. -/
  loaded : Nat
  /-- Number of successful cell CASes by other threads at the attempt. -/
  successes : Nat
  /-- Whether the whole-cell compare-exchange succeeded. -/
  ok : Bool
  deriving Repr, DecidableEq

/-- Number of failed attempts in a list. -/
def countFailures : List Attempt → Nat
  | [] => 0
  | a :: as => (if a.ok then 0 else 1) + countFailures as

/-- A chain of failed attempts of one thread.  `c` is the number of
successful CASes by others at the start; `cN` is the count after the last
recorded attempt.  Each failed attempt must have seen a strictly larger
count than at its load, and the next attempt's load is at least the count
at the previous attempt. -/
inductive PendingChain : Nat → List Attempt → Nat → Prop
  | nil (c : Nat) : PendingChain c [] c
  | cons {c cN : Nat} (a : Attempt)
      (hload : c ≤ a.loaded)
      (hlt : a.loaded < a.successes)
      (hok : a.ok = false)
      (hnext : PendingChain a.successes as cN) :
      PendingChain c (a :: as) cN

theorem PendingChain.start_le_end {c0 cN : Nat} {as : List Attempt}
    (h : PendingChain c0 as cN) : c0 ≤ cN := by
  induction h with
  | nil => exact Nat.le_refl _
  | cons a hload hlt hok hnext ih =>
      exact Nat.le_trans hload (Nat.le_trans (Nat.le_of_lt hlt) ih)

/-- A chain of failed attempts followed by one successful attempt. -/
inductive CompletedChain : Nat → List Attempt → Nat → Prop
  | last {c : Nat} (a : Attempt)
      (hload : c ≤ a.loaded) (hle : a.loaded ≤ a.successes)
      (hok : a.ok = true) :
      CompletedChain c [a] a.successes
  | cons {c cN : Nat} (a : Attempt)
      (hload : c ≤ a.loaded)
      (hlt : a.loaded < a.successes)
      (hok : a.ok = false)
      (hnext : CompletedChain a.successes as cN) :
      CompletedChain c (a :: as) cN

theorem CompletedChain.start_le_end {c0 cN : Nat} {as : List Attempt}
    (h : CompletedChain c0 as cN) : c0 ≤ cN := by
  induction h with
  | last a hload hle hok =>
      exact Nat.le_trans hload hle
  | cons a hload hlt hok hnext ih =>
      exact Nat.le_trans hload (Nat.le_trans (Nat.le_of_lt hlt) ih)

/-- A pending thread with `k` failures has seen at least `k` successful
cell CASes by other threads. -/
theorem pending_failures_le {c0 cN : Nat} {as : List Attempt}
    (h : PendingChain c0 as cN) : countFailures as ≤ cN - c0 := by
  induction as generalizing c0 cN with
  | nil =>
      cases h
      simp [countFailures]
  | cons a as ih =>
      cases h with
      | cons a hload hlt hok hnext =>
          have h1 := ih hnext
          have hle := PendingChain.start_le_end hnext
          simp [countFailures, hok]
          omega

/-- The same bound for a completed operation: all failures before the
successful attempt are charged to successes by other threads. -/
theorem completed_failures_le {c0 cN : Nat} {as : List Attempt}
    (h : CompletedChain c0 as cN) : countFailures as ≤ cN - c0 := by
  induction as generalizing c0 cN with
  | nil => cases h
  | cons a as ih =>
      cases h with
      | last a hload hle hok =>
          simp [countFailures, hok]
      | cons a hload hlt hok hnext =>
          have h1 := ih hnext
          have hle := CompletedChain.start_le_end hnext
          simp [countFailures, hok]
          omega

/-- Contrapositive form: if the number of successful cell CASes by other
threads is bounded, a pending thread cannot have more failed attempts than
that bound. -/
theorem pending_failures_bounded {c0 cN k : Nat} {as : List Attempt}
    (h : PendingChain c0 as cN) (hk : cN - c0 ≤ k) :
    countFailures as ≤ k :=
  Nat.le_trans (pending_failures_le h) hk

/-- Contrapositive form with an explicit success bound: if the number of
successes by other threads is at most `k + c0`, the pending chain has at most
`k` failures. -/
theorem pending_failures_bounded_of_successes {c0 cN k : Nat}
    {as : List Attempt} (h : PendingChain c0 as cN) (hk : cN ≤ k + c0) :
    countFailures as ≤ k := by
  have h1 : cN - c0 ≤ k := by omega
  exact pending_failures_bounded h h1

end Mpmc
