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
  Tagged kernel execution: every global kernel step has an `Effect` tag, and
  a finite schedule is an `Exec` with a parallel tag list.
-/

import Mpmc.Effect
import Mpmc.KernelLoadObs
import Mpmc.KernelTrace

namespace Mpmc

open Mpmc.Kernel

/-- Every global kernel step has a tagged effect.  Besides events and
stutters, this version recognizes the legal `pushFull` observation at the
push cell load; the generic fallback is the same simulation as
`gstep_sim`. -/
theorem gstep_effect {n C limit k : Nat} {kind : Fin n → Kind} {s : AbsState UInt64}
    {g g' : GState n} {i : Fin n}
    (hi : Inv C limit s) (hg : GRef C limit kind s g)
    (hC : 0 < C) (hpow : C = 2 ^ k) (hCmax : C ≤ 2 ^ 24)
    (hbound : limit < 2 ^ 63) (hlimitC : limit + C ≤ 2 ^ 63)
    (hstep : GStep kind g i g') :
    ∃ s' : AbsState UInt64, ∃ tag : StepTag UInt64,
      GRef C limit kind s' g' ∧ Inv C limit s' ∧
      Effect 0 C limit hC s (Shared.toMem g.shared) s' (Shared.toMem g'.shared) tag := by
  have hgeneric : ∃ s' : AbsState UInt64, ∃ tag : StepTag UInt64,
      GRef C limit kind s' g' ∧ Inv C limit s' ∧
      Effect 0 C limit hC s (Shared.toMem g.shared) s' (Shared.toMem g'.shared) tag := by
    obtain ⟨s', hg', hev | ⟨hs_eq, hshared⟩⟩ :=
      gstep_sim hi hg hC hpow hCmax hbound hlimitC hstep
    · obtain ⟨a, res, hev⟩ := hev
      exact ⟨s', .event a res, hg', Inv.step hi (EventStep.step hev),
        Effect.event a res hev⟩
    · have hmem : Shared.toMem g'.shared = Shared.toMem g.shared := by rw [hshared]
      cases hphase : (g'.locals i).phase with
      | returned v =>
          exact ⟨s', .ret v, hg', by simpa [hs_eq] using hi,
            Effect.ret v (SharedRef.ref hg.hshared) hs_eq hmem⟩
      | running pc oi =>
          exact ⟨s', .stutter, hg', by simpa [hs_eq] using hi,
            Effect.stutter (SharedRef.ref hg.hshared) hs_eq hmem⟩
      | trapped =>
          exact ⟨s', .stutter, hg', by simpa [hs_eq] using hi,
            Effect.stutter (SharedRef.ref hg.hshared) hs_eq hmem⟩
  cases hk : kind i with
  | push =>
      cases hp : (g.locals i).phase with
      | running pc oi =>
          by_cases hexh : pc = 0 ∧ oi = 1
          · have hphase : (g.locals i).phase = Phase.running 0 1 := by
              rw [hp]
              rcases hexh with ⟨rfl, rfl⟩
              rfl
            by_cases hge : limit ≤ ((g.locals i).regs rHint).toNat
            · obtain ⟨s', tag, hg', hi', heff, _⟩ :=
                push_horizon_exhausted_effect hi hg hC hpow hCmax hbound hlimitC
                  hk hphase hstep hge
              exact ⟨s', tag, hg', hi', heff⟩
            · exact hgeneric
          · by_cases hpc : pc = 1 ∧ oi = 1
            · have hphase : (g.locals i).phase = Phase.running 1 1 := by
                rw [hp]
                rcases hpc with ⟨rfl, rfl⟩
                rfl
              by_cases hfull :
                  (g.shared.cells (((g.locals i).regs rSlot).toNat)).marker.toNat / 2 + C
                    = ((g.locals i).regs rHint).toNat
              · obtain ⟨s', tag, hg', hi', heff, _⟩ :=
                  push_load_full_effect hi hg hC hpow hCmax hbound hlimitC hk hphase hstep hfull
                exact ⟨s', tag, hg', hi', heff⟩
              · exact hgeneric
            · exact hgeneric
      | returned _ => exact hgeneric
      | trapped => exact hgeneric
  | pop =>
      cases hp : (g.locals i).phase with
      | running pc oi =>
          by_cases hexh : pc = 0 ∧ oi = 1
          · have hphase : (g.locals i).phase = Phase.running 0 1 := by
              rw [hp]
              rcases hexh with ⟨rfl, rfl⟩
              rfl
            by_cases hge : limit ≤ ((g.locals i).regs rHint).toNat
            · obtain ⟨s', tag, hg', hi', heff, _⟩ :=
                pop_horizon_exhausted_effect hi hg hC hpow hCmax hbound hlimitC
                  hk hphase hstep hge
              exact ⟨s', tag, hg', hi', heff⟩
            · exact hgeneric
          · by_cases hpc : pc = 1 ∧ oi = 1
            · have hphase : (g.locals i).phase = Phase.running 1 1 := by
                rw [hp]
                rcases hpc with ⟨rfl, rfl⟩
                rfl
              by_cases hempty :
                  (g.shared.cells (((g.locals i).regs rSlot).toNat)).marker.toNat / 2
                    = ((g.locals i).regs rHint).toNat
              · by_cases heven :
                    (g.shared.cells (((g.locals i).regs rSlot).toNat)).marker.toNat % 2 = 0
                · obtain ⟨s', tag, hg', hi', heff, _⟩ :=
                    pop_load_empty_effect hi hg hC hpow hCmax hbound hlimitC hk hphase hstep
                      hempty heven
                  exact ⟨s', tag, hg', hi', heff⟩
                · exact hgeneric
              · exact hgeneric
            · exact hgeneric
      | returned _ => exact hgeneric
      | trapped => exact hgeneric

/-- One move of a data-level schedule: a kernel step by a fixed thread, or a
fresh operation invocation. -/
inductive Move (n : Nat) where
  | step (i : Fin n)
  | invoke (i : Fin n) (v : UInt64)

/-- A finite tagged execution.  `tags` records the thread and the observable
label of every step, in order; invocations are stutters on the shared state. -/
inductive Exec {n : Nat} (kind : Fin n → Kind) (C limit : Nat) (hC : 0 < C) :
    AbsState UInt64 → GState n → List (Move n) → AbsState UInt64 → GState n →
      List (Fin n × StepTag UInt64) → Prop
  | nil {s : AbsState UInt64} {g : GState n} :
      Exec kind C limit hC s g [] s g []
  | step {s : AbsState UInt64} {g : GState n} {s' : AbsState UInt64} {g' : GState n}
      {i : Fin n} {tag : StepTag UInt64} {ms : List (Move n)}
      {s'' : AbsState UInt64} {g'' : GState n} {tags : List (Fin n × StepTag UInt64)}
      (hstep : GStep kind g i g')
      (heff : Effect 0 C limit hC s (Shared.toMem g.shared) s' (Shared.toMem g'.shared) tag)
      (hs : Exec kind C limit hC s' g' ms s'' g'' tags) :
      Exec kind C limit hC s g (Move.step i :: ms) s'' g'' ((i, tag) :: tags)
  | invoke {s : AbsState UInt64} {g : GState n} {i : Fin n} {v : UInt64} {g' : GState n}
      {ms : List (Move n)} {s' : AbsState UInt64} {g'' : GState n}
      {tags : List (Fin n × StepTag UInt64)}
      (h : GInvoke g i v g')
      (hg' : GRef C limit kind s g')
      (hshared : g'.shared = g.shared)
      (href : Ref 0 C s (Shared.toMem g.shared))
      (hs : Exec kind C limit hC s g' ms s' g'' tags) :
      Exec kind C limit hC s g (Move.invoke i v :: ms) s' g'' ((i, .stutter) :: tags)

/-- An invocation leaves the shared state unchanged. -/
theorem GInvoke.shared_eq {n : Nat} {g g' : GState n} {i : Fin n} {v : UInt64}
    (h : GInvoke g i v g') : g'.shared = g.shared := by
  rcases h with ⟨r, hphase, rfl⟩
  rfl

/-- Any `GPath` has a tagged `Exec`; this is the data-level schedule used by
history and progress. -/
theorem GPath.toExec {n C limit k : Nat} {kind : Fin n → Kind} {g g' : GState n}
    (hp : GPath kind g g')
    (s : AbsState UInt64) (hi : Inv C limit s) (hg : GRef C limit kind s g)
    (hC : 0 < C) (hpow : C = 2 ^ k) (hCmax : C ≤ 2 ^ 24)
    (hbound : limit < 2 ^ 63) (hlimitC : limit + C ≤ 2 ^ 63) :
    ∃ s' ms tags,
      Exec kind C limit hC s g ms s' g' tags := by
  induction hp generalizing s with
  | refl g => exact ⟨s, [], [], Exec.nil⟩
  | step i h hs ih =>
      obtain ⟨s1, tag, hg1, hi1, heff⟩ :=
        gstep_effect hi hg hC hpow hCmax hbound hlimitC h
      obtain ⟨s2, ms, tags, hexec⟩ := ih s1 hi1 hg1
      exact ⟨s2, Move.step i :: ms, (i, tag) :: tags, Exec.step h heff hexec⟩
  | invoke i v h hs ih =>
      obtain ⟨s2, ms, tags, hexec⟩ := ih s hi (GInvoke.gref hg h)
      exact ⟨s2, Move.invoke i v :: ms, (i, .stutter) :: tags,
        Exec.invoke h (GInvoke.gref hg h) (GInvoke.shared_eq h)
          (SharedRef.ref hg.hshared) hexec⟩

/-- A tagged execution projects to an `ObservedSteps` trace. -/
theorem Exec.observed {n C limit : Nat} {hC : 0 < C} {kind : Fin n → Kind}
    {s : AbsState UInt64} {g : GState n} {ms : List (Move n)}
    {s' : AbsState UInt64} {g' : GState n} {tags : List (Fin n × StepTag UInt64)}
    (h : Exec kind C limit hC s g ms s' g' tags) :
    ∃ as rs, ObservedSteps 0 C limit hC s (Shared.toMem g.shared) as rs
      s' (Shared.toMem g'.shared) := by
  induction h with
  | nil => exact ⟨[], [], ObservedSteps.nil⟩
  | @step s g s' g' i tag ms s'' g'' tags hstep heff hs ih =>
      obtain ⟨as, rs, hobs⟩ := ih
      cases tag with
      | stutter =>
          have hstepObs : ObservedStep 0 C limit hC s (Shared.toMem g.shared)
              none none s' (Shared.toMem g'.shared) := by
            simpa using heff.toObserved
          exact ⟨as, rs, ObservedSteps.stutter hstepObs hobs⟩
      | event a r =>
          have hstepObs : ObservedStep 0 C limit hC s (Shared.toMem g.shared)
              (some a) (some r) s' (Shared.toMem g'.shared) := by
            simpa using heff.toObserved
          exact ⟨a :: as, r :: rs, ObservedSteps.step hstepObs hobs⟩
      | obs k =>
          have hstepObs : ObservedStep 0 C limit hC s (Shared.toMem g.shared)
              none none s' (Shared.toMem g'.shared) := by
            simpa using heff.toObserved
          exact ⟨as, rs, ObservedSteps.stutter hstepObs hobs⟩
      | ret status =>
          have hstepObs : ObservedStep 0 C limit hC s (Shared.toMem g.shared)
              none none s' (Shared.toMem g'.shared) := by
            simpa using heff.toObserved
          exact ⟨as, rs, ObservedSteps.stutter hstepObs hobs⟩
  | @invoke s g i v g' ms s' g'' tags h hg' hshared href hs ih =>
      obtain ⟨as, rs, hobs⟩ := ih
      have hst : ObservedStep 0 C limit hC s (Shared.toMem g.shared)
          none none s (Shared.toMem g.shared) :=
        ObservedStep.event (EventStep.stutter href)
      have hobs' : ObservedSteps 0 C limit hC s (Shared.toMem g.shared) as rs
          s' (Shared.toMem g''.shared) := by
        simpa [hshared] using hobs
      exact ⟨as, rs, ObservedSteps.stutter hst hobs'⟩

/-- Number of kernel moves executed by thread `i` in a schedule. -/
def threadSteps {n : Nat} (i : Fin n) : List (Move n) → Nat
  | [] => 0
  | Move.step j :: ms => (if i = j then 1 else 0) + threadSteps i ms
  | Move.invoke _ _ :: ms => threadSteps i ms

/-- Whether a step tag is a successful abstract event (push, pop, or help). -/
def StepTag.isEvent : StepTag UInt64 → Bool
  | .event _ _ => true
  | _ => false

/-- Number of abstract events attributed to threads other than `i`. -/
def otherEvents {n : Nat} (i : Fin n) : List (Fin n × StepTag UInt64) → Nat
  | [] => 0
  | (j, t) :: ts =>
      (if j = i then 0 else if t.isEvent then 1 else 0) + otherEvents i ts

theorem threadSteps_le_length {n : Nat} (i : Fin n) (ms : List (Move n)) :
    threadSteps i ms ≤ ms.length := by
  induction ms with
  | nil => simp [threadSteps]
  | cons m ms ih =>
      cases m with
      | step j =>
          simp only [threadSteps, List.length_cons]
          split <;> omega
      | invoke j v =>
          simp only [threadSteps, List.length_cons]
          omega

theorem otherEvents_le_length {n : Nat} (i : Fin n)
    (tags : List (Fin n × StepTag UInt64)) :
    otherEvents i tags ≤ tags.length := by
  induction tags with
  | nil => simp [otherEvents]
  | cons p ts ih =>
      obtain ⟨j, t⟩ := p
      by_cases hji : j = i
      · simp only [otherEvents, if_pos hji, List.length_cons]
        omega
      · by_cases hev : t.isEvent
        · simp only [otherEvents, if_neg hji, if_pos hev, List.length_cons]
          omega
        · simp only [otherEvents, if_neg hji, if_neg hev, List.length_cons]
          omega

/-- A tagged execution has one tag per move. -/
theorem Exec.length_eq {n C limit : Nat} {hC : 0 < C} {kind : Fin n → Kind}
    {s : AbsState UInt64} {g : GState n} {ms : List (Move n)}
    {s' : AbsState UInt64} {g' : GState n}
    {tags : List (Fin n × StepTag UInt64)}
    (h : Exec kind C limit hC s g ms s' g' tags) :
    ms.length = tags.length := by
  induction h with
  | nil => rfl
  | step hstep heff hs ih =>
      simp only [List.length_cons, ih]
  | invoke h hg' hshared href hs ih =>
      simp only [List.length_cons, ih]

/-- If no tag in an execution is a cell event, every cell marker is
unchanged. -/
theorem Exec.cell_marker_eq_of_no_cell_events {n C limit : Nat} {hC : 0 < C}
    {kind : Fin n → Kind} {s : AbsState UInt64} {g : GState n}
    {ms : List (Move n)} {s' : AbsState UInt64} {g' : GState n}
    {tags : List (Fin n × StepTag UInt64)}
    (h : Exec kind C limit hC s g ms s' g' tags)
    (hnone : ∀ p, p ∈ tags → p.2.isCellEvent = false) (j : Nat) :
    ((Shared.toMem g'.shared).cells j).marker =
      ((Shared.toMem g.shared).cells j).marker := by
  induction h with
  | nil => rfl
  | @step s0 g0 s1 g1 i tag ms0 s2 g2 tags0 hstep heff hs ih =>
      have hhead : tag.isCellEvent = false := hnone (i, tag) (by simp)
      have htail : ∀ p, p ∈ tags0 → p.2.isCellEvent = false := by
        intro p hp
        exact hnone p (by simp [hp])
      have h1 := heff.cell_marker_eq_of_not_cellEvent hhead j
      have h2 := ih htail
      exact h2.trans h1
  | @invoke s0 g0 i v g1 ms0 s1 g2 tags0 h hg' hshared href hs ih =>
      have htail : ∀ p, p ∈ tags0 → p.2.isCellEvent = false := by
        intro p hp
        exact hnone p (by simp [hp])
      simpa [hshared] using ih htail

/-- A changed cell marker in a tagged execution witnesses at least one
successful cell event (push or pop), not merely a hint-help event. -/
theorem Exec.cell_event_of_marker_change {n C limit : Nat} {hC : 0 < C}
    {kind : Fin n → Kind} {s : AbsState UInt64} {g : GState n}
    {ms : List (Move n)} {s' : AbsState UInt64} {g' : GState n}
    {tags : List (Fin n × StepTag UInt64)} {j : Nat}
    (h : Exec kind C limit hC s g ms s' g' tags)
    (hchange : ((Shared.toMem g'.shared).cells j).marker ≠
      ((Shared.toMem g.shared).cells j).marker) :
    ∃ p, p ∈ tags ∧ p.2.isCellEvent = true := by
  by_cases hex : ∃ p, p ∈ tags ∧ p.2.isCellEvent = true
  · exact hex
  · have hnone : ∀ p, p ∈ tags → p.2.isCellEvent = false := by
      intro p hp
      cases hb : p.2.isCellEvent with
      | false => rfl
      | true => exact absurd ⟨p, hp, hb⟩ hex
    have heq := Exec.cell_marker_eq_of_no_cell_events h hnone j
    exact absurd heq hchange

end Mpmc
