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
  Kernel-to-event bridge, part 1: the multi-thread state and the
  shared-memory refinement relation.

  The generated kernel is a CFG over a per-thread register file and a shared
  array of cells plus two hints.  `Shared` is the part visible to every
  thread; `Local` is the part owned by one thread.  This file only sets up
  the state and the projection to the existing `MState`/`Mem` interfaces.
  The per-op simulation lemmas live below this layer.
-/

import Mpmc.KernelRef
import Mpmc.Concurrent

namespace Mpmc

open Mpmc.Kernel

/-- The part of the machine state shared by every thread.  The `value`
parameter of `Params` is per-thread and is therefore supplied by `Local`. -/
structure Shared where
  params : Params
  cells : Nat → KCell
  hintW : UInt64
  hintR : UInt64

/-- A thread is either running a block at operation `oi`, has returned a
status, or trapped. -/
inductive Phase where
  | running (pc oi : Nat)
  | returned (v : UInt64)
  | trapped
  deriving DecidableEq, Repr

/-- A thread's execution state.  `pc` is the current basic block and `oi`
the next operation inside it; when `oi` reaches the block length the
terminator executes. -/
structure Local where
  phase : Phase
  value : UInt64
  regs : Nat → UInt64
  out0 : UInt64
  out1 : UInt64

/-- The immutable role of a thread. -/
inductive Kind where
  | push
  | pop

/-- The program executed by a thread of each role. -/
def programOf : Kind → Program
  | .push => pushProgram
  | .pop => popProgram

/-- A global state with `n` threads. -/
structure GState (n : Nat) where
  shared : Shared
  locals : Fin n → Local

/-- Adapt a shared/local pair to the existing single-thread kernel state. -/
def toMState (sh : Shared) (loc : Local) : MState :=
  { params := { sh.params with value := loc.value }
    regs := loc.regs
    cells := sh.cells
    hintW := sh.hintW
    hintR := sh.hintR
    out0 := loc.out0
    out1 := loc.out1 }

/-- Extract the shared part after a kernel operation. -/
def Shared.after (sh : Shared) (st : MState) : Shared :=
  { sh with cells := st.cells, hintW := st.hintW, hintR := st.hintR }

/-- Extract the local part after a kernel operation. -/
def Local.after (loc : Local) (st : MState) : Local :=
  { loc with regs := st.regs, out0 := st.out0, out1 := st.out1 }

/-- Update one thread's local state. -/
def updLocal {n : Nat} (f : Fin n → Local) (i : Fin n) (x : Local) : Fin n → Local :=
  fun j => if j = i then x else f j

/-- The result of one operation-level step. -/
inductive OpResult where
  | running (pc oi : Nat) (st : MState)
  | returned (v : UInt64) (st : MState)
  | trapped (st : MState)

/-- Execute one operation, or the block terminator when all operations of
the block have been executed.  This is the operational model used for the
concurrent simulation: each `execOp` is one atomic step. -/
def opStep (p : Program) (pc oi : Nat) (st : MState) : OpResult :=
  match p.blocks[pc]? with
  | none => .trapped st
  | some b =>
      match b.ops[oi]? with
      | some op => .running pc (oi + 1) (execOp op st)
      | none =>
          match b.term with
          | .goto n => .running n 0 st
          | .branch c t f => .running (if eval c st ≠ 0 then t else f) 0 st
          | .ret e => .returned (eval e st) st
          | .trap => .trapped st

/-- One global step: thread `i` executes one operation (or one terminator)
of its immutable role's program. -/
def GStep {n : Nat} (kind : Fin n → Kind) (g : GState n) (i : Fin n)
    (g' : GState n) : Prop :=
  let loc := g.locals i
  match loc.phase with
  | .running pc oi =>
      match opStep (programOf (kind i)) pc oi (toMState g.shared loc) with
      | .running pc' oi' st' =>
          g' = { shared := g.shared.after st'
                 locals := updLocal g.locals i
                   { loc.after st' with phase := .running pc' oi' } }
      | .returned v st' =>
          g' = { shared := g.shared.after st'
                 locals := updLocal g.locals i
                   { loc.after st' with phase := .returned v } }
      | .trapped st' =>
          g' = { shared := g.shared.after st'
                 locals := updLocal g.locals i
                   { loc.after st' with phase := .trapped } }
  | _ => False

/-- Immutable configuration facts shared by every thread. -/
structure ConfigOK (C limit : Nat) (sh : Shared) : Prop where
  hC : 0 < C
  hCpow : ∃ k, C = 2 ^ k
  hCmax : C ≤ 2 ^ 24
  hbound : limit < 2 ^ 63
  hlimitC : limit + C ≤ 2 ^ 63

/-- The shared projection as abstract memory. -/
def Shared.toMem (sh : Shared) : Mem UInt64 :=
  { w := sh.hintW.toNat
    r := sh.hintR.toNat
    cells := fun j => kcellToCell (sh.cells j) }

/-- Shared-memory refinement: the geometry, hints, and every cell slot agree
with the abstract state.  This is `KRef` with the per-thread registers
removed. -/
structure SharedRef (C limit : Nat) (s : AbsState UInt64) (sh : Shared) : Prop where
  hcap : sh.params.capacity.toNat = C
  hmask : sh.params.mask.toNat = C - 1
  hlimit : sh.params.limit.toNat = limit
  hw : sh.hintW.toNat = s.w
  hr : sh.hintR.toNat = s.r
  hcells : ∀ j, j < C → kcellToCell (sh.cells j) = viewCell 0 C s j

theorem SharedRef.ref {C limit : Nat} {s : AbsState UInt64} {sh : Shared}
    (h : SharedRef C limit s sh) : Ref 0 C s sh.toMem :=
  ⟨h.hw, h.hr, h.hcells⟩

/-- A `SharedRef` gives the same `KRef` for any local register file. -/
theorem SharedRef.toKRef {C limit : Nat} {s : AbsState UInt64} {sh : Shared}
    (h : SharedRef C limit s sh) (loc : Local) :
    KRef C limit s (toMState sh loc) where
  hcap := h.hcap
  hmask := h.hmask
  hlimit := h.hlimit
  hw := h.hw
  hr := h.hr
  hcells := h.hcells

/-- The abstract memory after a successful write-hint advance. -/
theorem Shared.toMem_setHintW (sh : Shared) (v : UInt64) :
    Shared.toMem { sh with hintW := v } = { Shared.toMem sh with w := v.toNat } := by
  rfl

/-- The abstract memory after a successful read-hint advance. -/
theorem Shared.toMem_setHintR (sh : Shared) (v : UInt64) :
    Shared.toMem { sh with hintR := v } = { Shared.toMem sh with r := v.toNat } := by
  rfl

/-- A successful write-hint help CAS is an abstract `helpW` event.  The
stale snapshot enters only through the marker lower bound; the current cell
need not equal the snapshot. -/
theorem helpW_event_of_snapshot {C limit : Nat} {s : AbsState UInt64} {sh : Shared}
    (hi : Inv C limit s) (hs : SharedRef C limit s sh) (hC : 0 < C)
    {h : Nat} (hintEq : sh.hintW.toNat = h) (hle : h ≤ s.w)
    (hmark : 2 * h < ((Shared.toMem sh).cells (h % C)).marker) :
    EventStep 0 C limit hC s (Shared.toMem sh) (some .helpW) (some .helped)
      { s with w := s.w + 1 } { Shared.toMem sh with w := h + 1 } := by
  have hhw : sh.hintW.toNat = s.w := hs.hw
  have hwEq : s.w = h := by omega
  have hcellView : (Shared.toMem sh).cells (h % C) = viewCell 0 C s (h % C) := by
    simpa [Shared.toMem] using hs.hcells (h % C) (Nat.mod_lt _ hC)
  have hmark' : 2 * h < (viewCell 0 C s (h % C)).marker := by
    simpa [hcellView] using hmark
  have hlt : h < s.W := helpW_of_marker_gt hi hC hle hmark'
  have hWle : s.W ≤ h + 1 := by
    have hstep := hi.hW_le_w
    omega
  have hW : s.W = h + 1 := Nat.le_antisymm hWle hlt
  have hmw : (Shared.toMem sh).w = h := by simpa [Shared.toMem] using hintEq
  exact EventStep.helpW hi (SharedRef.ref hs) hmw hW

/-- A successful read-hint help CAS is an abstract `helpR` event. -/
theorem helpR_event_of_snapshot {C limit : Nat} {s : AbsState UInt64} {sh : Shared}
    (hi : Inv C limit s) (hs : SharedRef C limit s sh) (hC : 0 < C)
    {h : Nat} (hintEq : sh.hintR.toNat = h) (hle : h ≤ s.r)
    (hmark : 2 * h + 1 < ((Shared.toMem sh).cells (h % C)).marker) :
    EventStep 0 C limit hC s (Shared.toMem sh) (some .helpR) (some .helped)
      { s with r := s.r + 1 } { Shared.toMem sh with r := h + 1 } := by
  have hhr : sh.hintR.toNat = s.r := hs.hr
  have hrEq : s.r = h := by omega
  have hcellView : (Shared.toMem sh).cells (h % C) = viewCell 0 C s (h % C) := by
    simpa [Shared.toMem] using hs.hcells (h % C) (Nat.mod_lt _ hC)
  have hmark' : 2 * h + 1 < (viewCell 0 C s (h % C)).marker := by
    simpa [hcellView] using hmark
  have hlt : h < s.R := helpR_of_marker_gt hi hC hle hmark'
  have hRle : s.R ≤ h + 1 := by
    have hstep := hi.hR_le_r
    omega
  have hR : s.R = h + 1 := Nat.le_antisymm hRle hlt
  have hmr : (Shared.toMem sh).r = h := by simpa [Shared.toMem] using hintEq
  exact EventStep.helpR hi (SharedRef.ref hs) hmr hR

/-- A `UInt64.ofNat` whose argument is in range has the expected `toNat`. -/
theorem uint64_toNat_ofNat_of_lt {n : Nat} (h : n < 2 ^ 64) :
    (UInt64.ofNat n).toNat = n := by
  rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt h]

/-- The register shape at the push cell CAS (block 3, operation 2).  `h` is
the hint value the thread loaded. -/
structure PushCasReady (C limit : Nat) (s : AbsState UInt64) (sh : Shared)
    (loc : Local) (h : Nat) : Prop where
  hpc : loc.phase = .running 3 2
  hintEq : loc.regs rHint = UInt64.ofNat h
  hintLe : h ≤ s.w
  hlim : h < limit
  slotEq : loc.regs rSlot = UInt64.ofNat (h % C)
  markerEq : loc.regs rMarker = UInt64.ofNat (2 * h)
  payloadEq : loc.regs rPayload = 0
  desMarker : loc.regs rTmp0 = UInt64.ofNat (2 * h + 1)
  desPayload : loc.regs rTmp1 = loc.value
  cellEq : sh.cells (h % C) = ⟨UInt64.ofNat (2 * h), 0⟩

/-- A successful push cell CAS is exactly one abstract push event. -/
theorem pushCas_event {C limit : Nat} {s : AbsState UInt64} {sh : Shared}
    {loc : Local} {h : Nat}
    (hi : Inv C limit s) (hs : SharedRef C limit s sh) (hC : 0 < C)
    (h2 : 2 * h + 1 < 2 ^ 64) (hr : PushCasReady C limit s sh loc h) :
    ∃ st', opStep pushProgram 3 2 (toMState sh loc) = .running 3 3 st' ∧
      EventStep 0 C limit hC s (Shared.toMem sh)
        (some (.push loc.value)) (some (.pushed h))
        (pushState s loc.value) (Shared.toMem (sh.after st')) := by
  let st := toMState sh loc
  have hmodle : h % C ≤ h := Nat.mod_le h C
  have h2h : 2 * h < 2 ^ 64 := by omega
  have hmodbound : h % C < 2 ^ 64 := by
    exact Nat.lt_of_le_of_lt hmodle (by omega)
  have hslotNat : (loc.regs rSlot).toNat = h % C := by
    rw [hr.slotEq, uint64_toNat_ofNat_of_lt hmodbound]
  have hmarkerNat : (loc.regs rMarker).toNat = 2 * h := by
    rw [hr.markerEq, uint64_toNat_ofNat_of_lt h2h]
  have hmarkerU : (UInt64.ofNat (2 * h)).toNat = 2 * h :=
    uint64_toNat_ofNat_of_lt h2h
  have hmarkerFull : (UInt64.ofNat (2 * h + 1)).toNat = 2 * h + 1 :=
    uint64_toNat_ofNat_of_lt h2
  have hcellMem : (Shared.toMem sh).cells (h % C) = emptyCell 0 h := by
    simp [Shared.toMem, kcellToCell, emptyCell, hr.cellEq, hmarkerU, h2h]
  have hcond : (toMState sh loc).cells ((toMState sh loc).regs rSlot).toNat =
      { marker := (toMState sh loc).regs rMarker,
        payload := (toMState sh loc).regs rPayload } := by
    dsimp [toMState]
    rw [hslotNat, hr.cellEq, hr.markerEq, hr.payloadEq]
  have hcondEval : st.cells (eval (.var rSlot) st).toNat =
      { marker := eval (.var rMarker) st, payload := eval (.var rPayload) st } := by
    simpa [eval, st] using hcond
  let st' : MState :=
    { st with
      cells := upd st.cells (h % C) ⟨UInt64.ofNat (2 * h + 1), loc.value⟩
      regs := upd st.regs rOk 1 }
  have hstep :
      execOp (.casCell rOk (.var rSlot) (.var rMarker) (.var rPayload)
        (.var rTmp0) (.var rTmp1) .seqCst .seqCst) st = st' := by
    simp only [execOp]
    by_cases hcase : st.cells (eval (.var rSlot) st).toNat =
        { marker := eval (.var rMarker) st, payload := eval (.var rPayload) st }
    · rw [if_pos hcase]
      simp [eval, st, st', toMState, hslotNat, hr.desMarker, hr.desPayload]
    · exfalso
      exact hcase hcondEval
  have hop : opStep pushProgram 3 2 st = .running 3 3 st' := by
    simp [opStep, pushProgram, st, st', hstep]
  refine ⟨st', hop, ?_⟩
  have hfull : kcellToCell (⟨UInt64.ofNat (2 * h + 1), loc.value⟩ : KCell) =
      fullCell h loc.value := by
    dsimp [kcellToCell, fullCell]
    rw [hmarkerFull]
  have hmem : Shared.toMem (sh.after st') =
      (Shared.toMem sh).setCell (h % C) (fullCell h loc.value) := by
    apply Mem.ext'
    · rfl
    · rfl
    · intro j
      by_cases hj : j = h % C
      · subst j
        simp only [Shared.toMem, Shared.after, Mem.setCell, st', st, toMState]
        rw [upd_self]
        exact hfull
      · simp only [Shared.toMem, Shared.after, Mem.setCell, st', st, toMState]
        simp [upd_ne, hj]
  rw [hmem]
  exact EventStep.push hi (SharedRef.ref hs) hr.hintLe hr.hlim hcellMem loc.value

/-- The register shape at the pop cell CAS (block 7, operation 2). -/
structure PopCasReady (C limit : Nat) (s : AbsState UInt64) (sh : Shared)
    (loc : Local) (h : Nat) (p : UInt64) : Prop where
  hpc : loc.phase = .running 7 2
  hintEq : loc.regs rHint = UInt64.ofNat h
  hintLe : h ≤ s.r
  hlim : h < limit
  slotEq : loc.regs rSlot = UInt64.ofNat (h % C)
  markerEq : loc.regs rMarker = UInt64.ofNat (2 * h + 1)
  payloadEq : loc.regs rPayload = p
  desMarker : loc.regs rTmp0 = UInt64.ofNat (2 * (h + C))
  desPayload : loc.regs rTmp1 = 0
  cellEq : sh.cells (h % C) = ⟨UInt64.ofNat (2 * h + 1), p⟩

/-- A successful pop cell CAS is exactly one abstract pop event. -/
theorem popCas_event {C limit : Nat} {s : AbsState UInt64} {sh : Shared}
    {loc : Local} {h : Nat} {p : UInt64}
    (hi : Inv C limit s) (hs : SharedRef C limit s sh) (hC : 0 < C)
    (h2h : 2 * h + 1 < 2 ^ 64) (h2c : 2 * (h + C) < 2 ^ 64)
    (hr : PopCasReady C limit s sh loc h p) :
    ∃ st', opStep popProgram 7 2 (toMState sh loc) = .running 7 3 st' ∧
      EventStep 0 C limit hC s (Shared.toMem sh)
        (some .pop) (some (.popped h p))
        (popState s) (Shared.toMem (sh.after st')) := by
  let st := toMState sh loc
  have hmodle : h % C ≤ h := Nat.mod_le h C
  have hmodbound : h % C < 2 ^ 64 := by
    exact Nat.lt_of_le_of_lt hmodle (by omega)
  have hslotNat : (loc.regs rSlot).toNat = h % C := by
    rw [hr.slotEq, uint64_toNat_ofNat_of_lt hmodbound]
  have hmarkerNat : (loc.regs rMarker).toNat = 2 * h + 1 := by
    rw [hr.markerEq, uint64_toNat_ofNat_of_lt h2h]
  have hmarkerU : (UInt64.ofNat (2 * h + 1)).toNat = 2 * h + 1 :=
    uint64_toNat_ofNat_of_lt h2h
  have hmarkerEmpty : (UInt64.ofNat (2 * (h + C))).toNat = 2 * (h + C) :=
    uint64_toNat_ofNat_of_lt h2c
  have hcellMem : (Shared.toMem sh).cells (h % C) = fullCell h p := by
    simp [Shared.toMem, kcellToCell, fullCell, hr.cellEq, hmarkerU, h2h]
  have hcondEval : st.cells (eval (.var rSlot) st).toNat =
      { marker := eval (.var rMarker) st, payload := eval (.var rPayload) st } := by
    dsimp [st, toMState, eval]
    rw [hslotNat, hr.cellEq, hr.markerEq, hr.payloadEq]
  let st' : MState :=
    { st with
      cells := upd st.cells (h % C) ⟨UInt64.ofNat (2 * (h + C)), 0⟩
      regs := upd st.regs rOk 1 }
  have hstep :
      execOp (.casCell rOk (.var rSlot) (.var rMarker) (.var rPayload)
        (.var rTmp0) (.var rTmp1) .seqCst .seqCst) st = st' := by
    simp only [execOp]
    by_cases hcase : st.cells (eval (.var rSlot) st).toNat =
        { marker := eval (.var rMarker) st, payload := eval (.var rPayload) st }
    · rw [if_pos hcase]
      simp [eval, st, st', toMState, hslotNat, hr.desMarker, hr.desPayload]
    · exfalso
      exact hcase hcondEval
  have hop : opStep popProgram 7 2 st = .running 7 3 st' := by
    simp [opStep, popProgram, st, st', hstep]
  refine ⟨st', hop, ?_⟩
  have hempty : kcellToCell (⟨UInt64.ofNat (2 * (h + C)), 0⟩ : KCell) =
      emptyCell 0 (h + C) := by
    dsimp [kcellToCell, emptyCell]
    rw [hmarkerEmpty]
  have hmem : Shared.toMem (sh.after st') =
      (Shared.toMem sh).setCell (h % C) (emptyCell 0 (h + C)) := by
    apply Mem.ext'
    · rfl
    · rfl
    · intro j
      by_cases hj : j = h % C
      · subst j
        simp only [Shared.toMem, Shared.after, Mem.setCell, st', st, toMState]
        rw [upd_self]
        exact hempty
      · simp only [Shared.toMem, Shared.after, Mem.setCell, st', st, toMState]
        simp [upd_ne, hj]
  rw [hmem]
  exact EventStep.pop hi (SharedRef.ref hs) hr.hintLe hr.hlim p hcellMem

/-- The register shape at a push help hint CAS (block 4 operation 2, or
block 7 operation 1). -/
structure PushHintReady (C limit : Nat) (s : AbsState UInt64) (sh : Shared)
    (loc : Local) (h : Nat) : Prop where
  hintEq : sh.hintW.toNat = h
  hintReg : loc.regs rHint = UInt64.ofNat h
  hle : h ≤ s.w
  hmark : 2 * h < ((Shared.toMem sh).cells (h % C)).marker
  desHint : loc.regs rTmp2 = UInt64.ofNat (h + 1)

/-- A successful write-hint CAS is one abstract `helpW` event. -/
theorem pushHint_event {C limit : Nat} {s : AbsState UInt64} {sh : Shared}
    {loc : Local} {h : Nat}
    (hi : Inv C limit s) (hs : SharedRef C limit s sh) (hC : 0 < C)
    (h2h1 : h + 1 < 2 ^ 64) (hr : PushHintReady C limit s sh loc h) :
    ∃ st',
      execOp (.casHint rOk .write (.var rHint) (.var rTmp2) .release)
        (toMState sh loc) = st' ∧
      EventStep 0 C limit hC s (Shared.toMem sh)
        (some .helpW) (some .helped)
        { s with w := s.w + 1 } (Shared.toMem (sh.after st')) := by
  let st := toMState sh loc
  have hhintU : sh.hintW = UInt64.ofNat h := by
    apply UInt64.toNat_inj.mp
    rw [hr.hintEq, uint64_toNat_ofNat_of_lt (by omega)]
  have hdes : loc.regs rTmp2 = UInt64.ofNat (h + 1) := hr.desHint
  let st' : MState :=
    { st with
      hintW := loc.regs rTmp2
      regs := upd st.regs rOk 1 }
  have hcond : st.hintW = st.regs rHint := by
    dsimp [st, toMState]
    rw [hhintU, hr.hintReg]
  have hstep :
      execOp (.casHint rOk .write (.var rHint) (.var rTmp2) .release) st = st' := by
    simp [execOp, eval, st, st', hcond]
    rfl
  refine ⟨st', hstep, ?_⟩
  have hmem : Shared.toMem (sh.after st') =
      { Shared.toMem sh with w := h + 1 } := by
    apply Mem.ext'
    · dsimp [Shared.after, st', Shared.toMem]
      rw [hdes]
      exact uint64_toNat_ofNat_of_lt h2h1
    · rfl
    · intro j; rfl
  rw [hmem]
  exact helpW_event_of_snapshot hi hs hC hr.hintEq hr.hle hr.hmark

/-- The register shape at a pop help hint CAS. -/
structure PopHintReady (C limit : Nat) (s : AbsState UInt64) (sh : Shared)
    (loc : Local) (h : Nat) : Prop where
  hintEq : sh.hintR.toNat = h
  hintReg : loc.regs rHint = UInt64.ofNat h
  hle : h ≤ s.r
  hmark : 2 * h + 1 < ((Shared.toMem sh).cells (h % C)).marker
  desHint : loc.regs rTmp2 = UInt64.ofNat (h + 1)

/-- A successful read-hint CAS is one abstract `helpR` event. -/
theorem popHint_event {C limit : Nat} {s : AbsState UInt64} {sh : Shared}
    {loc : Local} {h : Nat}
    (hi : Inv C limit s) (hs : SharedRef C limit s sh) (hC : 0 < C)
    (h2h1 : h + 1 < 2 ^ 64) (hr : PopHintReady C limit s sh loc h) :
    ∃ st',
      execOp (.casHint rOk .read (.var rHint) (.var rTmp2) .release)
        (toMState sh loc) = st' ∧
      EventStep 0 C limit hC s (Shared.toMem sh)
        (some .helpR) (some .helped)
        { s with r := s.r + 1 } (Shared.toMem (sh.after st')) := by
  let st := toMState sh loc
  have hhintU : sh.hintR = UInt64.ofNat h := by
    apply UInt64.toNat_inj.mp
    rw [hr.hintEq, uint64_toNat_ofNat_of_lt (by omega)]
  let st' : MState :=
    { st with
      hintR := loc.regs rTmp2
      regs := upd st.regs rOk 1 }
  have hcond : st.hintR = st.regs rHint := by
    dsimp [st, toMState]
    rw [hhintU, hr.hintReg]
  have hstep :
      execOp (.casHint rOk .read (.var rHint) (.var rTmp2) .release) st = st' := by
    simp [execOp, eval, st, st', hcond]
    rfl
  refine ⟨st', hstep, ?_⟩
  have hmem : Shared.toMem (sh.after st') =
      { Shared.toMem sh with r := h + 1 } := by
    apply Mem.ext'
    · rfl
    · dsimp [Shared.after, st', Shared.toMem]
      rw [hr.desHint]
      exact uint64_toNat_ofNat_of_lt h2h1
    · intro j; rfl
  rw [hmem]
  exact helpR_event_of_snapshot hi hs hC hr.hintEq hr.hle hr.hmark

/-- The concrete initial shared state used by the C initializer: all slots
hold the empty cell for their slot index, both hints are zero. -/
def initShared (C limit : Nat) : Shared :=
  { params :=
      { capacity := UInt64.ofNat C
        mask := UInt64.ofNat (C - 1)
        limit := UInt64.ofNat limit
        value := 0 }
    cells := fun j => ⟨UInt64.ofNat (2 * j), 0⟩
    hintW := 0
    hintR := 0 }

/-- The concrete initial shared state refines the abstract initial state. -/
theorem initShared_ref {C limit : Nat}
    (hC : 0 < C) (hCmax : C ≤ 2 ^ 24) (hlimit : limit < 2 ^ 63) :
    SharedRef C limit (initial UInt64) (initShared C limit) := by
  have hC64 : C < 2 ^ 64 := by omega
  have hCm1 : C - 1 < 2 ^ 64 := by omega
  have hlim64 : limit < 2 ^ 64 := by omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [initShared, uint64_toNat_ofNat_of_lt hC64]
  · simp [initShared, uint64_toNat_ofNat_of_lt hCm1]
  · simp [initShared, uint64_toNat_ofNat_of_lt hlim64]
  · simp [initShared, initial]
  · simp [initShared, initial]
  · intro j hj
    have hjC : j < C := hj
    have hsub : C - 1 - j < C := by omega
    have hq : (C - 1 - j) / C = 0 := Nat.div_eq_of_lt hsub
    have hsp : slotPos 0 j C = j := by
      simp [slotPos, slotQ, hq]
    have h2j : 2 * j < 2 ^ 64 := by omega
    dsimp [Shared.toMem, kcellToCell, initShared, viewCell, initial, emptyCell]
    rw [hsp]
    simp [uint64_toNat_ofNat_of_lt h2j]
    exact h2j

end Mpmc
