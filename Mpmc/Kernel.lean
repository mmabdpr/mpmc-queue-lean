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
  A small imperative kernel language for the queue's two hot loops.

  The same program is used three ways:

  * `Mpmc.Kernel.run` interprets it (differential testing, proofs);
  * `Mpmc.Codegen` prints it as C (the shipped kernel);
  * the protocol lemmas in `Mpmc.Protocol` describe what its cell CASes do.

  The language is small: 64-bit registers, whole-cell loads and
  compare-exchanges, cursor loads/CASes, output stores, and structured
  branches.  There are no function calls, no allocation, and no pointers
  inside the language; the printer turns slot indices into `mpmc_slots(q)[...]`.
-/

namespace Mpmc.Kernel

/-- Runtime parameters of a kernel invocation. -/
inductive Param where
  | capacity
  | mask
  | limit
  | value
  deriving DecidableEq, BEq, Repr

/-- Memory ordering annotation. -/
inductive MemOrd where
  | relaxed
  | acquire
  | release
  | acqRel
  | seqCst
  deriving DecidableEq, Repr

/-- Which cursor a hint operation addresses. -/
inductive Hint where
  | write
  | read
  deriving DecidableEq, Repr

/-- Expressions over registers, parameters, and 64-bit literals. -/
inductive Expr where
  | var (n : Nat)
  | param (p : Param)
  | lit (v : UInt64)
  | add (a b : Expr)
  | sub (a b : Expr)
  | mul (a b : Expr)
  | band (a b : Expr)
  | bor (a b : Expr)
  | shl (a b : Expr)
  | shr (a b : Expr)
  | eq (a b : Expr)
  | ne (a b : Expr)
  | ult (a b : Expr)
  | ule (a b : Expr)
  deriving Repr

/-- Kernel parameters.  `value` is only used by push. -/
structure Params where
  capacity : UInt64
  mask : UInt64
  limit : UInt64
  value : UInt64
  deriving Repr

/-- A cell in the kernel model. -/
structure KCell where
  marker : UInt64
  payload : UInt64
  deriving DecidableEq, Repr

/-- Machine state of the interpreter: registers, cell array, cursors, outputs. -/
structure MState where
  params : Params
  regs : Nat → UInt64
  cells : Nat → KCell
  hintW : UInt64
  hintR : UInt64
  out0 : UInt64
  out1 : UInt64

/-- Evaluate an expression. -/
def eval (e : Expr) (st : MState) : UInt64 :=
  match e with
  | .var n => st.regs n
  | .param .capacity => st.params.capacity
  | .param .mask => st.params.mask
  | .param .limit => st.params.limit
  | .param .value => st.params.value
  | .lit v => v
  | .add a b => eval a st + eval b st
  | .sub a b => eval a st - eval b st
  | .mul a b => eval a st * eval b st
  | .band a b => eval a st &&& eval b st
  | .bor a b => eval a st ||| eval b st
  | .shl a b => eval a st <<< eval b st
  | .shr a b => eval a st >>> eval b st
  | .eq a b => if eval a st = eval b st then 1 else 0
  | .ne a b => if eval a st = eval b st then 0 else 1
  | .ult a b => if eval a st < eval b st then 1 else 0
  | .ule a b => if eval a st ≤ eval b st then 1 else 0

/-- Operations.  `casCell`/`casHint` write 1 on success and 0 on failure.
`loadCell` reads the whole cell as one snapshot. -/
inductive Op where
  | set (r : Nat) (e : Expr)
  | loadCell (marker payload : Nat) (slot : Expr) (ord : MemOrd)
  | casCell (r : Nat) (slot : Expr) (em ep dm dp : Expr) (okOrd failOrd : MemOrd)
  | loadHint (r : Nat) (which : Hint) (ord : MemOrd)
  | casHint (r : Nat) (which : Hint) (expected desired : Expr) (ord : MemOrd)
  | storeOut (which : Nat) (e : Expr)
  deriving Repr

/-- Block terminators. -/
inductive Term where
  | goto (b : Nat)
  | branch (c : Expr) (t f : Nat)
  | ret (e : Expr)
  | trap
  deriving Repr

structure Block where
  ops : List Op
  term : Term
  deriving Repr

structure Program where
  name : String
  params : List Param
  regCount : Nat
  outCount : Nat
  blocks : List Block
  entry : Nat
  deriving Repr

/-- Point update of a function (the core library does not provide
`Function.update` without Mathlib). -/
def upd {α β : Type} [DecidableEq α] (f : α → β) (a : α) (b : β) : α → β :=
  fun x => if x = a then b else f x

@[simp] theorem upd_self {α β : Type} [DecidableEq α] (f : α → β) (a : α) (b : β) :
    upd f a b a = b := by simp [upd]

@[simp] theorem upd_ne {α β : Type} [DecidableEq α] (f : α → β) (a x : α) (b : β)
    (h : x ≠ a) : upd f a b x = f x := by simp [upd, h]

/-- Execute one operation. -/
def execOp (op : Op) (st : MState) : MState :=
  match op with
  | .set r e =>
      { st with regs := upd st.regs r (eval e st) }
  | .loadCell m p slot _ =>
      let c := st.cells (eval slot st).toNat
      { st with
        regs := upd (upd st.regs m c.marker) p c.payload }
  | .casCell r slot em ep dm dp _ _ =>
      let j := (eval slot st).toNat
      let expected : KCell := { marker := eval em st, payload := eval ep st }
      let desired : KCell := { marker := eval dm st, payload := eval dp st }
      if st.cells j = expected then
        { st with
          cells := upd st.cells j desired,
          regs := upd st.regs r 1 }
      else
        { st with regs := upd st.regs r 0 }
  | .loadHint r which _ =>
      let v := if which = .write then st.hintW else st.hintR
      { st with regs := upd st.regs r v }
  | .casHint r which expected desired _ =>
      let e := eval expected st
      let d := eval desired st
      let old := if which = .write then st.hintW else st.hintR
      if old = e then
        { st with
          hintW := if which = .write then d else st.hintW,
          hintR := if which = .read then d else st.hintR,
          regs := upd st.regs r 1 }
      else
        { st with regs := upd st.regs r 0 }
  | .storeOut which e =>
      { st with
        out0 := if which = 0 then eval e st else st.out0,
        out1 := if which = 1 then eval e st else st.out1 }

def execOps : List Op → MState → MState
  | [], st => st
  | op :: ops, st => execOps ops (execOp op st)

inductive ExecResult where
  | running (pc : Nat) (st : MState)
  | returned (v : UInt64) (st : MState)
  | trapped (st : MState)

/-- One basic-block step. -/
def step (p : Program) (pc : Nat) (st : MState) : ExecResult :=
  match p.blocks[pc]? with
  | none => .trapped st
  | some b =>
      let st' := execOps b.ops st
      match b.term with
      | .goto n => .running n st'
      | .branch c t f =>
          .running (if eval c st' ≠ 0 then t else f) st'
      | .ret e => .returned (eval e st') st'
      | .trap => .trapped st'

/-- Run with a fuel bound. -/
def run : Nat → Program → Nat → MState → ExecResult
  | 0, _, pc, st => .running pc st
  | fuel + 1, p, pc, st =>
      match step p pc st with
      | .running pc' st' => run fuel p pc' st'
      | r => r

/-- A fresh state for a single-threaded trace. -/
def initState (_p : Program) (params : Params) (cells : Nat → KCell)
    (hintW hintR : UInt64) : MState :=
  { params := params
    regs := fun _ => 0
    cells := cells
    hintW := hintW
    hintR := hintR
    out0 := 0
    out1 := 0 }

/-- Register names used by both kernels. -/
def rHint : Nat := 0
def rPos : Nat := 1
def rMarker : Nat := 2
def rPayload : Nat := 3
def rTmp0 : Nat := 4
def rTmp1 : Nat := 5
def rOk : Nat := 6
def rTmp2 : Nat := 7
def rSlot : Nat := 8

def half : UInt64 := UInt64.ofNat (2 ^ 63)

/-- Push.  Block indices:
0 load/limit, 1 slot/load/pos, 2 ready?, 3 cell CAS, 4 success,
5 behind, 6 FULL, 7 help, 8 ahead check, 9 EXHAUSTED, 10 retry fallback. -/
def pushProgram : Program :=
  { name := "mpmc_kernel_push"
    params := [.capacity, .mask, .limit, .value]
    regCount := 9
    outCount := 1
    entry := 0
    blocks := [
      { ops := [.loadHint rHint .write .acquire]
        term := .branch (.ult (.var rHint) (.param .limit)) 1 9 },
      { ops := [.set rSlot (.band (.var rHint) (.param .mask)),
                .loadCell rMarker rPayload (.var rSlot) .seqCst,
                .set rPos (.shr (.var rMarker) (.lit 1))]
        term := .branch (.eq (.var rPos) (.var rHint)) 2 5 },
      { ops := [.set rTmp0 (.band (.var rMarker) (.lit 1))]
        term := .branch (.eq (.var rTmp0) (.lit 0)) 3 7 },
      { ops := [.set rTmp0 (.add (.shl (.var rHint) (.lit 1)) (.lit 1)),
                .set rTmp1 (.param .value),
                .casCell rOk (.var rSlot) (.var rMarker) (.var rPayload)
                  (.var rTmp0) (.var rTmp1) .seqCst .seqCst]
        term := .branch (.eq (.var rOk) (.lit 0)) 0 4 },
      { ops := [.storeOut 0 (.var rHint),
                .set rTmp2 (.add (.var rHint) (.lit 1)),
                .casHint rOk .write (.var rHint) (.var rTmp2) .release]
        term := .ret (.lit 0) },
      { ops := [.set rPos (.sub (.var rHint) (.var rPos))]
        term := .branch (.eq (.var rPos) (.param .capacity)) 6 8 },
      { ops := []
        term := .ret (.lit 1) },
      { ops := [.set rTmp2 (.add (.var rHint) (.lit 1)),
                .casHint rOk .write (.var rHint) (.var rTmp2) .release]
        term := .goto 0 },
      { ops := []
        term := .branch (.ult (.lit half) (.var rPos)) 7 10 },
      { ops := []
        term := .ret (.lit 3) },
      { ops := []
        term := .goto 0 }
    ] }

/-- Pop.  Block indices:
0 load/limit, 1 slot/load/pos, 2 ready?, 3 EMPTY, 4 success, 5 ahead,
6 help, 7 cell CAS, 8 EXHAUSTED, 9 retry fallback. -/
def popProgram : Program :=
  { name := "mpmc_kernel_pop"
    params := [.capacity, .mask, .limit]
    regCount := 9
    outCount := 2
    entry := 0
    blocks := [
      { ops := [.loadHint rHint .read .acquire]
        term := .branch (.ult (.var rHint) (.param .limit)) 1 8 },
      { ops := [.set rSlot (.band (.var rHint) (.param .mask)),
                .loadCell rMarker rPayload (.var rSlot) .seqCst,
                .set rPos (.shr (.var rMarker) (.lit 1))]
        term := .branch (.eq (.var rPos) (.var rHint)) 2 5 },
      { ops := [.set rTmp0 (.band (.var rMarker) (.lit 1))]
        term := .branch (.eq (.var rTmp0) (.lit 0)) 3 7 },
      { ops := []
        term := .ret (.lit 2) },
      { ops := [.storeOut 0 (.var rPayload),
                .storeOut 1 (.var rHint),
                .set rTmp2 (.add (.var rHint) (.lit 1)),
                .casHint rOk .read (.var rHint) (.var rTmp2) .release]
        term := .ret (.lit 0) },
      { ops := [.set rPos (.sub (.var rPos) (.var rHint))]
        term := .branch (.ult (.var rPos) (.lit half)) 6 9 },
      { ops := [.set rTmp2 (.add (.var rHint) (.lit 1)),
                .casHint rOk .read (.var rHint) (.var rTmp2) .release]
        term := .goto 0 },
      { ops := [.set rTmp0 (.shl (.add (.var rHint) (.param .capacity)) (.lit 1)),
                .set rTmp1 (.lit 0),
                .casCell rOk (.var rSlot) (.var rMarker) (.var rPayload)
                  (.var rTmp0) (.var rTmp1) .seqCst .seqCst]
        term := .branch (.eq (.var rOk) (.lit 0)) 0 4 },
      { ops := []
        term := .ret (.lit 3) },
      { ops := []
        term := .goto 0 }
    ] }

end Mpmc.Kernel
