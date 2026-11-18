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
  Differential test driver.

  Generates deterministic single-threaded operation traces, runs them through
  the kernel interpreter, and checks the results against the abstract queue
  model.  It also writes the traces under `tests/`; `tests/test_kernel_trace.c`
  replays the same traces through the generated C kernel, so an interpreter /
  code-generator disagreement becomes a test failure.
-/

import Mpmc.Kernel

open Mpmc.Kernel

namespace Mpmc.KernelTest

inductive OpKind where
  | push (v : UInt64)
  | pop
  deriving Repr

structure Model where
  W : Nat
  R : Nat
  vals : List UInt64

def initialCells (C : Nat) : Nat → KCell :=
  fun j =>
    if j < C then
      { marker := UInt64.ofNat (2 * j), payload := 0 }
    else
      { marker := 0, payload := 0 }

def initialKState (capacity limit : Nat) : MState :=
  { params := { capacity := UInt64.ofNat capacity,
                mask := UInt64.ofNat (capacity - 1),
                limit := UInt64.ofNat limit,
                value := 0 }
    regs := fun _ => 0
    cells := initialCells capacity
    hintW := 0
    hintR := 0
    out0 := 0
    out1 := 0 }

def initialModel : Model := { W := 0, R := 0, vals := [] }

def stepSeed (s : UInt64) : UInt64 :=
  s * 6364136223846793005 + 1442695040888963407

def genOps : Nat → UInt64 → List OpKind
  | 0, _ => []
  | n + 1, s =>
      let s := stepSeed s
      if (s >>> 33) % 3 = 0 then
        .pop :: genOps n s
      else
        .push (s % 100) :: genOps n s

def pushModel (capacity limit : Nat) (m : Model) (v : UInt64) :
    Nat × Nat × Model :=
  if m.W ≥ limit then
    (3, 0, m) -- exhausted
  else if m.W - m.R ≥ capacity then
    (1, 0, m) -- full
  else
    (0, m.W, { m with W := m.W + 1, vals := m.vals ++ [v] })

def popModel (limit : Nat) (m : Model) :
    Nat × Nat × Option UInt64 × Model :=
  if m.R ≥ limit then
    (3, 0, none, m) -- exhausted
  else
    match m.vals with
    | [] => (2, 0, none, m) -- empty
    | v :: vs => (0, m.R, some v, { m with R := m.R + 1, vals := vs })

def go (capacity limit : Nat) :
    List OpKind → MState → Model → List String →
      Except String (List String)
  | [], _, _, acc => .ok acc.reverse
  | op :: rest, st, m, acc =>
      match op with
      | .push v =>
          let st1 := { st with params := { st.params with value := v } }
          let (expectedStatus, expectedSeq, m') := pushModel capacity limit m v
          match run 1000 pushProgram pushProgram.entry st1 with
          | .returned status st' =>
              if status.toNat ≠ expectedStatus then
                .error s!"push {v}: status {status.toNat}, expected {expectedStatus}"
              else if expectedStatus = 0 && st'.out0.toNat ≠ expectedSeq then
                .error s!"push {v}: seq {st'.out0.toNat}, expected {expectedSeq}"
              else
                go capacity limit rest st' m' (s!"push {v.toNat}" :: acc)
          | .running _ _ => .error s!"push {v}: did not return"
          | .trapped _ => .error s!"push {v}: trapped"
      | .pop =>
          let (expectedStatus, expectedSeq, expectedValue, m') := popModel limit m
          match run 1000 popProgram popProgram.entry st with
          | .returned status st' =>
              if status.toNat ≠ expectedStatus then
                .error s!"pop: status {status.toNat}, expected {expectedStatus}"
              else if expectedStatus = 0 then
                if st'.out1.toNat ≠ expectedSeq then
                  .error s!"pop: seq {st'.out1.toNat}, expected {expectedSeq}"
                else
                  match expectedValue with
                  | some v =>
                      if st'.out0 ≠ v then
                        .error s!"pop: value {st'.out0}, expected {v}"
                      else
                        go capacity limit rest st' m' ("pop" :: acc)
                  | none => .error "pop: model has no value"
              else
                go capacity limit rest st' m' ("pop" :: acc)
          | .running _ _ => .error "pop: did not return"
          | .trapped _ => .error "pop: trapped"

def runTrace (capacity limit n seed : Nat) : Except String (List String) :=
  let ops := genOps n (UInt64.ofNat seed)
  go capacity limit ops (initialKState capacity limit) initialModel []

def writeTrace (path : String) (capacity limit : Nat) (lines : List String) :
    IO Unit := do
  let text :=
    "capacity " ++ toString capacity ++ "\n" ++
    "limit " ++ toString limit ++ "\n" ++
    String.intercalate "\n" lines ++ "\n"
  IO.FS.writeFile path text
  IO.println s!"{path}: ok ({lines.length} operations)"

end Mpmc.KernelTest

open Mpmc.KernelTest

structure TraceSpec where
  path : String
  capacity : Nat
  limit : Nat
  operations : Nat
  seed : Nat

def traces : List TraceSpec :=
  [ { path := "tests/kernel_trace.txt", capacity := 4, limit := 100000,
      operations := 5000, seed := 1 },
    { path := "tests/kernel_trace_exhaust.txt", capacity := 8, limit := 12,
      operations := 400, seed := 7 },
    { path := "tests/kernel_trace_fuzz_1.txt", capacity := 2, limit := 3,
      operations := 300, seed := 11 },
    { path := "tests/kernel_trace_fuzz_2.txt", capacity := 4, limit := 4,
      operations := 500, seed := 23 },
    { path := "tests/kernel_trace_fuzz_3.txt", capacity := 16, limit := 40,
      operations := 800, seed := 101 },
    { path := "tests/kernel_trace_fuzz_4.txt", capacity := 64, limit := 100,
      operations := 1200, seed := 777 },
    { path := "tests/kernel_trace_fuzz_5.txt", capacity := 256, limit := 1000,
      operations := 2000, seed := 4242 },
    { path := "tests/kernel_trace_fuzz_6.txt", capacity := 1024, limit := 5000,
      operations := 3000, seed := 9999 } ]

def main : IO Unit := do
  for spec in traces do
    match runTrace spec.capacity spec.limit spec.operations spec.seed with
    | .error message =>
        IO.eprintln s!"kernel trace {spec.path}: {message}"
        IO.Process.exit 1
    | .ok lines =>
        writeTrace spec.path spec.capacity spec.limit lines
