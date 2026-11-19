# Proof

The Lean development has three layers:

1. an **abstract machine** with ghost counters `W` (published), `R`
   (consumed), hints `w`, `r`, and a value map `val : Nat -> Option V`;
2. a **cell protocol refinement** that derives every slot's cell from
   `(W, R, C)` and proves that a successful cell compare-exchange performs
   exactly one abstract transition;
3. a **kernel refinement** (`Mpmc/KernelRef.lean`) that proves the executable
   push/pop programs return the correct outcome on their success, full, empty,
   exhausted, and lagging-hint help paths, and that a successful cell CAS
   performs the corresponding abstract push/pop.

**Model scope.** The Lean kernel model indexes logical workers by
`kind : Fin n → Kind`, fixing each worker's role (push or pop). The C API does
not require this: any real thread may call either function. A real thread
that switches roles is represented by a fresh logical worker for each call:
each invocation starts from the fresh start local, and the logical workers
share only the queue state. The model is a logical-worker decomposition, not
a one-to-one model of OS threads.

All top-level statements also assume `C = 2^k`, `2 <= C <= 2^24`,
`limit < 2^63`, `limit + C <= 2^63`, and a finite trace.  The trace-indexed
`trace_linearizable` takes the move list as a parameter; `initial_linearizable`
existentially produces one.

The kernel theorems in `Mpmc/KernelRef.lean` are fixed-fuel,
no-interference runs.  They are strengthened by a stage simulation
(`Mpmc/KernelSim.lean`, section 8.1): under arbitrary interference, every
operation-level kernel step is exactly one admissible event or a stutter,
preserving the per-thread and shared invariant.  `Mpmc/KernelTrace.lean`
(section 8.2) composes these steps into finite global schedules, including
operation invocations, and proves FIFO from the concrete initial state.  The lowering from the C11/C++ atomics to the machine is still
unmechanized, and kernel-level lock-freedom/liveness is not mechanized.

Every theorem statement below is in `Mpmc/` and is checked by `lake build`
with no `sorry`.

## 1. Abstract machine (`Mpmc/Abstract.lean`)

```lean
structure AbsState (V : Type) where
  W : Nat
  R : Nat
  w : Nat
  r : Nat
  val : Nat → Option V
```

`Inv C limit s` is the safety invariant:

| Field | Meaning |
|---|---|
| `hR_le_W` | `R <= W` |
| `hocc` | `W - R <= C` |
| `hw_le`, `hW_le_w` | `w <= W <= w + 1` |
| `hr_le`, `hR_le_r` | `r <= R <= r + 1` |
| `hlimit` | `W <= limit` |
| `hval_some` | every position below `W` has a value |
| `hval_none` | every position at or above `W` has none |

The transitions are `Step C limit s a s' r`:

- `push v`: guard `w = W`, `W - R < C`, `W < limit`; append `v` at `W`,
  advance `W`, return `.pushed W`.
- `pop`: guard `r = R`, `R < W`, `val R = some v`; advance `R`, return
  `.popped R v`.
- `helpW`: guard `W = w + 1`; advance `w`.
- `helpR`: guard `R = r + 1`; advance `r`.

`initial_inv` establishes the invariant for the empty queue.

`Inv.step` is the preservation theorem: every transition from an invariant
state lands in an invariant state. The interesting cases are push (needs
`w = W` for `W+1 <= w+1`, and `W-R < C` for occupancy) and pop (needs
`R < W` for `R+1 <= W`). `Steps.inv` lifts it to a list of transitions.

### FIFO labels

`Steps C limit s0 as sf rs` is a finite run with the results `rs`.
`pushLabels` and `popLabels` filter the results to the sequence numbers.

- `pushLabels_eq_range' : Steps ... -> pushLabels rs = List.range' s0.W (sf.W - s0.W)`
- `popLabels_eq_range' : Steps ... -> popLabels rs = List.range' s0.R (sf.R - s0.R)`

From the initial state, the successful push labels are `0, 1, ..., W-1` and
the successful pop labels are `0, 1, ..., R-1`, in trace order. This is the
sequence-number half of FIFO/linearizability.

The value half (`Mpmc/Linearizable.lean`):

- `pushValues_eq_map`: the values pushed, in order, are the final values at
  positions `s0.W, s0.W+1, ...`.
- `popValues_eq_map`: the values popped, in order, are the final values at
  positions `s0.R, s0.R+1, ...`.
- `trace_fifo` combines both halves.

The stability lemmas `Step.val_lt_W` / `Steps.val_lt_W` (a push only writes
its own position) and `Step.val_stable` / `Steps.val_stable` (a value below
the read counter never changes) are what let the final-state values stand in
for the values at the time of each pop.

## 2. Slot view (`Mpmc/View.lean`)

```lean
def slotQ (R j C : Nat) : Nat := (R + C - 1 - j) / C
def slotPos (R j C : Nat) : Nat := j + slotQ R j C * C
```

`slotPos R j C` is the first position `>= R` in slot `j` (the `ceil` form,
with `Nat` truncating subtraction handling `R <= j`).

Proved:

- `slotPos_mod`: `slotPos R j C % C = j` for `j < C`.
- `slotPos_ge`: `R <= slotPos R j C`.
- `slotPos_lt`: `slotPos R j C < R + C`.
- `slotPos_unique`: if `R <= p`, `p < R + C`, and `p % C = j`, then
  `p = slotPos R j C`.

Uniqueness is the load-bearing lemma. It says the window `[R, R+C)` contains
exactly one representative of each slot, so the cell's position is a function
of `R`, `j`, and `C` alone. All guard equivalence arguments reduce to it.

## 3. Cell protocol (`Mpmc/Protocol.lean`)

```lean
structure Cell (V) where
  marker : Nat
  payload : V

def emptyCell z p := ⟨2*p, z⟩
def fullCell p v  := ⟨2*p + 1, v⟩
```

`viewCell z C s j` is the required cell in slot `j`:

- position `slotPos s.R j C`;
- full (odd marker) iff `slotPos s.R j C < s.W`;
- payload `s.val (slotPos ...)` when full, `z` otherwise.

`Mem` is the concrete memory: the two hints and a total function
`cells : Nat -> Cell V`. `Ref z C s m` says `m.w = s.w`, `m.r = s.r`, and
every slot below `C` is exactly `viewCell z C s j`.

The transition lemmas:

| Theorem | Statement |
|---|---|
| `push_ref` | A successful push CAS at `s.W % C` turns the memory into `Ref (pushState s v)`, with the cell `fullCell s.W v` |
| `pop_ref` | A successful pop CAS at `s.R % C` turns the memory into `Ref (popState s)`, with the cell `emptyCell z (s.R + C)` |
| `helpW_ref` | Advancing the write hint is the helpW transition |
| `helpR_ref` | Advancing the read hint is the helpR transition |

The guard lemmas make the CAS guards equivalent to the abstract guards:

- `slotPos_push`: at `w = W`, the slot `W % C` has position `W` when
  `W - R < C`.
- `slotPos_push_full`: at `w = W` and `W - R = C`, the same slot has position
  `W - C` and is full (so the code returns `FULL`).
- `slotPos_self` / `slotPos_succ_self`: at `r = R`, the slot `R % C` is
  `R` / after consumption `R + C`.
- `helpW_cell`: at `W = w + 1`, the cell at `w` is either `full(w)` or
  `empty(w + C)`; both send the code to the help branch.
- `helpR_cell`: at `R = r + 1`, the cell at `r` is either `full(r + C)` or
  `empty(r + C)`; both send the code to the help branch.

`push_ref` and `pop_ref` are the refinement steps: a successful cell CAS is
one abstract transition, and the payload/readiness are published together.
The `Ref` invariant also implies the local snapshot used by the CAS is the
unique correct expected cell: a CAS can only succeed on the exact empty cell
at `W` (push) or the exact full cell at `R` (pop), so there is no ABA within
the ring: a cell that has moved on carries a different marker (or a different
lap), and the whole-cell comparison rejects it.

## 4. FIFO values (`Mpmc/Linearizable.lean`)

`Step.val_stable` and `Steps.val_stable` show that a transition never changes
a value below the read counter. `popValues_eq_map` shows

```lean
(popValues rs).map some =
  (List.range' s0.R (sf.R - s0.R)).map (fun i => sf.val i)
```

i.e. at the abstract event level the values returned by successful pops are
exactly the values at the consumed positions, in order. `trace_fifo` combines
the push labels, pop labels, and pop values in one statement.  The bridge
from these abstract event results to the kernel's caller-visible `out0`/
`out1` stores is mechanized: the post-success stage invariants carry the
register equations, `RetObs` records the actual return `Local`, and
`RetObs.sound`/`trace_linearizable` expose the output equalities (see
Sections 8.4–8.5).

Starting from the initial state, this is the functional half of
linearizability: successful pushes return `0, 1, ..., W-1`; successful pops
return positions `0, 1, ..., R-1` and values `val 0, ..., val (R-1)`, in
order. Because a push publishes exactly at its returned position and a pop
consumes exactly at its returned position, the abstract trace is a legal
sequential FIFO history and each operation's response is the one that history
assigns.

### Real-time order

The linearization point of a push is its cell CAS (the instant `W`
increments); the linearization point of a pop is its cell CAS (the instant
`R` increments). If operation A completes before operation B starts, A's CAS
happens before B's CAS in the execution, so A's abstract transition precedes
B's in the trace.

This is now packaged mechanically. `TimedOp.lin_lt_of_ret_lt_inv` /
`History.real_time_order` prove the abstract index form;
`ObsHistory` stores the real invocation, linearization, and response
positions, and `RespectsRealTime` is proved for every built history
(`ObsHistory.real_time`).  Real-time order is a consequence of the recorded
`inv <= lin <= ret` positions; the substantive claim is that those positions
are actual schedule indices. `initial_linearizable` in
`Mpmc/KernelBuild.lean` produces such a history from every finite kernel path
and proves both `Linearizes` and `RespectsRealTime`.

## 5. Executable kernel (`Mpmc/Kernel.lean`, `Mpmc/KernelRef.lean`, `Mpmc/Codegen.lean`)

`Kernel.lean` defines a small CFG IR:

- `Expr` over `u64` variables and parameters (`capacity`, `mask`, `limit`,
  `value`);
- `Op`: set, cell load, cell CAS, hint load, hint CAS, store output;
- `Term`: goto, branch, return, and the unused trap term (the shipped
  push/pop programs use a `goto` retry fallback);
- `Program`: named blocks with a register count and output count;
- `execOp`/`execOps`/`step`/`run`: an executable semantics over `MState`;
- `pushProgram` and `popProgram`: the two hot loops.

`KernelRef.lean` relates a kernel `MState` to the abstract state:

```lean
structure KRef (C limit : Nat) (s : AbsState UInt64) (st : MState) : Prop where
  hcap   : st.params.capacity.toNat = C
  hmask  : st.params.mask.toNat = C - 1
  hlimit : st.params.limit.toNat = limit
  hw     : st.hintW.toNat = s.w
  hr     : st.hintR.toNat = s.r
  hcells : ∀ j, j < C → kcellToCell (st.cells j) = viewCell 0 C s j
```

The refinement theorems (all no-`sorry`, checked by `CheckAxioms.lean`):

| Theorem | Result |
|---|---|
| `push_success` | Current write hint, space: `run 5 pushProgram` returns `OK`, publishes at `s.W`, advances the write hint, and leaves the cells of `pushState s v`; the combined post-state is the hint-advanced push state, not `KRef` for the un-advanced `pushState` |
| `pop_success` | Current read hint, nonempty: `run 5 popProgram` returns `OK`, outputs `val s.R`, advances the read hint, and leaves the cells of `popState s`; the combined post-state is the hint-advanced pop state |
| `push_full` | Current write hint, `W - R = C`: returns `FULL` without changing shared state |
| `pop_empty` | Current read hint, `R = W`: returns `EMPTY` without changing shared state |
| `push_exhausted` | Write hint at `limit`: returns `EXHAUSTED` without changing shared state |
| `pop_exhausted` | Read hint at `limit`: returns `EXHAUSTED` without changing shared state |
| `push_help_full` | Lagging write hint whose slot is `full w`: helps `w` to `w+1` and loops, preserving `KRef` |
| `push_help_empty` | Lagging write hint whose slot is `empty (w+C)`: helps and loops, preserving `KRef` |
| `pop_help` | Lagging read hint whose slot is `full/empty (r+C)`: helps `r` to `r+1` and loops, preserving `KRef` |

`KRef.push_cell`, `KRef.pop_cell`, `KRef.push_cell_full`, and
`KRef.pop_cell_empty` are the cell-shape lemmas that connect the kernel's
loaded marker/payload to `viewCell`. `Mem.ext'` and `add_one_toNat` are the
supporting arithmetic. The success theorems prove the kernel's cell CAS
publishes exactly the cell required by `push_ref`, and the hint CAS is the
`helpW`/`helpR` transition; the failure theorems prove the shared state is
untouched.

`Codegen.lean` prints the same programs as C:

```
static inline uint64_t mpmc_kernel_push(struct mpmc_queue *q,
                                        uint64_t capacity, uint64_t mask,
                                        uint64_t limit, uint64_t value,
                                        uint64_t *out0);
static inline uint64_t mpmc_kernel_pop(struct mpmc_queue *q, uint64_t capacity,
                                       uint64_t mask, uint64_t limit,
                                       uint64_t *out0, uint64_t *out1);
```

The generated file is `include/mpmc/detail/kernel.inc`; `lake exe
mpmc-codegen` regenerates it and CI diffs it. The C uses the wrapper's
`mpmc_cas_cell` / `mpmc_cas_u64` helpers, which wrap the GCC/Clang
`__atomic_compare_exchange` builtin on the 16-byte cell and
`__atomic_compare_exchange_n` on the 64-bit hints. The same generated file is
compiled by the C library and by the header-only C/C++ API.

`KernelTest.lean` generates deterministic traces and checks the interpreter
against a simple FIFO model; `tests/test_kernel_trace.c` replays the same
traces through the generated C. There are eight checked-in traces:

- `tests/kernel_trace.txt`: capacity 4, limit 100000, 5000 operations
  (heavy wraparound, full/empty);
- `tests/kernel_trace_exhaust.txt`: capacity 8, limit 12, 400 operations
  (hits `EXHAUSTED`);
- `tests/kernel_trace_fuzz_1..6.txt`: six deterministic mixed traces with
  capacities 2, 4, 16, 64, 256, 1024 and 300–3000 operations.

## 6. Concurrent event composition (`Mpmc/Concurrent.lean`)

The per-CAS protocol lemmas are composed into finite event sequences at the
shared-memory level.  `EventStep z C limit hC s m a r s' m'` has five
constructors:

| Constructor | Shared effect | Abstract action/result |
|---|---|---|
| `stutter` | none | `none`, `none` |
| `push` | `m.cells (h % C) = emptyCell z h` becomes `fullCell h v` | `.push v`, `.pushed h` |
| `pop` | `m.cells (h % C) = fullCell h p` becomes `emptyCell z (h+C)` | `.pop`, `.popped h p` |
| `helpW` | `m.w = h` becomes `h+1` | `.helpW`, `.helped` |
| `helpR` | `m.r = h` becomes `h+1` | `.helpR`, `.helped` |

The push/pop constructors carry the local provenance `h ≤ s.w` / `h ≤ s.r`;
together with `viewCell_empty_self` / `viewCell_full_self` they derive
`h = s.W` (push) or `h = s.R` (pop), the occupancy guard, and the payload
equality.  `helpW`/`helpR` carry `s.W = h+1` / `s.R = h+1` directly.

`EventStep`/`EventSteps` model only stutter, successful push, successful pop,
and hint help.  They do not model `FULL`, `EMPTY`, or `EXHAUSTED` returns, so
spurious failure outcomes are not excluded by this event layer; the fixed-fuel
kernel theorems cover those paths one run at a time.

Proved:

- `EventStep.step`: a non-stutter event is exactly an abstract `Step`.
- `EventStep.ref`: a non-stutter event preserves `Ref`; a stutter event is
  the identity on shared memory.
- `EventSteps.steps`: a finite list of events (with stutters) yields an
  abstract `Steps` trace with the same actions/results.
- `EventSteps.ref`: the whole event list preserves `Ref`.

Consequently `trace_fifo` applies to any finite sequence of admissible events:
the successful push positions and pop positions/values are FIFO, and the
per-CAS linearization points compose at the event level.

The bridge from the executable kernel to these events is mechanized in
sections 8.1 and 8.2.  Event-level composition is sequentially consistent;
the C11 memory-model refinement remains a separate obligation.

## 7. Progress: finite bound and retry charge (`Mpmc/Potential.lean`, `Mpmc/Progress.lean`)

`psi s = s.W + s.R + s.w + s.r` strictly increases on every non-stutter
event (`EventStep.psi_lt`), weakly increases on every event and every finite
trace (`EventSteps.psi_mono`), and bounds the number of events:
`as.length ≤ psi s' - psi s` (`EventSteps.length_le_psi`).
`cellClock s = s.W + s.R` is monotone under every event and strictly
increases when a cell marker increases (`EventStep.cellClock_mono`,
`EventStep.cellClock_lt_of_cell_marker_lt`).  `GPath.events_bounded` applies
the `psi` bound to any finite global kernel path.

`Attempt` records, for one cell-CAS attempt of a pending thread, the global
number of successful cell CASes by other threads at the last load (`loaded`)
and at the attempt (`successes`), plus the CAS outcome.  This is a
**conditional counting model**, not yet extracted from a kernel execution.
`PendingChain c0 as cN` is a chain of failed attempts where each attempt saw
`loaded < successes` and the next attempt starts at or after the previous
`successes`; `CompletedChain` is the same with a final successful attempt.

Proved:

- `pending_failures_le`: `countFailures as ≤ cN - c0`.
- `completed_failures_le`: the same bound including the successful attempt.
- `pending_failures_bounded`: if `cN - c0 ≤ k`, a pending thread has at most
  `k` failures.
- `pending_failures_bounded_of_successes`: the same with `cN ≤ k + c0`.
- `EventSteps.event_of_cell_change`: a changed cell marker in a trace
  certifies that the trace has at least one non-stutter event.  This is the
  formal bridge premise behind the retry charge (a failed CAS that observes a
  moved marker is witnessing someone's successful event).

The intended instantiation is the lock-free charge: if a failed whole-cell CAS
is known to mean the marker changed since the load, then another thread's
successful cell CAS occurred in between; after a failure the thread reloads,
so failures need distinct successes.  Under the chain premises, a pending
thread with `k` failures certifies at least `k` successful cell CASes by
other threads.  The premises `loaded < successes` and the reload ordering are
obligations of the kernel-to-progress bridge, not consequences proved here.
A successful cell CAS is a linearization event, not necessarily a completed
call.  This is a finite retry-charge lemma.  No machine-checked lock-freedom
or fair-scheduler liveness theorem is claimed.

## 8. Kernel stage simulation and finite global runs

### 8.1 Per-thread stage invariants (`Mpmc/KernelSim.lean`)

`PushInv` and `PopInv` are indexed by the program phase and track, for one
thread, exactly the stable facts needed at that point: the loaded hint and
its relation to the abstract hint, the slot and snapshot marker/position,
the marker lower bound that survives interference, the pre-CAS and pre-help
register shapes, and the provenance of each legal failure.  The retry fallback blocks
(push block 10, pop block 9) are proved unreachable.

`push_local_step` and `pop_local_step` prove that every reachable
operation-level step is either

- exactly one abstract `EventStep` (`push`, `pop`, `helpW`, or `helpR`), or
- a stutter that leaves the abstract state and shared memory unchanged.

The proof is by cases on every `PushInv`/`PopInv` constructor.  Loads,
register operations, failed cell CASes, and failed hint CASes are stutters;
successful cell CASes use `pushCas_event_of_success` /
`popCas_event_of_success`; successful hint CASes use
`pushHint_event_of_success` / `popHint_event_of_success`.  The stage
invariant and `SharedRef` are preserved under arbitrary interference, using
`PushInv.mono`/`PopInv.mono`.

`gstep_sim` lifts the per-thread step to the global `GStep` relation:

> Given `Inv C limit s`, `GRef C limit kind s g`, the configuration bounds,
> and one global step `GStep kind g i g'`, there is `s'` with
> `GRef C limit kind s' g'` and either one abstract event from `s` to `s'`
> or a stutter with `s' = s` and unchanged shared memory.

`GRef` combines the shared `SharedRef` with a per-thread `ThreadInv`; the
local invariant is preserved by the global step for every other thread
(`ThreadInv.mono`).

### 8.2 Finite global paths (`Mpmc/KernelTrace.lean`)

`GPath kind g g'` is a finite sequence of global steps, plus explicit
operation invocations `GInvoke` that reset a returned thread to block 0 with
a new payload.  `GPath.events` inducts over the path and composes
`gstep_sim` with `EventSteps`, producing an abstract event trace from the
initial abstract state to one that still satisfies `GRef`.

Consequences:

- `GPath.fifo`: any finite global path yields FIFO push labels, pop labels,
  pushed values, and popped values, with the same `trace_fifo` statement as
  the abstract machine.
- `initialGRef`: the concrete `initShared` state (all empty cells, both hints
  zero, the C layout's parameters) refines `initial UInt64`; the fresh local
  register files satisfy `PushInv.entry`/`PopInv.entry`.
- `initial_fifo`: FIFO holds for any finite global schedule that starts from
  the concrete initial state used by `mpmc_create`, including repeated
  invocations on each thread.
- `GPath.events_bounded`: the number of abstract events in a finite path is
  at most the growth of `psi`.
- `GPath.event_of_cell_change`: a changed cell marker along a finite path
  yields a nonempty abstract event trace.  This is the kernel-level witness
  used by the retry-charge argument.

This covers arbitrary finite interleavings, not only a
fixed-fuel single-thread run: every global step is covered by `gstep_sim`.
The remaining universe is the C call boundary: `GPath` models the kernel
from block 0 to return, and `GInvoke` models the caller's next call.  The
hand-written allocator/initializer and the C compiler/atomic lowering are
outside the Lean model.

### 8.3 Failure observations and history

`ObservedStep`/`ObservedSteps` add legal `FULL`/`EMPTY`/`EXHAUSTED`
observations as stutters, preserve `Ref`, and project to abstract `Steps`.
`History`/`TimedOp` package a trace in linearization order and prove that
`a.ret < b.inv` implies `a.lin < b.lin`.

`Mpmc/ObsHistory.lean` adds `ObsHistory`, `TimedObsOp`, and a combinatorial
scan (`BuildHistory`) over the zipped `(Move, StepTag)` schedule.  It proves
that scan positions are bounded by the schedule length, that a selected
successful event is a push/pop event, and that the resulting history
respects real time.

`Mpmc/KernelLinearize.lean` proves the semantic half of the bridge.
`sync s` is the canonical queue state with both hints current.  Every
successful push/pop event in a tagged kernel trace induces one canonical
push/pop: the kernel event followed by one `helpW`/`helpR`
(`Step.push_sync_help`, `Step.pop_sync_help`).  Failure guards mention only
`W` and `R`, so they are invariant under `sync` (`ObsGuard.sync`).
`Effect.client_step` lifts each tagged kernel effect to this client level,
and `Exec.exists_client_trace` proves that every finite tagged execution has
a `ClientTrace` from the canonical initial state to the canonical final
state.  `ClientTrace.steps` produces an abstract `Steps` trace with
the inserted canonical helps.  Dropping helps from the *raw* event trace is
indeed unsound; inserting the canonical help is the correct
help-erased presentation.

`ClientTrace.toClientScan` and `ClientTrace.toHistory_linearizes` then turn
that replay into a queue-level `ClientScan` and an `ObsHistory` that
satisfies `ObsHistory.Linearizes`.  `Exec.exists_obs_history` states the
result for every finite tagged execution: a linearizable observed history of
length at most the schedule length, respecting real time.  Positions in that
history are event positions, and every operation is packaged on worker `0`
with `inv = lin`; the per-invocation invocation/response packaging with real
schedule positions is the `BuildHistory` scan.

`Mpmc/KernelBuild.lean` starts the per-invocation alignment.  It adds a
computable `Stage` (`pre`, `success`, `pushFull`, `popEmpty`, `exhausted`,
`done`) read off the local phase and registers, an `Align` relation between a
`BuildState` and a `GState`, and the bridge
`BuildHistory.linearizes_of_clientEvents`: a scanned history whose client
events replay as a `ClientTrace` linearizes.  It also proves the exact
failure-observation decision points at the two load phases and the two
horizon phases for each role:

* `push_horizon_tag` / `pop_horizon_tag`: at the hint test, either the
  `EXHAUSTED` observation at `(9,0)`/`(8,0)`, or a stutter to the next test;
* `push_load_tag` / `pop_load_tag`: at the cell load, either the
  `FULL`/`EMPTY` observation at `(1,2)`, or a stutter into the ready path;
* `push_cas_tag` / `pop_cas_tag`: at the cell CAS, either the exact
  successful `push`/`pop` event at `(3,3)`/`(7,3)` with `rOk = 1`, or a
  stutter with `rOk = 0`.

Each returns the concrete `GRef`, `Inv`, tagged `Effect`, and the post
phase, so every selected tag is attached to its exact linearization point.

The alignment is completed.  `gstep_tag` strengthens `gstep_effect` to
return the canonical tag together with a `StepClass`: stutter and help tags
preserve the thread's stage, a selected event moves `pre` to the matching
outcome stage, and a return carries exactly the stage's canonical status.
`buildScan_step` extends a `BuildScan` by one schedule entry under the
`Align` relation, so the scan consumes the *same* tags as the `Exec`.
`GPath.buildScanExec` inducts over a finite kernel path and produces, in one
pass, the `Exec`, the `BuildScan`, the alignment, and the invariant
`st.linOps.map outcomeEvent = previous ++ tags.flatMap clientEvents`.
`BuildHistory.linearizes_of_clientEvents` then turns the scan into
`hist.Linearizes`, and `GPath.buildHistory` / `initial_linearizable` state
the result for every finite run from the C library's initial state.  The
exact return code is tied to the outcome by `StepClass.ret_status` and
`buildScan_step_ret_status` (`0` success, `1` `pushFull`, `2` `popEmpty`,
`3` exhausted).

`EventStep.push_of_cellRef` and `EventStep.pop_of_cellRef` prove that a
successful whole-cell CAS is a legal push/pop using only the cell view and a
hint lower bound; the exact hint values are irrelevant to cell safety.

Not yet mechanized:

- extracting the retry/help `Attempt` chain from a kernel `GPath`, and
  bounding help iterations; hence no kernel-level lock-freedom theorem;
- the C11/C++ weak-memory refinement: the cell-safety lemmas show stale hints
  cannot break the cell protocol, but a full memory-model refinement is not
  mechanized.

### 8.4 Real-invocation histories

`Mpmc/KernelBuild.lean` completes the per-invocation bridge:

* `gstep_tag`: every global kernel step produces a canonical `StepTag`, an
  `Effect`, and a `StepClass` proving that the tag either preserves the
  thread's stage (stutter/help), moves it from `pre` to the selected outcome
  stage (push, pop, or failure observation), or is the exact canonical return
  of the current stage.
* `buildScan_step`: one schedule entry extends a `BuildScan` while
  preserving the `Align` relation between the scan state and the kernel
  state, and updates the accumulated selected-event list by exactly the
  tag's client events.
* `GPath.buildScanExec`: induction over a finite `GPath` builds the `Exec`,
  the `BuildScan`, and the alignment simultaneously.
* `GPath.buildHistory` / `initial_linearizable`: the resulting
  `ObsHistory` has `clientEvents` equal to the run's selected client events,
  `Linearizes` from the canonical initial to the canonical final state, and
  `RespectsRealTime`.  Every `lin` is a real schedule position
  (`BuildHistory.lin_lt_length`), and `inv ≤ lin ≤ ret`
  (`BuildHistory.positions`).  `GPathTrace.TagsFor` authenticates each tag in
  the schedule against the actual trace step's `StepClass`, so the coverage
  conjunct is over the real steps, not an unrelated tag list.
* `BuildScan.pushEvent` / the alignment invariant also fix the pushed value:
  a successful push's recorded outcome value is the value in the invocation
  (`hval`).  This is part of `BuildHistory`; the headline statement exports
  the output equations but not a separate input-value conjunct.

* `StepClass.ret_status` / `buildScan_step_ret_status`: a returning
  linearized operation's status is exactly the outcome's canonical code:
  `0` success, `1` pushFull, `2` popEmpty, `3` exhausted.

The remaining boundary for the C library is the documented TCB: the
printer, the compiler and its 16-byte atomic lowering, the
allocation/initialization wrapper, and the C11/C++ weak-memory refinement.

### 8.5 Trace-indexed executions and return-state authenticity

`GPathTrace kind g ms g'` is the trace-indexed execution relation: the move
list `ms` is an index of the relation, not existentially produced.  Its
`StateAt` predicate names the global state at a local move index, and
`GPathTrace.buildScanExec` proves the same `Exec`/`BuildScan`/`Align`
package over it.  `GPathTrace.buildHistory` and `trace_linearizable` are the
trace-indexed counterparts of `GPath.buildHistory`/`initial_linearizable`;
`GPathTrace.TagsFor` records that every tag is the canonical `StepClass` tag
of the corresponding `GStep`/`GInvoke`; in addition to all history, status,
output, provenance, and coverage conjuncts, they state

```lean
∀ r ∈ rets, ∃ gk, GPathTrace.StateAt hp r.pos gk ∧ r.loc = gk.locals r.thread
```

so every recorded return's caller-visible local is exactly the global state
at that schedule position.  The endpoint-indexed `initial_linearizable`
remains available for callers that only know the endpoints.

## What is actually proved

Proved, with no `sorry`:

- the abstract invariant is preserved by every transition and every finite
  run;
- successful push positions and pop positions are consecutive ranges in
  trace order;
- successful pop values are the values at those positions, in order;
- the slot cell is a function of `(W, R, C)`, with the exact marker and
  payload;
- a successful push CAS / pop CAS performs exactly one abstract push / pop,
  and a hint CAS performs one help transition;
- the guard conditions at the hints are the abstract guards (including the
  `FULL` and help branches);
- the executable kernel returns `OK` and performs the abstract push/pop on
  its success paths, returns `FULL`/`EMPTY`/`EXHAUSTED` with the shared state
  unchanged on the failure paths, and performs one help transition on each
  lagging-hint path (`push_success`, `pop_success`, `push_full`, `pop_empty`,
  `push_exhausted`, `pop_exhausted`, `push_help_full`, `push_help_empty`,
  `pop_help`);
- **event-level SC composition**: `EventStep.step` / `EventStep.ref` lift each
  admissible per-CAS event to an abstract `Step` and preserve `Ref`;
  `EventSteps.steps` / `EventSteps.ref` lift a finite sequence with stutters
  to an abstract `Steps` trace, so `trace_fifo` applies to any finite sequence
  of admissible events;
- **kernel stage simulation**: `PushInv`/`PopInv`, `push_local_step`/
  `pop_local_step`, and `gstep_sim` prove that every operation-level kernel
  step under arbitrary interference is exactly one abstract event or a
  stutter, preserving `GRef`.  The stage invariants omit the fallback-entry
  constructors: the only branch that targets them is proved untaken
  (`push_step8_running`, `pop_step5_running`), so every *reachable* state is
  still covered;
- **finite global kernel runs**: `GPath`, `GInvoke`, `GPath.events`,
  `GPath.fifo`, `initialGRef`, and `initial_fifo` prove FIFO for any finite
  schedule from the concrete initial state, including arbitrary
  interleavings and repeated invocations; `GPath.events_bounded` bounds the
  number of abstract events by the growth of `psi`;
- **kernel bridge interfaces**: `push_load_dec`/`pop_load_dec` classify a
  loaded cell; the four `*_of_success` lemmas turn a successful kernel CAS
  into exactly one abstract push, pop, helpW, or helpR event; `SharedRef`
  and `initShared_ref` establish the shared-memory invariant and its initial
  state;
- **failure-observation composition**: `ObservedStep`/`ObservedSteps` add
  legal `FULL`/`EMPTY`/`EXHAUSTED` observations as stutters and preserve
  `Ref` and abstract `Steps`;
- **progress monotonicity**: `psi = W+R+w+r` strictly increases on every
  non-stutter event, and `cellClock = W+R` is monotone; finite event traces
  satisfy `length ≤ psi s' - psi s`; `EventSteps.event_of_cell_change` turns
  a changed cell marker into a nonempty-event witness;
- **real-time history packaging**: `TimedOp.lin_lt_of_ret_lt_inv` and
  `History.real_time_order` prove that response-before-invocation order
  implies linearization-point order; `History.Linearizes` is the trace
  premise for `trace_fifo`;
- **observed history scan**: `ObsHistory`, `TimedObsOp`, `BuildHistory`, and
  `BuildHistory.real_time` scan a tagged `(Move, StepTag)` schedule into
  per-thread operation records and prove schedule-length and real-time
  bounds; `BuildHistory.positions` records that every operation satisfies
  `inv ≤ lin ≤ ret` and that every linearization point is a real schedule
  position;
- **real-invocation linearizability**: `gstep_tag` (canonical tag plus
  `StepClass`), the six decision-point lemmas, `buildScan_step`,
  `GPath.buildScanExec`, and `GPath.buildHistory`/`initial_linearizable`
  prove that every finite kernel path from the C library's initial state
  yields one `Exec`, one scan of its real tags, and an `ObsHistory` whose
  `clientEvents` are exactly the run's selected client events, which
  `Linearizes` from the canonical initial to the canonical final state and
  `RespectsRealTime`.  The invocation, linearization, and response positions
  are the real `Move.invoke`/event/return positions of the schedule (with a
  synthetic end position only for operations still open when the schedule
  ends).  In addition, every `.ret status` in the schedule has a recorded
  return at that position with that status (`initial_linearizable`'s
  coverage conjunct), and every record's status is the outcome's canonical
  code
  (`RetObs.OK` includes `r.status = (stageOfOutcome r.outcome).status`);
- **caller-visible output stores**: the post-success push invariants
  (`hintPath1..3`) carry `out0 = rHint`, and the post-success pop invariants
  (`out1..4`) carry `out0 = rPayload` and `out1 = rHint`.  `push_ret_outputs`
  and `pop_ret_outputs` prove the return-phase equalities, and the tagged
  step classification carries them (`RetOutputs` is part of `StepClass`'s ret
  disjunct, projected by `StepClass.ret_outputs`).  `buildScan_step` records
  each return as a `RetObs` (position, thread, status, outcome, and the
  actual kernel `Local` at the return) with a proof `RetObs.Fits`;
  `GPath.buildScanExec` threads the recorded returns through the path
  (`RetObs.OK`), and `GPath.buildHistory` / `initial_linearizable` export the
  explicit conjunct that for every recorded return, `r.pos < ms.length`, the
  schedule tag at `r.pos` is exactly `(r.thread, .ret r.status)`, and if the
  recorded outcome is a successful push/pop then the caller-visible outputs
  `r.loc.out0`/`r.loc.out1` are exactly the publication position (push) or
  the popped value and position (pop);
- **client-level event linearization**: `sync`, `Step.push_sync_help`,
  `Step.pop_sync_help`, `ObsGuard.sync`, `ClientTrace`, `ClientTrace.steps`,
  `Effect.client_step`, and `Exec.exists_client_trace` prove that every
  finite tagged kernel run replays as a queue-level trace with the canonical
  helps inserted; `ClientScan`/`ClientTrace.toClientScan` and
  `Exec.exists_obs_history` package it as a linearizable `ObsHistory`;
- **hint-independent cell safety**: `CellRef`,
  `EventStep.push_of_cellRef`, and `EventStep.pop_of_cellRef` show that a
  successful whole-cell CAS is a legal push/pop using only the cell view and
  a hint lower bound; exact hint values do not affect cell safety;
- **retry-charge counting lemma**: `PendingChain`/`CompletedChain` and
  `pending_failures_le` / `completed_failures_le` prove the conditional bound
  that a pending thread's failed cell CASes are at most successful cell CASes
  by other threads; `pending_failures_bounded` states the finite form.  The
  chain premises are not yet extracted from a kernel execution, and no
  lock-freedom theorem is claimed.

Proved with stated qualification:

- **Failure-return event coverage**: the exact return-code mapping is proved
  at the step level (`StepClass.ret_status`, `buildScan_step_ret_status`:
  `0`/`1`/`2`/`3` for success/`pushFull`/`popEmpty`/exhausted).  The
  `ObsHistory` predicate `OpOutcome.acceptsStatus` records only
  success (`0`) versus failure (nonzero), so the history itself does not
  re-export the numeral; this is a presentation choice, not a gap in the
  step-level result.
- **Return-record provenance**: every recorded return has a matching
  history operation.  `BuildState.LinMem` and `BuildState.ThreadOK` (proved
  preserved by `BuildScan.inv`) give that a linearized phase's record is in
  `linOps` and belongs to its thread; `closeLin_exists_id` (with the idempotent
  `closeLin`, which closes only an unclosed matching record) identifies the
  closed entry, and
  `exists_finalize_of_mem` carries it through `finalize`.  The theorem states
  `∀ r ∈ rets, ∃ op ∈ hist.ops, op.id.thread = r.thread ∧ op.lin = r.lin ∧
  op.outcome = r.outcome ∧ op.ret = r.pos`; each return record also carries
  the kernel `Local` at the return (`RetObs.loc`), and `RetObs.sound` proves
  its `out0`/`out1` equal the outcome's result.  Exact response-position
  equality uses the idempotent `closeLin` (an already-closed record is never
  overwritten) and `BuildScan.lin_exists_ret`.  Coverage is stated for every
  status: every `.ret status` in the schedule has a recorded return at that
  position with that status.  The conjunct is "every record has a matching
  history operation"; it does not assert that distinct records map to
  distinct operations (id freshness makes that true, but injectivity is not a
  stated conjunct).
- **Endpoint-indexed variant**: `GPath` remains the endpoint-indexed form and
  `initial_linearizable` still existentially produces `ms`.  The
  trace-indexed form `GPathTrace` (`trace_linearizable`) supplies the move
  list as a parameter, so the schedule is part of the statement; the two
  forms coexist, and `GPathTrace.toGPath` forgets the moves.  This is a
  presentation choice: the trace-indexed statement is the stronger form.

Not proved:

- **Kernel progress instantiation / lock-freedom**: the abstract
  retry-charge lemma and the `psi`/`cellClock` monotonicity lemmas are
  mechanized, but extracting the actual load/CAS attempt chain from a kernel
  execution and bounding help iterations are not.  No machine-checked
  lock-freedom, fair-scheduler, or wait-freedom theorem is claimed.  A thread
  that is never scheduled is not guaranteed to complete.
- **Weak-memory refinement**: the proof is sequentially consistent. The
  implementation uses seq_cst cell atomics and acquire/release hints, documented in
  `docs/algorithm.md`; the lowering from the C11/C++ operations to the
  machine is not mechanized.
- **Wrappers/layout/allocation**: the magic check, `aligned_alloc`, header
  offsets, slot stride, and initialization are tested, not proved. The
  `static_assert`s pin the offsets, and `tests/test_layout.c` checks the
  128-byte slot stride at runtime. The Rust crate's ownership, lifetime, and
  `Send`/`Sync` reasoning is a hand-written FFI layer tested by
  `tests/rust_api.rs`; it is not part of the Lean proof.
- **16-byte atomicity/lock-freedom**: assumed from the platform and checked
  at creation. On x86-64, `mpmc_create` checks CPUID CX16. Clang uses
  `__atomic_is_lock_free` on an aligned probe. GCC x86-64 with `-mcx16` is
  accepted after CPUID because the GNU libatomic used in CI dispatches its
  16-byte operations to CX16, even though its predicate returns false.
  That runtime lowering is trusted, not proved.
- **x86-64**: exercised by the Linux CI jobs (GCC and Clang). The code needs a compiler that
  lowers 16-byte atomics to `cmpxchg16b`. The CMake build probes for `-mcx16`
  and links `libatomic` if that is the only working lowering.

## Trusted computing base

1. **The C printer** (`Mpmc/Codegen.lean`). Not verified. The generated C is
   checked in, reviewed, and regenerated in CI (which rejects any
   generated-file drift with `git status --porcelain`).
2. **The C compiler and platform atomics.** `mpmc_cell` is 16 bytes and
   16-byte aligned (static asserts); `mpmc_create` checks CPUID CX16 on
   x86-64 and refuses to run unless the platform lock-free check passes.
   GCC x86-64 with `-mcx16` is accepted after CPUID; this relies on GNU
   libatomic's CX16 runtime dispatch for 16-byte operations. The `__atomic` builtins lower the
   cell CAS to a single 16-byte `casp` (`caspl`/`caspa`) on arm64 with LSE;
   baseline arm64 uses an `ldxp`/`stxp` loop or libatomic. The Rust arm64
   build requires Clang, whose baseline lowering uses LDXP/STXP (inline or
   outlined); LSE is used only if a user explicitly requests it. On x86-64
   they need
   `cmpxchg16b`/`-mcx16`.
3. **The C and Rust wrappers** (`src/mpmc.c`, `src/lib.rs`, `build.rs`, and
   `include/mpmc/detail/impl.h`): allocation, header, initialization,
   validation, and the Rust ownership/FFI boundary. Tested by `tests/` and
   `tests/rust_api.rs`; the wrapper code is not proved.
4. **The Lean kernel and standard axioms.** No `sorryAx`. `#print axioms`
   reports `propext`, `Quot.sound`, and `Classical.choice`; these are Lean's
   standard axioms, not extra assumptions about the queue.
5. **The kernel-to-event instantiation** is mechanized through `KernelSim`,
   `KernelTrace`, and `KernelBuild`: `initial_linearizable` produces the
   real-invocation linearizable observed history for every finite kernel
   path, and `StepClass.ret_status` gives the exact return code.  The
   **weak-memory refinement** and **kernel-level progress instantiation**
   are not mechanized, as described above.

## Reproduce

```sh
lake build
if grep -rnE '\b(sorry|admit)\b' Mpmc Mpmc.lean; then exit 1; fi
lake env lean scripts/CheckAxioms.lean
lake exe mpmc-codegen
lake exe mpmc-kernel-trace
test -z "$(git status --porcelain -- include/mpmc/detail/kernel.inc 'tests/kernel_trace*.txt')"
cmake -S . -B build -DCMAKE_BUILD_TYPE=Release
cmake --build build -j
ctest --test-dir build --output-on-failure
```

The sanitizer builds are described in the README. The concurrency stress test
(`tests/test_stress.c`) detects missing and duplicate values; TSan reports no
data races on the tested topologies.
