# mpmc-lean

[![CI](https://github.com/mmabdpr/mpmc-queue-lean/actions/workflows/ci.yml/badge.svg)](https://github.com/mmabdpr/mpmc-queue-lean/actions/workflows/ci.yml)
[![Release](https://img.shields.io/github/v/release/mmabdpr/mpmc-queue-lean?label=release)](https://github.com/mmabdpr/mpmc-queue-lean/releases)

A bounded multi-producer/multi-consumer queue **designed to be lock-free,
modeled in Lean 4 and code-generated into C**, with a **machine-checked
safety and FIFO core**, shipped as a single public header for C and C++ and a
safe Rust crate. The implementation is the same cell/marker design as the
companion C++ queue (`mpmc-queue`): a power-of-two ring of 16-byte cells, one
16-byte compare-exchange per publication, monotone index hints that any
participant may help advance, and a 64-bit payload. Push and pop never
allocate, never take a lock, and do not block on a particular thread by
design.

```c
#include "mpmc.h"

mpmc_queue *q = mpmc_create(4096);
if (!q) { /* invalid capacity, out of memory, or no lock-free 16-byte CAS */ }

if (mpmc_push(q, 42)) {
  uint64_t value;
  if (mpmc_pop(q, &value)) {
    /* value == 42 */
  }
}

mpmc_destroy(q);
```

C++ uses the same header and one RAII type:

```cpp
#include "mpmc.h"

mpmc::queue q(4096);
if (q.push(42)) {
  std::uint64_t value;
  if (q.pop(value)) { /* value == 42 */ }
}
```

Rust uses the safe crate in this repository:

```rust
let q = mpmc_lean::Queue::new(4096).expect("queue");
q.push(42).expect("space");
assert_eq!(q.pop(), Some(42));
```

Capacity, horizon, slot arithmetic, hint helping, and the atomic protocol are
implementation details. The public surface is the four C functions, the C++
class, and the Rust `Queue` type.

## Status

| Layer | State |
|---|---|
| Abstract algorithm (state machine, invariant, FIFO label/value theorems) | Proved in Lean, no `sorry` |
| Concrete cell protocol (slot view, CAS guards, push/pop/help refinement) | Proved in Lean |
| Executable kernel IR (push/pop success, full, empty, exhausted, and hint-help paths) | Proved in Lean (fixed-fuel, no-interference paths) |
| Kernel stage simulation (per-thread `PushInv`/`PopInv`, failed CAS, help, unreachable fallback) | Proved in Lean: every kernel step is one abstract event or a stutter |
| Event-level SC composition (admissible stutter/push/pop/help events -> abstract `Steps`) | Proved in Lean |
| Finite global kernel runs (arbitrary interleavings, operation invocations, FIFO from the concrete initial state) | Proved in Lean |
| Kernel history scan (`ObsHistory`) | Proved: real invocation/linearization/response positions, per-thread records, real-time order, authenticated tags, and the per-invocation alignment to the tagged run (`initial_linearizable`; trace-indexed `trace_linearizable`) |
| Client-level event linearization (`KernelLinearize`) | Proved: every finite tagged run replays as a help-erased queue trace (`Exec.exists_client_trace`) and yields a linearizable event-position `ObsHistory` (`Exec.exists_obs_history`); this is a degenerate worker-0 packaging with `inv = lin`, not the real-position history |
| Exhaustion observations | Proved: `pushExhausted`/`popExhausted` emitted at the horizon with their guards |
| Retry-charge counting lemma (failed CASes bounded by others' successes) | Proved in Lean; conditional on a kernel attempt extraction |
| Progress | `psi` finite event bound and changed-cell event witnesses proved; lock-freedom/fair-scheduler liveness not mechanized |
| Generated C kernel | Emitted from the Lean IR; checked in; differentially tested |
| C wrapper, allocation, ABI layout | Hand-written C; tested (ASan/UBSan/TSan) |
| Rust safe wrapper | Hand-written safe ownership/FFI layer; tested; not proved |

Claim:

> The Lean development proves safety and FIFO for the abstract queue and cell
> protocol, the fixed-fuel kernel paths, a per-step simulation to abstract
> events, finite global runs, and linearizable histories with real invocation,
> linearization, and response positions, exact status codes, caller-visible
> outputs, and authenticated trace tags. All statements assume `C = 2^k`,
> `2 <= C <= 2^24`, `limit < 2^63`, `limit + C <= 2^63`, a finite trace, and
> fixed-role logical workers.
>
> The generated C is a transcription of the kernel. The printer, compiler and
> atomic lowering, allocator/initialization wrapper, C11/C++ lowering, the
> Rust ownership/FFI wrapper, and kernel-level progress remain trusted or
> unmechanized. No machine-checked lock-freedom or liveness theorem is
> claimed. See `docs/proof.md` for the theorem list, hypotheses, and trusted
> computing base.

`docs/proof.md` lists every theorem, the trusted computing base, and what is
**not** proved. Do not read this as "the C code is proved".

## Performance

Apple M3 Max, Apple clang 21, capacity 4096. `bench/compare.cpp` runs both
queues in the same process, alternating which queue goes first each round,
with 20 rounds × 1,000,000 values per producer. The C++ header compiles the
generated kernel into the caller's translation unit, so these numbers do not
depend on LTO. Representative medians (one session; the host is shared):

| Topology | mpmc-lean (M/s) | C++ reference (M/s) | Ratio |
|---|---:|---:|---:|
| 1P / 1C | 109.5 | 192.6 | 0.57× |
| 2P / 2C | 12.8 | 15.3 | 0.83× |
| 4P / 4C | 5.0 | 5.0 | 0.99× |
| 4P / 1C | 6.8 | 6.4 | 1.07× |
| 1P / 4C | 6.8 | 6.4 | 1.07× |

This run used LTO off. The 1P/1C measurement is about 9.1 ns of wall-clock
time per transferred value (aggregate reciprocal throughput, not per-operation
latency). The acquire/release hints and seq_cst cell operations cost
throughput versus the reference's relaxed-hint profile: 4P/1C and 1P/4C are
ahead, 4P/4C is parity, and 1P/1C is 43% behind. The comparison uses the
reference's `Index=uint32_t` profile and a compile-time capacity; this library
keeps a 64-bit index and a runtime capacity, so it is same-shape but not
bit-for-bit. x86-64 performance is unmeasured. The Rust crate calls the
out-of-line C ABI and is not separately benchmarked here.

The slot type has a 128-byte stride (`include/mpmc/detail/impl.h`,
regression-tested by `tests/test_layout.c`). See `docs/benchmarks.md` for raw
runs, caveats, and the layout history.

## Features

- Bounded MPMC queue, capacity a power of two (2 … 2²⁴), 64-bit payload.
- One 16-byte atomic compare-exchange publishes a payload and its readiness
  together; readers never see a value without its marker.
- No locks, no allocation, and no syscalls in `mpmc_push`/`mpmc_pop`.
- FIFO. Internal positions are unique and strictly increasing; consumers
  claim them in order.
- Monotone hints with helping: a stalled participant cannot leave a
  published value unclaimable by others.
- Publication horizon (`2^63 - capacity`), so markers never wrap. Push returns
  `false` at the horizon; this is unreachable in practice and testable only
  with the internal constructor.
- GCC/Clang `__atomic` builtins; the same layout and generated kernel compile
  as C11 and C++17. On x86-64, GCC (tested with GCC 13) needs `-mcx16` and
  `-latomic`. Its runtime check uses CPUID CX16 and relies on GNU libatomic's
  CX16 dispatch, because GCC's own 16-byte predicate is conservative. On
  other targets, `__atomic_is_lock_free(16)` must report
  lock-free (for example LSE on arm64); otherwise `mpmc_create` returns
  `NULL` rather than silently using locks. The x86-64 build needs a compiler
  that lowers 16-byte atomics to `cmpxchg16b` and a CX16-capable CPU (see
  `docs/api.md`). An LSE-enabled C/C++ build must run on an LSE-capable CPU.
  The Rust crate builds baseline arm64 with Clang, so it also runs on non-LSE
  hardware. GCC arm64 is rejected by the Rust build because its libatomic
  lock-freedom depends on the runtime version.
- Single-header use for both C and C++; the static library exports the same
  four symbols for FFI.
- Safe Rust crate at the repository root: `Queue` owns the C handle, implements
  `Send + Sync`, and exposes non-blocking `push`/`pop` without requiring
  `unsafe` from callers.

## Platforms

| Target | Status |
|---|---|
| macOS 15 arm64 (Apple Clang) | CI matrix |
| Linux x86-64 (Clang 18) | CI matrix |
| Linux x86-64 (GCC 13) | CI matrix |
| Linux arm64 (Clang 18, LSE) | CI matrix |
| macOS x86-64 | header/compiler syntax checked; not in CI |
| Windows / MSVC | unsupported; CMake rejects non-GCC/Clang |

The C++ wrapper uses exceptions (`std::invalid_argument`, `std::runtime_error`);
compile C++ with exceptions enabled. The C API does not use exceptions. The
Rust crate is tested on Linux x86-64 with GCC and Clang, Linux arm64 baseline
with Clang 18, and macOS arm64; it rejects GCC arm64, Windows/MSVC, and other
unsupported targets at build time.

## Build

### Lean proofs and code generator

Requires [elan](https://github.com/leanprover/elan) with Lean 4.36.0.

```sh
lake build                      # check every proof
lake exe mpmc-codegen           # regenerate include/mpmc/detail/kernel.inc
lake exe mpmc-kernel-trace      # regenerate tests/kernel_trace*.txt
```

CI rejects every `sorry`/`admit` and runs `#print axioms`
(`scripts/CheckAxioms.lean`) on the headline theorems. The only axioms are
Lean's standard `propext`, `Quot.sound`, and `Classical.choice`; there is no
`sorryAx`.

### C / C++ library and tests

Requires CMake 3.20+, a C11 compiler, and, for the test/benchmark targets, a
C++17 compiler.

```sh
cmake -S . -B build -DCMAKE_BUILD_TYPE=Release
cmake --build build -j
ctest --test-dir build --output-on-failure
```

The `mpmc` target is a library for FFI and linking; it is static by default,
and `-DBUILD_SHARED_LIBS=ON` builds a shared library (needed for `ctypes`/
`dlopen`-style FFI). Header-only C/C++ users include `mpmc.h` and do not need
to link it. `MPMC_ENABLE_LTO` (default `ON`) applies to the bundled
benchmarks; the static library is built as portable native objects so it can
be linked by a different compiler or FFI consumer. The header-only path
inlines the kernel by construction. `MPMC_BUILD_TESTS` and `MPMC_BUILD_BENCH`
default to `ON` only when mpmc is the top-level project. Cross-compiling
cannot run the lock-free probe: pass `-DMPMC_LOCKFREE=TRUE` (and
`-DMPMC_LOCKFREE_LIBATOMIC=TRUE` if `-latomic` is required) to override it.

### Rust crate

The crate is at the repository root and compiles the same `src/mpmc.c` and
generated kernel directly; no CMake build or installed C library is required.
It needs a GCC or Clang C11 compiler and Rust 1.74 or newer.

```sh
cargo test --all-targets --locked
cargo test --release --all-targets --locked
cargo test --doc --locked
cargo package --locked
```

The crate is shipped in the repository and will be included in future tagged
source archives. It is not yet published to crates.io; from a checkout, use it
as a path dependency:

```toml
[dependencies]
mpmc-lean = { path = "path/to/mpmc-queue-lean" }
```

See `docs/rust.md` for the safe API, platform requirements, and proof scope.

### Sanitizers

```sh
cmake -S . -B build-asan -DCMAKE_BUILD_TYPE=RelWithDebInfo -DMPMC_SANITIZE=ON
cmake --build build-asan -j
ASAN_OPTIONS=abort_on_error=1 UBSAN_OPTIONS=halt_on_error=1 \
  ctest --test-dir build-asan --output-on-failure

cmake -S . -B build-tsan -DCMAKE_BUILD_TYPE=RelWithDebInfo -DMPMC_TSAN=ON
cmake --build build-tsan -j
TSAN_OPTIONS=halt_on_error=1 ctest --test-dir build-tsan --output-on-failure
```

`MPMC_SANITIZE` (ASan+UBSan) and `MPMC_TSAN` are mutually exclusive.

### Install and consume

```sh
cmake --install build --prefix /your/prefix
```

This installs `include/mpmc.h`, the private `include/mpmc/detail/` headers,
the library (`libmpmc.a`, or a shared library with
`-DBUILD_SHARED_LIBS=ON`), a CMake package (`find_package(mpmc CONFIG REQUIRED)` →
`mpmc::mpmc`), and `mpmc.pc`. A CMake consumer needs only:

```cmake
find_package(mpmc CONFIG REQUIRED)
target_link_libraries(app PRIVATE mpmc::mpmc)
```

For a pkg-config consumer:

```sh
cc app.c $(pkg-config --cflags --libs mpmc)
```

## API

The complete public surface is four C functions, one C++ class, and the Rust
`Queue`, `CreateError`, and `PushError` types:

```c
typedef struct mpmc_queue mpmc_queue;

mpmc_queue *mpmc_create(uint64_t capacity);
void        mpmc_destroy(mpmc_queue *q);
bool        mpmc_push(mpmc_queue *q, uint64_t value);
bool        mpmc_pop(mpmc_queue *q, uint64_t *value);
```

`mpmc_create` returns `NULL` for an invalid capacity, allocation failure, or a
target where the 16-byte cell compare-exchange is not lock-free. `mpmc_push`
returns `false` when the queue is full (or has reached its publication
horizon); `mpmc_pop` returns `false` when it is empty and writes `*value` only
on success. `mpmc_destroy(NULL)` is a no-op. `mpmc_push` and `mpmc_pop` do
not block; `mpmc_create` and `mpmc_destroy` call the allocator.

See `docs/api.md` for the C/C++ concurrency contract, portability, and
examples; see `docs/rust.md` for the Rust API and proof scope.

## Repository layout

```
Mpmc/Abstract.lean      abstract machine, invariant, FIFO labels/values
Mpmc/View.lean          slot arithmetic for the ring
Mpmc/Protocol.lean      cell view and CAS/help refinement
Mpmc/Linearizable.lean  FIFO label/value theorems over a trace
Mpmc/Kernel.lean        small CFG IR and the push/pop programs
Mpmc/KernelRef.lean     fixed-fuel kernel outcome/refinement theorems
Mpmc/KernelConcurrent.lean global shared/local state and kernel step relation
Mpmc/KernelClassify.lean load classification and successful-CAS event lemmas
Mpmc/KernelSim.lean     per-thread stage invariants and GStep simulation
Mpmc/KernelTrace.lean   finite global paths, invocations, FIFO from initial state
Mpmc/KernelBuild.lean   stage alignment, tagged steps, linearizable histories
Mpmc/ObsHistory.lean    scan of a tagged schedule into timed records
Mpmc/KernelLinearize.lean  semantic client-trace/client-scan bridge
Mpmc/KernelEffect.lean  tagged effects and executions
Mpmc/Concurrent.lean    event composition into abstract Steps
Mpmc/Observed.lean      legal FULL/EMPTY/EXHAUSTED observations
Mpmc/Potential.lean     psi/cellClock progress monotonicity
Mpmc/Progress.lean      conditional retry-charge counting lemma
Mpmc/History.lean       real-time history packaging
Mpmc/Codegen.lean       C printer for the kernel
Mpmc/KernelTest.lean    deterministic trace generator
Cargo.toml              Rust crate manifest and build metadata
build.rs                compiles the C kernel for Cargo
src/lib.rs              safe Rust Queue wrapper
docs/rust.md            Rust API, platform, and TCB documentation
tests/rust_api.rs       Rust FIFO, error, and concurrency tests
include/mpmc.h          the only public header
include/mpmc/detail/    private layout, atomics, generated kernel
src/mpmc.c              four exported symbols for FFI
tests/                  C/C++ tests, layout checks, traces
bench/                  throughput/latency and reference comparison
docs/                   algorithm, proof, API, benchmarks
tools/                  release validation and packaging
.github/                CI, CodeQL, and release workflows
```

## Non-goals

- Values larger than 64 bits, non-trivially-copyable payloads, or a generic
  `T` in the C ABI. Use a handle or an index.
- Blocking/backpressure, dynamic growth, per-thread fairness.
- `peek`, `clear`, `size`, `replace`, shared-memory attach, or SPSC
  specializations. The minimal API omits them.
- A machine-checked lock-freedom theorem, fair-scheduler liveness, or a C11
  memory-model refinement. The algorithm is lock-free by design; the exact
  status of the proof is in `docs/proof.md`. The Lean model fixes each
  logical worker's role (push or pop); the C API still permits any thread to
  call either function.

## Releases

Tagged releases are built, tested, and published by
`.github/workflows/release.yml`. The workflow requires a green `CI` run for
the tagged commit and publishes source, headers, and checksum archives. Source
archives from this commit onward include the Rust crate; the headers archive
remains the C/C++ header-only package. The published v0.1.0 archive predates
the crate. See `RELEASING.md` for the tag and recovery procedure.

## Security

See `SECURITY.md` for the vulnerability-reporting contact and scope.

## License

CPAL-1.0. See `LICENSE` and `NOTICE`. The cell design follows Erez Strauss's
MPMC queue; the comparison reference is the companion C++ project
<https://github.com/mmabdpr/mpmc-queue>. See the attribution in `NOTICE`.
Release notes are in `CHANGELOG.md`; contribution requirements are in
`CONTRIBUTING.md`.
