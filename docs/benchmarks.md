# Benchmarks

All numbers are from an Apple M3 Max (14 hardware threads), macOS arm64,
Apple clang 21.0.0, capacity 4096. The machine is shared and not isolated;
absolute rates vary by roughly ±20% between runs. The useful number is the
same-run ratio against the C++ reference.

## Comparison harness

`bench/compare.cpp` runs both queues in the same process, with the same
topology, value sequence, start barrier, and spin loop. Each round runs one
queue and then the other, alternating which one goes first, so slow drift in
host load affects both sides. It is a parity check, not a calibrated record
attempt.

```sh
cmake -S . -B build-compare \
  -DCMAKE_BUILD_TYPE=Release \
  -DMPMC_ENABLE_LTO=OFF \
  -DMPMC_REFERENCE_INCLUDE_DIR=/path/to/mpmc-queue/include
cmake --build build-compare --target mpmc_compare -j
./build-compare/mpmc_compare 20 1000000
```

The fifth numeric argument is nonzero to print per-round rates and min/median/
max. The reference is `mpmc::mpmc_queue<uint64_t, 4096, uint32_t>` from the
companion repository <https://github.com/mmabdpr/mpmc-queue> at commit
`0b980ff60ee9164252b3e4ff5a0c5f03a048ef84`; it uses a 32-bit index and a
compile-time capacity, so the comparison is same-shape but not bit-for-bit
like-for-like.

Twenty rounds, 1,000,000 values per producer, one representative session
(medians of the per-round rates):

| Topology | mpmc-lean (M/s) | C++ reference (M/s) | Ratio |
|---|---:|---:|---:|
| 1P / 1C | 109.5 | 192.6 | 0.57× |
| 2P / 2C | 12.8 | 15.3 | 0.83× |
| 4P / 4C | 5.0 | 5.0 | 0.99× |
| 4P / 1C | 6.8 | 6.4 | 1.07× |
| 1P / 4C | 6.8 | 6.4 | 1.07× |

This is a Release, non-LTO build (`-DMPMC_ENABLE_LTO=OFF`) using the
header-only C++ class. At 1P/1C it is about 9.1 ns of wall-clock time per
transferred value (aggregate reciprocal throughput, not per-operation
latency). In this representative session 4P/1C and 1P/4C are ahead, 4P/4C is
parity (0.99×), and the 1P/1C pair is 43% behind. The implementation uses
acquire/release hints and seq_cst cell atomics to align the C execution with
the SC proof; the reference uses a relaxed-hint profile. The difference is
consistent with the stronger ordering, but the harness does not isolate the
cause.
The host is shared, so an individual run can move by tens of percent, but the
ratio is stable because the two sides are interleaved. The C++ class includes
the generated kernel, so it does not rely on link-time optimization for the
hot path.

## The layout fix

The first version of this library typed the slot array as a packed
`mpmc_cell[]`, so `q->slots[i]` advanced by 16 bytes instead of the documented
128-byte stride. The algorithm was still correct, but adjacent slots shared
cache lines, and the asymmetric 4P/1C and 1P/4C topologies were 10–14% behind
the reference. The slot type is now a 128-byte-aligned `mpmc_slot`, the field
is reached through `mpmc_slots(q)`, and `tests/test_layout.c` asserts the
stride, alignment, and header offsets. The numbers above are from the fixed
layout.

The reference is a header-only template with a compile-time capacity and a
32-bit index; mpmc-lean keeps a 64-bit index. The C++ class caches the
geometry in the handle, while the C header-only path reloads `capacity`,
`mask`, `limit`, and `magic` per call; only the C++ class is close to the
reference's push/pop shape, and even that comparison is same-shape rather
than instruction-for-instruction.

## Non-LTO and inline paths

`mpmc.h` is header-only: both the C functions and the C++ `mpmc::queue`
class compile the generated kernel into the caller's translation unit, so
push/pop inline without LTO. The static library exports the same four
functions for FFI; those calls are out-of-line unless the consumer also
builds with LTO. The `mpmc_bench` and `mpmc_bench_header` targets measure
the C++ and C header-only paths; the comparison harness uses `mpmc::queue`.

Guidance:

- C and C++ consumers include `mpmc.h`; push/pop inline by default.
- FFI/dynamic-language consumers use the four exported symbols in
  `libmpmc.a` (or the shared library); the archive ships native objects and
  can be linked by a different compiler.
- There is no separate "fast" or "inline" API to choose.

## What the numbers do and do not show

- They show 0.57×–1.07× in the representative run: 4P/1C and 1P/4C are
  ahead, 4P/4C is parity, and the 1P/1C pair is 43% behind because the
  implementation uses acquire/release hints and seq_cst cell atomics for the
  SC model.
- They do not show a throughput record. The host is shared; the same topology
  moves by roughly ±20–30% between runs, which is why the harness interleaves
  and reports medians.
- They do not cover ping-pong latency percentiles, cross-process/shared
  memory, or a NUMA host. Those are not part of this release.
- They are from an arm64 host. x86-64 performance is unmeasured; on x86-64 a
  seq_cst 16-byte cell load lowers to a locked instruction and may behave
  differently.
- The Lean proofs and the differential tests run on the same source; the
  benchmark is a separate C/C++ build, not a proof.

## Reproduce

```sh
# Lean and tests
lake build
lake exe mpmc-codegen
lake exe mpmc-kernel-trace
cmake -S . -B build -DCMAKE_BUILD_TYPE=Release
cmake --build build -j
ctest --test-dir build --output-on-failure

# Quick single-topology run (inline C++ wrapper)
./build/mpmc_bench 1 1 3000000 4096

# Header-only C path (no LTO)
./build/mpmc_bench_header 1 1 2000000 4096

# Same-shape comparison (needs the C++ reference headers)
cmake -S . -B build-compare -DCMAKE_BUILD_TYPE=Release \
  -DMPMC_ENABLE_LTO=OFF \
  -DMPMC_REFERENCE_INCLUDE_DIR=/path/to/mpmc-queue/include
cmake --build build-compare --target mpmc_compare -j
./build-compare/mpmc_compare 20 1000000
# or one topology:
./build-compare/mpmc_compare 20 1000000 1 1
```
