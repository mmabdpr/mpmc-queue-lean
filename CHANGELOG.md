# Changelog

## 0.1.0 - 2026-11-18

- First public release of `mpmc-lean`.
- Bounded MPMC queue with a power-of-two capacity from 2 to 2^24, one 64-bit
  payload per entry, FIFO ordering, and a cell/marker design built to be lock-free.
- Lean 4.36 proof of the sequentially consistent kernel-event core: safety,
  FIFO, the cell protocol, stage simulation, finite global runs, and
  linearizable histories with real invocation, linearization, and response
  positions.
- Generated C kernel, C11/C++17 header API, static and shared libraries,
  CMake and pkg-config packages, FFI and installed consumers.
- CI on Linux x86-64 (GCC and Clang), Linux arm64, and macOS arm64, including
  Debug, ASan/UBSan, and TSan jobs. Annotated tag releases rebuild and verify
  the source, headers, checksums, and installed package before publishing.
- Documented trusted computing base: the C printer, compiler and 16-byte
  atomic lowering, allocation/initialization wrapper, C11/C++ lowering, and
  kernel-level progress. The C library is not proved end to end.
- Licensed under CPAL-1.0; see `LICENSE` and `NOTICE`.
