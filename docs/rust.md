# mpmc-lean

Safe Rust bindings for **mpmc-lean**, a bounded multi-producer/multi-consumer
queue whose kernel core is modeled in Lean 4 and generated into C. The crate
compiles the same generated C kernel that the C and C++ APIs use; it is not a
second implementation.

```rust
use mpmc_lean::Queue;

let queue = Queue::new(4).expect("queue");
queue.push(10).expect("space");
queue.push(20).expect("space");

assert_eq!(queue.pop(), Some(10));
assert_eq!(queue.pop(), Some(20));
assert_eq!(queue.pop(), None);
```

## Properties

- Bounded ring with a power-of-two capacity from 2 to 2^24.
- One `u64` payload per entry.
- FIFO order.
- `push` and `pop` are non-blocking and never allocate. On a platform where
  the 16-byte atomic operation is lock-free, they do not take a lock or make
  a syscall.
- The queue is `Send + Sync`; share it with `Arc` for MPMC use.
- Dropping the queue frees it. Rust ownership ensures no safe operation races
  with `Drop`.

`Queue::new` returns `CreateError::InvalidCapacity` for a capacity outside the
supported range. `CreateError::Unavailable` means creation failed: allocation
failed, the C constructor rejected the platform, or the required 16-byte
lock-free operations are unavailable.

`Queue::push` returns `PushError::Full` when the queue has no space. The C API
maps the practically unreachable publication-horizon case to the same result.
`Queue::pop` returns `None` when the queue is empty.

## Platform and build requirements

The crate is tested on Linux x86-64 with GCC and Clang, Linux arm64 with
Clang 18, and macOS arm64 with Apple Clang. It requires:

- a GCC or Clang C11 compiler;
- 16-byte lock-free compare-exchange on the target CPU;
- on x86-64, CX16 (`cmpxchg16b`) and, for GCC, the GNU libatomic runtime;
- on Linux arm64, Clang 18. GCC arm64 is rejected at build time because its
  16-byte libatomic implementation is only guaranteed lock-free on newer
  runtimes. Clang's baseline lowering uses LDXP/STXP, inline or outlined
  depending on compiler configuration; it uses LSE only if a user explicitly
  adds an LSE `-march` through `CFLAGS`.

The build script adds `-mcx16` on x86-64, leaves Linux arm64 at its baseline
instruction set, links `libatomic` for GCC on Linux x86-64, and rejects GCC on
Linux arm64 with an instruction to set `CC=clang`. Clang 18 is the tested
Clang version. The script compiles `src/mpmc.c` and the generated header from
the crate package, so no separate CMake build or installed C library is
needed. Windows/MSVC and other targets are rejected with a build error.
macOS x86-64 is accepted by the build script but is not covered by CI.

The required architecture and atomic flags are part of the supported build
profile. Overriding them through `CFLAGS`, `-mcpu`, or a stronger `RUSTFLAGS`
baseline can invalidate the lock-free or linkage assumptions; the crate does
not attempt to repair an unsupported compiler configuration. The CI arm64
runners provide LSE, so the baseline LDXP/STXP execution path is not exercised
on non-LSE hardware; the compiler/runtime atomic lowering remains trusted
rather than machine-checked.

## Concurrency

`Queue` is safe to move between threads and to call concurrently. The test
suite covers debug and optimized builds, FIFO, randomized status transitions,
and mixed-role stress:

```rust
use std::sync::Arc;
use mpmc_lean::Queue;

let queue = Arc::new(Queue::new(2).expect("queue"));
let producer = {
    let queue = Arc::clone(&queue);
    std::thread::spawn(move || {
        for value in 0..100 {
            loop {
                match queue.push(value) {
                    Ok(()) => break,
                    Err(_) => std::hint::spin_loop(),
                }
            }
        }
    })
};

for expected in 0u64..100 {
    loop {
        if let Some(value) = queue.pop() {
            assert_eq!(value, expected);
            break;
        }
        std::hint::spin_loop();
    }
}
producer.join().expect("producer");
```

A push or pop can retry after losing a race. The C queue is designed to be
lock-free, but the Lean development does not contain a machine-checked
lock-freedom or fair-scheduler liveness theorem (see below). The test
deadlines bound the retry loops in this crate's tests; a C operation that
never returns is bounded only by the CI job timeout, because the C API has no
operation timeout.

## What is proved, and what is trusted

The Lean theorem covers the sequentially consistent kernel-event core: cell
protocol, stage simulation, finite global runs, FIFO, real invocation and
response positions, caller-visible outputs, exact status codes, and
authenticated trace tags. The full statement and hypotheses are in
[`docs/proof.md`](https://github.com/mmabdpr/mpmc-queue-lean/blob/main/docs/proof.md).

The following are trusted or unmechanized, exactly as for the C API:

- the C printer and compiler;
- the compiler's 16-byte atomic lowering and the platform atomics;
- allocation, initialization, layout, and validation;
- the C11/C++ memory-model refinement;
- kernel-level progress and lock-freedom;
- this Rust wrapper's ownership, lifetime, and `Send`/`Sync` reasoning.

The Rust layer is a small hand-written FFI wrapper. It is tested for FIFO,
capacity, errors, and concurrent exactly-once delivery, but it is not part of
the Lean proof and does not make the C implementation proved end to end.

## License

CPAL-1.0. See `LICENSE` and `NOTICE` in the source distribution.
