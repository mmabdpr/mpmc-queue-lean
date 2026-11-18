# API

One header: `#include "mpmc.h"`. The implementation is header-only for C and
C++; the same four symbols are also exported by the static or shared library
for FFI.

## C

```c
#include <stdbool.h>
#include <stdint.h>

typedef struct mpmc_queue mpmc_queue;

mpmc_queue *mpmc_create(uint64_t capacity);
void        mpmc_destroy(mpmc_queue *q);
bool        mpmc_push(mpmc_queue *q, uint64_t value);
bool        mpmc_pop(mpmc_queue *q, uint64_t *value);
```

### `mpmc_create`

```c
mpmc_queue *q = mpmc_create(4096);
```

Allocates and initializes a queue. `capacity` must be a power of two in
`[2, 2^24]`. Returns `NULL` if the capacity is invalid, if allocation fails,
or if the target cannot perform a lock-free 16-byte compare-exchange. The
queue is ready for concurrent use when the call returns. It allocates
`384 + 128 * capacity` bytes (up to 2 GiB at the maximum capacity) and touches
every slot during initialization.

The publication horizon is `2^63 - capacity`; no configuration is exposed.
Exhaustion is therefore unreachable in a practical program, but the internal
constructor used by `tests/test_kernel_trace.c` can create a small horizon for
testing.

### `mpmc_destroy`

```c
mpmc_destroy(q);
```

Frees the queue. `mpmc_destroy(NULL)` is a no-op. The caller must ensure that
no other thread is inside `mpmc_push`/`mpmc_pop` and that no later operation
uses the handle. Destroying a queue in use is undefined behavior.

### `mpmc_push`

```c
bool ok = mpmc_push(q, value);
```

Attempts to append `value`. Returns `true` if it was published, `false` if the
queue is full (or the horizon is reached) or `q` is `NULL`. Successful calls
are totally ordered; the values are consumed in that order.

### `mpmc_pop`

```c
uint64_t value;
bool ok = mpmc_pop(q, &value);
```

Attempts to remove the oldest value. Returns `true` and writes `*value` on
success; returns `false` if the queue is empty, `q` is `NULL`, or `value` is
`NULL`. `*value` is untouched on failure.

## C++

The same header defines one RAII type:

```cpp
namespace mpmc {
class queue {
 public:
  explicit queue(std::uint64_t capacity);
  ~queue();

  queue(queue&&) noexcept;
  queue& operator=(queue&&) noexcept;
  queue(const queue&) = delete;
  queue& operator=(const queue&) = delete;

  bool push(std::uint64_t value) noexcept;
  bool pop(std::uint64_t& value) noexcept;
};
}
```

The constructor throws `std::invalid_argument` for a non-power-of-two or
out-of-range capacity, and `std::runtime_error` if allocation fails or the
target cannot provide lock-free 16-byte compare-exchange. Moved-from queues return
`false` from `push`/`pop`. The C++ wrapper uses exceptions and requires a C++
compiler with exceptions enabled; the C API does not.

```cpp
#include "mpmc.h"

mpmc::queue q(4096);
q.push(1);
std::uint64_t v;
if (q.pop(v)) { /* v == 1 */ }
```

## Concurrency contract

- Any number of threads may call `mpmc_push` and `mpmc_pop` concurrently, in
  any mix. No external lock is needed.
- A queue handle must outlive every operation on it. `mpmc_destroy` requires
  quiescence. Publish a newly created handle to other threads with a
  happens-before edge (for example, create the threads after `mpmc_create`
  returns); do not share a partially initialized handle.
- Moving a `mpmc::queue` is not thread-safe and must not race with another
  thread using either object.
- `mpmc_push`/`mpmc_pop` are non-blocking: they contain no locks, no
  allocation, no syscalls, and no blocking on another thread. They are not
  wait-free; a thread may retry while another thread is descheduled.
- Values are 64-bit words. Ownership of a popped value transfers to the
  caller; the queue never dereferences it.

## Memory ordering and portability

- A 16-byte cell is the atomic publication unit. Cell loads and successful
  cell CAS operations are sequentially consistent; a push is one 16-byte
  compare-exchange and a pop is one 16-byte compare-exchange. The payload and
  its readiness marker are in the same cell, so a consumer cannot observe a
  value without its marker.
- Index hints are acquire-load/release-CAS 64-bit atomics. They are monotone and may lag the
  authoritative cell state; helping closes the gap.
- The cell must be 16-byte aligned and lock-free. The header asserts the
  layout; `mpmc_create` returns `NULL` if the platform-specific lock-free
  check on an aligned 16-byte probe fails. This is a runtime check, so a
  compiler that needs `-mcx16`/`-latomic` or an LSE-capable `-march` must
  provide them.
- On x86-64, compiling 16-byte atomics may require `-mcx16` and/or
  `-latomic` depending on the compiler and target. The binary also requires a
  CPU with `cmpxchg16b` (CX16); `mpmc_create` performs a CPUID check in
  addition to the atomic predicate, but you must deploy on a CX16-capable
  machine. GCC's libatomic reports 16-byte objects as not lock-free even with
  `-mcx16`; on that path the runtime check uses CPUID, and the 16-byte
  operations rely on GNU libatomic's CX16 runtime dispatch. The CMake package
  probes the build and publishes the needed flags through `mpmc::mpmc` and
  `mpmc.pc`.
  If you compile the header by hand on x86-64, pass `-mcx16` (and link
  `-latomic` if your toolchain asks for it); without CX16 support the link
  may fail, or `mpmc_create` returns `NULL` because the 16-byte CAS is not
  lock-free. GCC builds on arm64 may also need an LSE-capable `-march` and
  `-latomic`. Apple silicon is native. Linux arm64 uses the same source path
  and is covered by CI with LSE enabled.
- The queue uses 128-byte slots and separates the write and read hints by
  128 bytes to avoid false sharing. `tests/test_layout.c` checks the layout.

## FFI

The library exports the four symbols with C linkage: `libmpmc.a` by default,
or a shared library with `-DBUILD_SHARED_LIBS=ON`. It is ordinary C with no
Lean runtime dependency; the only allocation is the queue storage in
`mpmc_create`.

```python
# Build with -DBUILD_SHARED_LIBS=ON; the default is a static archive.
import ctypes
lib = ctypes.CDLL("./libmpmc.so")  # or libmpmc.dylib on macOS
lib.mpmc_create.restype = ctypes.c_void_p
lib.mpmc_create.argtypes = [ctypes.c_uint64]
q = lib.mpmc_create(4096)
lib.mpmc_push.argtypes = [ctypes.c_void_p, ctypes.c_uint64]
lib.mpmc_push.restype = ctypes.c_bool
lib.mpmc_push(q, 42)
lib.mpmc_destroy.argtypes = [ctypes.c_void_p]
lib.mpmc_destroy(q)
```

## Limits

- Capacity: power of two, 2 … 2²⁴.
- Payload: one `uint64_t`.
- No `size`, `peek`, `clear`, `replace`, shared-memory attach, or SPSC mode in
  the public API. The internal kernel and tests retain an approximate size and
  a small-horizon constructor for verification.
