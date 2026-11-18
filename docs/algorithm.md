# Algorithm

The pseudocode, invariants, and correctness arguments in this document are
stated for the **sequentially consistent** model. The C implementation uses
sequentially consistent cell atomics and acquire/release hints; the lowering from
C11/C++ to the machine is a documented TCB obligation, not a machine-checked
theorem (see `docs/proof.md`).

This is a bounded MPMC queue in the cell/marker family. The implementation is
a ring of `C` slots (`C` a power of two); each slot holds one 16-byte cell.
The design is the same as the companion C++ queue, with two simplifications:
the payload is always one 64-bit word, and the publication horizon is fixed at
creation by the public constructor (an internal test constructor can choose a
smaller horizon).

## Layout

```
byte 0     magic, version, cell size, capacity, mask, limit, ...
byte 128   write_index   (atomic uint64, own 128-byte line)
byte 256   read_index    (atomic uint64, own 128-byte line)
byte 384   slot 0 cell   (16 bytes used, 128-byte stride)
           slot 1 cell
           ...
```

A cell is

```c
typedef struct {
  alignas(16) uint64_t marker;
  uint64_t payload;
} mpmc_cell;
```

The whole 16-byte object is accessed with 16-byte atomic operations
(GCC/Clang `__atomic` builtins). A cell is loaded and stored as a unit; a
compare-exchange compares and replaces both words. That is the
central trick: publishing a value and publishing its readiness are one
atomic operation, so a reader can never observe a marker that names position
`p` together with a payload from a different position.

A marker is

```
marker = 2 * position + ready        ready in {0, 1}
```

- `position = marker >> 1`
- `ready    = marker & 1`
- `marker` even: the cell is **empty for that position** (the position has not
  been published, or has been consumed and the cell was reset to the next
  position in the same slot).
- `marker` odd: the cell is **published at that position**; the payload word
  is the value.

Slots are reused every `C` positions: position `p` lives in slot `p & (C-1)`.
Each slot occupies a full 128-byte stride (`mpmc_slot`), so adjacent slots
never share a cache line; the slot array begins at header offset 384 and is
reached through `mpmc_slots(q)`. `tests/test_layout.c` checks the stride and
alignment.

## The slot view

Let `W` be the number of publications (the next position to publish) and `R`
the number of consumptions (the next position to consume). Both are ghost
counters in the proof; the implementation only stores the two hints.

For a slot `j`, the positions that map to it are `j, j+C, j+2C, ...`. Define

```
slotPos(R, j, C) = the unique p in [R, R+C) with p % C = j
                 = j + ceil((R - j) / C) * C
```

This is the cell's **current position**. The cell is full exactly when
`slotPos < W`, and its payload is the value at `slotPos`. This is the whole
protocol invariant:

> Slot `j` always describes the first position at or after `R` that maps to
> `j`. It is ready iff that position is below `W`.

`slotPos` is unique because `[R, R+C)` has exactly `C` consecutive integers
and therefore exactly one representative of each residue mod `C`. This
uniqueness is the load-bearing lemma; everything else is arithmetic.

A few consequences:

- At the write hint `w = W`, slot `W & (C-1)` is **empty at `W`** when
  `W - R < C`, and **full at `W-C`** when `W - R = C`. That is, a push either
  publishes at `W` or reports full.
- At the read hint `r = R`, slot `R & (C-1)` is **full at `R`** when `R < W`,
  and **empty at `R`** when `R = W`. That is, a pop either consumes at `R` or
  reports empty.
- A cell is reset after consumption to the next position in its slot,
  `position + C`, with a zero payload. The next publication at that slot is
  exactly `position + C`.

## Push

```
loop:
  w = load(write_index, acquire)
  if w >= limit: return EXHAUSTED
  cell = load(slot[w & mask], seq_cst)
  p = cell.marker >> 1

  if p == w:
    if cell is empty:
      CAS(cell, cell, { marker: 2*w+1, payload: value },
          seq_cst, seq_cst)
      on success:
        result = w
        CAS(write_index, w, w+1, release)   # may fail; another thread helped
        return OK
    else:
      # position w is already published; the write hint is stale
      CAS(write_index, w, w+1, release)
      continue

  behind = w - p                    # unsigned 64-bit subtraction
  if behind == capacity: return FULL
  if behind > 2^63:
    # the marker is ahead of the hint: the slot was already consumed
    CAS(write_index, w, w+1, release)
    continue
  # otherwise the snapshot was stale; the SC invariant proves this branch
  # unreachable, and the generated fallback retries from the hint load
```

The CAS is the publication point. Its expected value is the whole cell that
was loaded, so it succeeds only if the cell still is exactly that empty cell.
The payload is written in the same CAS.

`publish_write` is a compare-exchange from `w` to `w+1`, not a store: a
producer that was descheduled after its cell CAS must not move the hint
backwards after another producer has advanced it. The hint is monotone.

## Pop

```
loop:
  r = load(read_index, acquire)
  if r >= limit: return EXHAUSTED
  cell = load(slot[r & mask], seq_cst)
  p = cell.marker >> 1

  if p == r:
    if cell is ready:
      CAS(cell, cell, { marker: 2*(r+C), payload: 0 },
          seq_cst, seq_cst)
      on success:
        value = cell.payload          # from the local snapshot
        result = r
        CAS(read_index, r, r+1, release)
        return OK
    else:
      return EMPTY

  ahead = p - r
  if ahead < 2^63:
    # another consumer took r; help the hint forward
    CAS(read_index, r, r+1, release)
    continue
  # otherwise stale snapshot; the SC invariant proves this branch
  # unreachable, and the generated fallback retries from the hint load
```

The pop cell CAS is **sequentially consistent**, matching the cell load that
classifies it. The payload is read from the local `expected` snapshot after a
successful CAS; because the CAS compares the whole 16-byte cell, that snapshot
is exactly the published cell, payload included. The acquire hint load and
release hint CAS separately order hint advancement around the cell update.

The successful pop resets the cell to `empty(r + C)` with a zero payload. The
next producer to reach that slot must CAS against that exact empty cell, so a
stale producer cannot publish into a cell that has moved on.

## Hints and helping

`write_index` and `read_index` are **hints**, not authoritative counters. They
are monotone, advance at most one position at a time, and may lag the cell
state by at most one. Any thread that observes a published-but-unadvanced
write, or a consumed-but-unadvanced read, is allowed to advance the hint with
a release compare-exchange. The compare-exchange is what keeps a delayed
thread from moving the hint backwards.

A successful cell CAS winner may be descheduled before it advances the hint.
Another participant then sees the cell in its new state and helps. This is why
the queue is non-blocking: no thread ever waits for a *particular* thread to
make progress. It is not a wait-free claim: a thread can lose races
indefinitely, and a finite retry bound is not mechanized (see
`docs/proof.md`).

There is at most one pending advance **per cursor**: `W - w <= 1` and
`R - r <= 1`. A cell CAS publishes at most one position, and the hint advances
by exactly one, so the gap cannot grow. The helping branches use the exact
guards `W = w + 1` (write) and `R = r + 1` (read).

## False returns

A push returns `FULL` only when the slot at `w` carries the full marker
`w - C`, which happens exactly when `W - R = C` and `w = W`. A pop returns
`EMPTY` only when the slot at `r` carries the empty marker `r`, which happens
exactly when `R = W` and `r = R`. If a hint is stale, the loop helps first and
reloads, so a false `FULL`/`EMPTY` cannot be returned while another thread is
merely late in advancing the hint.

`EXHAUSTED` is different: it is a real, permanent condition. The publication
horizon is `limit`; positions `>= limit` are never published. A push at
`W = limit` returns `EXHAUSTED`; a pop at `R = limit` returns `EXHAUSTED`.
Already-published values can still be drained. The default limit is
`2^63 - C`, which is the largest value for which every marker
`2*position + 1` fits in an unsigned 64-bit word even at the last slot.

## Memory ordering

| Operation | Order | Why |
|---|---|---|
| Cell load (classify) | seq_cst | Latest cell snapshot; aligns the C execution with the SC proof |
| Push cell CAS | seq_cst / seq_cst | Publishes payload and readiness as one atomic unit |
| Pop cell CAS | seq_cst / seq_cst | Consumes and resets the cell; latest reset is visible |
| Hint load | acquire | Acquires the cell publication/reset ordered before the hint CAS |
| Hint CAS | release | Hints are monotone; release publishes the preceding cell state |
| Creation / cell init | relaxed | No concurrent access before publication of the handle |

The cell is the only object whose value carries a payload. Hints only say
where to look; a stale hint can cause extra work but never a wrong result,
because the cell CAS validates the whole cell.

## Capacity, alignment, horizon

- `C` is a power of two in `[2, 2^24]`; the slot index is `p & (C - 1)`. The
  proof uses `p % C`; the implementation's mask is the same operation for a
  power of two.
- The allocation is 128-byte aligned. The cell is at offset 0 of each
  128-byte slot; the write and read hints each own a 128-byte line.
- `limit` is in `[1, 2^63 - C]`. The default is `2^63 - C`. A smaller limit is
  useful in tests; it makes `EXHAUSTED` reachable after a few operations.

## Not provided

`peek`, `clear`, replace/conflation, blocking/backpressure, dynamic growth,
SPSC specialization, shared memory, and arbitrary payloads are not part of
this release. `clear` in particular would need a quiescence precondition and a new
generation/epoch argument; leaving it out keeps the verified state machine
small.
