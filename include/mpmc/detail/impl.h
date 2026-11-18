/*
 * Copyright (c) 2026 Mohammad Mahdi Abdollahpour.
 * The contents of this file are subject to the Common Public Attribution
 * License Version 1.0 (the "License"); you may not use this file except in
 * compliance with the License. You may obtain a copy of the License at
 * https://opensource.org/license/cpal-1-0.
 * The Original Code is mpmc-lean. The Initial Developer is Mohammad Mahdi
 * Abdollahpour. See LICENSE and NOTICE.
 */
#ifndef MPMC_DETAIL_IMPL_H
#define MPMC_DETAIL_IMPL_H

/*
 * Implementation details of mpmc.
 *
 * This header is included by the public `mpmc.h` and by the C ABI
 * translation unit.  It is not part of the public interface: the layout,
 * the atomic helpers, and the generated kernel are version-locked to the
 * installed library.
 *
 * Atomics use the GCC/Clang `__atomic` builtins rather than C11 `_Atomic`
 * so the same definitions compile as C11 and C++17.  The builtins lower to
 * the same instructions as std::atomic on the supported compilers.
 */

#include <assert.h>
#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
#include <cstdlib>
#include <cstring>
#else
#include <stdlib.h>
#include <string.h>
#endif

#ifndef __cplusplus
#include <stdatomic.h> /* __ATOMIC_* constants */
#endif

#if defined(__x86_64__)
#include <cpuid.h>
#ifndef bit_CMPXCHG16B
#define bit_CMPXCHG16B (1u << 13)
#endif
#endif

#define MPMC_MAGIC UINT64_C(0x4d504d434c45414e) /* "MPMCLEAN" */
/* Layout/ABI version, independent of the 0.1.0 release version. */
#define MPMC_VERSION 1u
#define MPMC_ABI_TAG 1u
#define MPMC_HEADER_BYTES 384u
#define MPMC_SLOT_BYTES 128u

/* Largest accepted capacity (2^24 slots, 2 GiB of slot storage). */
#define MPMC_MAX_CAPACITY (UINT64_C(1) << 24)

/* Status codes returned by the generated kernel.  The public API maps
 * these to a single boolean; the differential tests inspect them. */
typedef enum mpmc_kernel_status {
  MPMC_KERNEL_OK = 0,
  MPMC_KERNEL_FULL = 1,
  MPMC_KERNEL_EMPTY = 2,
  MPMC_KERNEL_EXHAUSTED = 3
} mpmc_kernel_status;

#if defined(__cplusplus)
#define MPMC_ALIGNAS(n) alignas(n)
#define MPMC_ALIGNOF(T) alignof(T)
#define MPMC_ALIGNED_ALLOC(alignment, size) std::aligned_alloc((alignment), (size))
#define MPMC_MEMSET(ptr, value, size) std::memset((ptr), (value), (size))
#define MPMC_FREE(ptr) std::free(ptr)
#else
#define MPMC_ALIGNAS(n) _Alignas(n)
#define MPMC_ALIGNOF(T) _Alignof(T)
#define MPMC_ALIGNED_ALLOC(alignment, size) aligned_alloc((alignment), (size))
#define MPMC_MEMSET(ptr, value, size) memset((ptr), (value), (size))
#define MPMC_FREE(ptr) free(ptr)
#endif

/*
 * One cell is the atomic publication unit.  The marker is
 * (position << 1) | ready; the payload is the user word.  The whole
 * 16-byte object is published by one compare-exchange, so a reader can
 * never observe a marker without its payload or vice versa.
 */
typedef struct mpmc_cell {
  MPMC_ALIGNAS(16) uint64_t marker;
  uint64_t payload;
} mpmc_cell;

static_assert(sizeof(mpmc_cell) == 16, "cell must be 16 bytes");
static_assert(MPMC_ALIGNOF(mpmc_cell) == 16, "cell must be 16-byte aligned");

/*
 * One 128-byte slot.  The atomic cell occupies the first 16 bytes; the rest
 * is padding so adjacent slots never share a cache line.  Indexing the slots
 * array therefore advances by 128 bytes, not by sizeof(mpmc_cell).
 */
typedef struct mpmc_slot {
  MPMC_ALIGNAS(MPMC_SLOT_BYTES) mpmc_cell value;
  uint8_t pad[MPMC_SLOT_BYTES - sizeof(mpmc_cell)];
} mpmc_slot;

static_assert(sizeof(mpmc_slot) == MPMC_SLOT_BYTES, "slot must be 128 bytes");
static_assert(MPMC_ALIGNOF(mpmc_slot) == MPMC_SLOT_BYTES,
              "slot must be 128-byte aligned");

typedef struct mpmc_queue mpmc_queue;

struct mpmc_queue {
  uint64_t magic;        /* +0   */
  uint32_t version;      /* +8   */
  uint32_t cell_bytes;   /* +12  */
  uint64_t capacity;     /* +16  */
  uint64_t mask;         /* +24  */
  uint64_t limit;        /* +32  */
  uint64_t slot_bytes;   /* +40  */
  uint64_t header_bytes; /* +48  */
  uint64_t abi_tag;      /* +56  */
  uint8_t pad0[64];      /* +64  */

  uint64_t write_index; /* +128 */
  uint8_t pad1[120];    /* +136 */

  uint64_t read_index; /* +256 */
  uint8_t pad2[120];   /* +264 */

  /*
   * The slot array follows this header at offset MPMC_HEADER_BYTES.  It is
   * not declared as a flexible array member so that this header compiles
   * cleanly as C++ as well as C; use mpmc_slots() to reach it.
   */
};

static_assert(offsetof(struct mpmc_queue, write_index) == 128,
              "write index must start a cache line");
static_assert(offsetof(struct mpmc_queue, read_index) == 256,
              "read index must start a cache line");
static_assert(sizeof(struct mpmc_queue) == MPMC_HEADER_BYTES,
              "header size must be exact");
static_assert(MPMC_HEADER_BYTES % MPMC_SLOT_BYTES == 0,
              "slot array must start on a slot boundary");

static inline mpmc_slot *mpmc_slots(mpmc_queue *q) {
  return (mpmc_slot *)((uint8_t *)q + MPMC_HEADER_BYTES);
}

static inline const mpmc_slot *mpmc_slots_const(const mpmc_queue *q) {
  return (const mpmc_slot *)((const uint8_t *)q + MPMC_HEADER_BYTES);
}

static inline uint64_t mpmc_load_u64(const uint64_t *p, int order) {
  return __atomic_load_n((uint64_t *)p, order);
}

static inline mpmc_cell mpmc_load_cell(const mpmc_cell *p, int order) {
  mpmc_cell value;
  __atomic_load((mpmc_cell *)p, &value, order);
  return value;
}

/* Whether the 16-byte cell compare-exchange is lock-free on this target.
 * The probe object is 16-byte aligned; a plain integer size is not enough
 * because x86-64 cmpxchg16b and some ARM configurations depend on it. */
static inline int mpmc_cell_lock_free(void) {
#if defined(__x86_64__)
  /* CPUID leaf 1, ECX bit 13 is CX16 (cmpxchg16b).  The compile-time atomic
   * predicate can fold to true for a target that has the instruction; this
   * runtime check rejects deployment on a CPU that lacks it. */
  unsigned int eax = 0, ebx = 0, ecx = 0, edx = 0;
  if (!__get_cpuid(1, &eax, &ebx, &ecx, &edx) ||
      (ecx & bit_CMPXCHG16B) == 0) {
    return 0;
  }
#if defined(__GNUC__) && !defined(__clang__) && \
    defined(__GCC_HAVE_SYNC_COMPARE_AND_SWAP_16)
  /* GCC's libatomic predicate is conservative for 16-byte objects on
   * x86-64. With -mcx16 and the GNU libatomic used in CI, the 16-byte
   * operations dispatch to CX16 on a CX16 CPU. The CPUID check above covers
   * the deployment CPU. */
  return 1;
#endif
#endif
  mpmc_cell probe = {0, 0};
  return __atomic_is_lock_free(sizeof(probe), &probe);
}

/* A live queue handle.  The magic check rejects NULL and a handle whose
 * magic no longer matches; destroyed/stale handles are outside the lifetime
 * contract, so this is not a use-after-free protection. */
static inline int mpmc_valid(const mpmc_queue *q) {
  return q != NULL && q->magic == MPMC_MAGIC && q->version == MPMC_VERSION &&
         q->abi_tag == MPMC_ABI_TAG;
}

/*
 * Allocate and initialise a queue.  `limit` is the publication horizon;
 * the public constructor uses 2^63 - capacity.  Returns NULL for an invalid
 * geometry, a platform without lock-free 16-byte atomics, or allocation
 * failure.
 */
static inline mpmc_queue *mpmc_new(uint64_t capacity, uint64_t limit) {
  if (capacity < 2 || capacity > MPMC_MAX_CAPACITY) {
    return NULL;
  }
  if ((capacity & (capacity - 1)) != 0) {
    return NULL;
  }
  const uint64_t max_limit = (UINT64_C(1) << 63) - capacity;
  if (limit == 0 || limit > max_limit) {
    return NULL;
  }
  if (!mpmc_cell_lock_free()) {
    return NULL;
  }
  if (capacity > (SIZE_MAX - MPMC_HEADER_BYTES) / MPMC_SLOT_BYTES) {
    return NULL;
  }

  const size_t bytes =
      (size_t)MPMC_HEADER_BYTES + (size_t)capacity * MPMC_SLOT_BYTES;
  void *memory = MPMC_ALIGNED_ALLOC(128, bytes);
  if (memory == NULL) {
    return NULL;
  }

  mpmc_queue *q = (mpmc_queue *)memory;
  MPMC_MEMSET(q, 0, MPMC_HEADER_BYTES);
  q->magic = MPMC_MAGIC;
  q->version = MPMC_VERSION;
  q->cell_bytes = (uint32_t)sizeof(mpmc_cell);
  q->capacity = capacity;
  q->mask = capacity - 1;
  q->limit = limit;
  q->slot_bytes = MPMC_SLOT_BYTES;
  q->header_bytes = MPMC_HEADER_BYTES;
  q->abi_tag = MPMC_ABI_TAG;

  __atomic_store_n(&q->write_index, 0, __ATOMIC_RELAXED);
  __atomic_store_n(&q->read_index, 0, __ATOMIC_RELAXED);
  mpmc_slot *slots = mpmc_slots(q);
  for (uint64_t j = 0; j < capacity; ++j) {
    mpmc_cell initial = {j << 1, 0};
    __atomic_store(&slots[j].value, &initial, __ATOMIC_RELAXED);
  }
  return q;
}

static inline void mpmc_free(mpmc_queue *q) {
  if (q == NULL) {
    return;
  }
  q->magic = 0;
  MPMC_FREE(q);
}

/*
 * Approximate number of published-but-unconsumed values.  The two cursor
 * hints are read without a common snapshot, so under concurrency the result
 * may be stale or an under-approximation.  It is exact when quiescent.
 * This is an internal diagnostic; it is not part of the public API.
 */
static inline uint64_t mpmc_size_approx_internal(const mpmc_queue *q) {
  if (!mpmc_valid(q)) {
    return 0;
  }
  const uint64_t write = mpmc_load_u64(&q->write_index, __ATOMIC_RELAXED);
  const uint64_t read = mpmc_load_u64(&q->read_index, __ATOMIC_RELAXED);
  if (write < read) {
    return 0;
  }
  const uint64_t size = write - read;
  return size > q->capacity ? q->capacity : size;
}

/*
 * The generated hot loops.  They use the layout and atomic helpers above;
 * the public header and the C ABI translation unit both include this file.
 */
#include "kernel.inc"

#endif /* MPMC_DETAIL_IMPL_H */
