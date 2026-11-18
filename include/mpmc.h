/*
 * Copyright (c) 2026 Mohammad Mahdi Abdollahpour.
 * The contents of this file are subject to the Common Public Attribution
 * License Version 1.0 (the "License"); you may not use this file except in
 * compliance with the License. You may obtain a copy of the License at
 * https://opensource.org/license/cpal-1-0.
 * The Original Code is mpmc-lean. The Initial Developer is Mohammad Mahdi
 * Abdollahpour. See LICENSE and NOTICE.
 */
#ifndef MPMC_H
#define MPMC_H

/*
 * mpmc: a bounded MPMC queue designed to be lock-free.
 *
 * This is the only header you need:
 *
 *   #include "mpmc.h"
 *
 *   mpmc_queue *q = mpmc_create(4096);
 *   mpmc_push(q, 42);
 *   uint64_t value;
 *   if (mpmc_pop(q, &value)) { ... }
 *   mpmc_destroy(q);
 *
 * C++ users get the same header plus a small RAII wrapper:
 *
 *   mpmc::queue q(4096);
 *   q.push(42);
 *   uint64_t value;
 *   if (q.pop(value)) { ... }
 *
 * The queue stores one 64-bit word per entry.  Capacity is a power of two
 * in [2, 2^24].  push/pop never block, never allocate, and never take a
 * lock.  They are not wait-free: an individual call may retry after losing
 * a race.  The design is lock-free, but no machine-checked liveness theorem
 * is claimed; see docs/proof.md.
 *
 * The implementation (layout, generated kernel, atomics) is included below
 * and is private.  Do not depend on the layout or on any symbol that is not
 * one of the four functions above or the C++ class.
 */

#include <stdbool.h>
#include <stdint.h>

#ifdef __cplusplus
#include <cstdint>
#include <new>
#include <stdexcept>
#endif

typedef struct mpmc_queue mpmc_queue;

/* -------------------------------------------------------------------------
 * Implementation (private)
 * ---------------------------------------------------------------------- */

#include "mpmc/detail/impl.h"

static inline mpmc_queue *mpmc_create(uint64_t capacity) {
  if (capacity < 2 || capacity > MPMC_MAX_CAPACITY ||
      (capacity & (capacity - 1)) != 0) {
    return NULL;
  }
  return mpmc_new(capacity, (UINT64_C(1) << 63) - capacity);
}

static inline void mpmc_destroy(mpmc_queue *q) { mpmc_free(q); }

static inline bool mpmc_push(mpmc_queue *q, uint64_t value) {
  if (!mpmc_valid(q)) {
    return false;
  }
  uint64_t sequence = 0;
  return mpmc_kernel_push(q, q->capacity, q->mask, q->limit, value,
                          &sequence) == 0;
}

static inline bool mpmc_pop(mpmc_queue *q, uint64_t *value) {
  if (!mpmc_valid(q) || value == NULL) {
    return false;
  }
  uint64_t out = 0;
  uint64_t sequence = 0;
  if (mpmc_kernel_pop(q, q->capacity, q->mask, q->limit, &out, &sequence) !=
      0) {
    return false;
  }
  *value = out;
  return true;
}

/* -------------------------------------------------------------------------
 * C++ RAII wrapper
 * ---------------------------------------------------------------------- */

#ifdef __cplusplus
namespace mpmc {

class queue {
 public:
  explicit queue(std::uint64_t capacity)
      : q_(mpmc_create(capacity)),
        capacity_(q_ != nullptr ? q_->capacity : 0),
        mask_(q_ != nullptr ? q_->mask : 0),
        limit_(q_ != nullptr ? q_->limit : 0) {
    if (q_ == nullptr) {
      if (capacity < 2 || capacity > MPMC_MAX_CAPACITY ||
          (capacity & (capacity - 1)) != 0) {
        throw std::invalid_argument(
            "mpmc: capacity must be a power of two in [2, 2^24]");
      }
      throw std::runtime_error("mpmc: queue creation failed");
    }
  }

  ~queue() { mpmc_destroy(q_); }

  queue(const queue &) = delete;
  queue &operator=(const queue &) = delete;

  queue(queue &&other) noexcept
      : q_(other.q_),
        capacity_(other.capacity_),
        mask_(other.mask_),
        limit_(other.limit_) {
    other.q_ = nullptr;
    other.capacity_ = 0;
    other.mask_ = 0;
    other.limit_ = 0;
  }

  queue &operator=(queue &&other) noexcept {
    if (this != &other) {
      mpmc_destroy(q_);
      q_ = other.q_;
      capacity_ = other.capacity_;
      mask_ = other.mask_;
      limit_ = other.limit_;
      other.q_ = nullptr;
      other.capacity_ = 0;
      other.mask_ = 0;
      other.limit_ = 0;
    }
    return *this;
  }

  bool push(std::uint64_t value) noexcept {
    if (q_ == nullptr) {
      return false;
    }
    std::uint64_t sequence = 0;
    return mpmc_kernel_push(q_, capacity_, mask_, limit_, value, &sequence) ==
           0;
  }

  bool pop(std::uint64_t &value) noexcept {
    if (q_ == nullptr) {
      return false;
    }
    std::uint64_t out = 0;
    std::uint64_t sequence = 0;
    if (mpmc_kernel_pop(q_, capacity_, mask_, limit_, &out, &sequence) != 0) {
      return false;
    }
    value = out;
    return true;
  }

 private:
  mpmc_queue *q_;
  std::uint64_t capacity_;
  std::uint64_t mask_;
  std::uint64_t limit_;
};

} // namespace mpmc
#endif

#endif /* MPMC_H */
