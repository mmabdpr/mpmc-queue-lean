/*
 * Copyright (c) 2026 Mohammad Mahdi Abdollahpour.
 * The contents of this file are subject to the Common Public Attribution
 * License Version 1.0 (the "License"); you may not use this file except in
 * compliance with the License. You may obtain a copy of the License at
 * https://opensource.org/license/cpal-1-0.
 * The Original Code is mpmc-lean. The Initial Developer is Mohammad Mahdi
 * Abdollahpour. See LICENSE and NOTICE.
 */
/*
 * C ABI build of mpmc.
 *
 * C and C++ callers normally get the same four functions as `static inline`
 * definitions from `mpmc.h` and do not need this translation unit.  It
 * exists so the library can also be loaded through a stable C ABI (FFI,
 * dynamic loading, or a consumer that deliberately wants an out-of-line
 * call).
 */

#include "mpmc/detail/impl.h"

#include <stdbool.h>

mpmc_queue *mpmc_create(uint64_t capacity) {
  if (capacity < 2 || capacity > MPMC_MAX_CAPACITY ||
      (capacity & (capacity - 1)) != 0) {
    return NULL;
  }
  return mpmc_new(capacity, (UINT64_C(1) << 63) - capacity);
}

void mpmc_destroy(mpmc_queue *q) { mpmc_free(q); }

bool mpmc_push(mpmc_queue *q, uint64_t value) {
  if (!mpmc_valid(q)) {
    return false;
  }
  uint64_t sequence = 0;
  return mpmc_kernel_push(q, q->capacity, q->mask, q->limit, value,
                          &sequence) == 0;
}

bool mpmc_pop(mpmc_queue *q, uint64_t *value) {
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
