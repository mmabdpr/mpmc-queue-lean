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
 * Layout regression test.
 *
 * The slot stride is part of the performance contract.  A regression to a
 * packed cell array silently shares cache lines between adjacent slots, so
 * check the internal geometry explicitly.
 */
#include "mpmc.h"

#include <stddef.h>
#include <stdint.h>

int main(void) {
  if (sizeof(mpmc_cell) != 16) {
    return 1;
  }
  if (sizeof(mpmc_slot) != 128) {
    return 1;
  }
  if (MPMC_ALIGNOF(mpmc_slot) != 128) {
    return 1;
  }
  if (offsetof(struct mpmc_queue, write_index) != 128) {
    return 1;
  }
  if (offsetof(struct mpmc_queue, read_index) != 256) {
    return 1;
  }
  if (sizeof(struct mpmc_queue) != MPMC_HEADER_BYTES) {
    return 1;
  }

  mpmc_queue *q = mpmc_create(8);
  if (q == NULL) {
    return 1;
  }
  const mpmc_slot *slots = mpmc_slots_const(q);
  if (((uintptr_t)slots & (MPMC_SLOT_BYTES - 1)) != 0) {
    mpmc_destroy(q);
    return 1;
  }
  if ((const char *)&slots[1] - (const char *)&slots[0] !=
      (ptrdiff_t)MPMC_SLOT_BYTES) {
    mpmc_destroy(q);
    return 1;
  }
  if ((const char *)&slots[7] - (const char *)&slots[0] !=
      (ptrdiff_t)(7 * MPMC_SLOT_BYTES)) {
    mpmc_destroy(q);
    return 1;
  }
  mpmc_destroy(q);
  return 0;
}
