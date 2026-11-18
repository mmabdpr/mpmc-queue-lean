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
 * Header-only half of the mixed ABI test.  It operates on a handle created by
 * the out-of-line library translation unit.
 */
#include "mpmc.h"

#include <stdint.h>

int mixed_inline_roundtrip(mpmc_queue *q, uint64_t base, uint64_t count) {
  for (uint64_t i = 0; i < count; ++i) {
    if (!mpmc_push(q, base + i)) {
      return 1;
    }
  }
  for (uint64_t i = 0; i < count; ++i) {
    uint64_t value = 0;
    if (!mpmc_pop(q, &value) || value != base + i) {
      return 2;
    }
  }
  return 0;
}
