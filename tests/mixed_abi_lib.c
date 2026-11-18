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
 * Out-of-line half of the mixed ABI test.  This translation unit does not
 * include `mpmc.h`; it calls the installed library symbols.
 */
#include <stdbool.h>
#include <stdint.h>

typedef struct mpmc_queue mpmc_queue;

extern mpmc_queue *mpmc_create(uint64_t capacity);
extern void mpmc_destroy(mpmc_queue *q);
extern bool mpmc_push(mpmc_queue *q, uint64_t value);
extern bool mpmc_pop(mpmc_queue *q, uint64_t *value);

mpmc_queue *mixed_lib_create(uint64_t capacity) { return mpmc_create(capacity); }

void mixed_lib_destroy(mpmc_queue *q) { mpmc_destroy(q); }

bool mixed_lib_push(mpmc_queue *q, uint64_t value) {
  return mpmc_push(q, value);
}

bool mixed_lib_pop(mpmc_queue *q, uint64_t *value) {
  return mpmc_pop(q, value);
}
