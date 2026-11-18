/*
 * Copyright (c) 2026 Mohammad Mahdi Abdollahpour.
 * The contents of this file are subject to the Common Public Attribution
 * License Version 1.0 (the "License"); you may not use this file except in
 * compliance with the License. You may obtain a copy of the License at
 * https://opensource.org/license/cpal-1-0.
 * The Original Code is mpmc-lean. The Initial Developer is Mohammad Mahdi
 * Abdollahpour. See LICENSE and NOTICE.
 */

/* Installed out-of-line ABI smoke test: no mpmc.h, just the exported symbols
 * from the installed library, as an FFI/dynamic-loader consumer would use. */
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>

typedef struct mpmc_queue mpmc_queue;

extern mpmc_queue *mpmc_create(uint64_t capacity);
extern void mpmc_destroy(mpmc_queue *q);
extern bool mpmc_push(mpmc_queue *q, uint64_t value);
extern bool mpmc_pop(mpmc_queue *q, uint64_t *value);

int main(void) {
  mpmc_queue *q = mpmc_create(8);
  if (q == NULL) {
    fputs("consumer-ffi: create failed\n", stderr);
    return 1;
  }
  for (uint64_t i = 0; i < 8; ++i) {
    if (!mpmc_push(q, i)) {
      fputs("consumer-ffi: push failed\n", stderr);
      mpmc_destroy(q);
      return 2;
    }
  }
  for (uint64_t i = 0; i < 8; ++i) {
    uint64_t value = 0;
    if (!mpmc_pop(q, &value) || value != i) {
      fputs("consumer-ffi: pop mismatch\n", stderr);
      mpmc_destroy(q);
      return 3;
    }
  }
  mpmc_destroy(q);
  puts("consumer-ffi: ok");
  return 0;
}
