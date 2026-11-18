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
 * C ABI / FFI regression test.
 *
 * This translation unit does not include the public header;
 * it declares the four exported symbols directly and links the static
 * library, exactly as an FFI consumer would.  The header-only API and the
 * library therefore share one ABI and one layout.
 */
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>

typedef struct mpmc_queue mpmc_queue;

extern mpmc_queue *mpmc_create(uint64_t capacity);
extern void mpmc_destroy(mpmc_queue *q);
extern bool mpmc_push(mpmc_queue *q, uint64_t value);
extern bool mpmc_pop(mpmc_queue *q, uint64_t *value);

int main(void) {
  mpmc_queue *q = mpmc_create(4);
  if (q == NULL) {
    fprintf(stderr, "ffi: create failed\n");
    return 1;
  }
  for (uint64_t i = 0; i < 4; ++i) {
    if (!mpmc_push(q, 100 + i)) {
      fprintf(stderr, "ffi: push failed\n");
      mpmc_destroy(q);
      return 1;
    }
  }
  if (mpmc_push(q, 999)) {
    fprintf(stderr, "ffi: full push succeeded\n");
    mpmc_destroy(q);
    return 1;
  }
  for (uint64_t i = 0; i < 4; ++i) {
    uint64_t value = 0;
    if (!mpmc_pop(q, &value) || value != 100 + i) {
      fprintf(stderr, "ffi: pop mismatch\n");
      mpmc_destroy(q);
      return 1;
    }
  }
  {
    uint64_t value = 0;
    if (mpmc_pop(q, &value)) {
      fprintf(stderr, "ffi: empty pop succeeded\n");
      mpmc_destroy(q);
      return 1;
    }
  }
  mpmc_destroy(q);
  puts("ffi: ok");
  return 0;
}
