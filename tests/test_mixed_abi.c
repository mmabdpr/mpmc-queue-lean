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
 * Cross-boundary ABI test: create a queue through one implementation path and
 * operate on it through the other.  The header-only and out-of-line paths
 * must agree on the opaque layout and on the four exported symbols.
 */
#include "mpmc.h"

#include <stdint.h>
#include <stdio.h>

extern mpmc_queue *mixed_lib_create(uint64_t capacity);
extern void mixed_lib_destroy(mpmc_queue *q);
extern bool mixed_lib_push(mpmc_queue *q, uint64_t value);
extern bool mixed_lib_pop(mpmc_queue *q, uint64_t *value);
extern int mixed_inline_roundtrip(mpmc_queue *q, uint64_t base, uint64_t count);

int main(void) {
  /* Header-created storage, library operations, library destruction. */
  mpmc_queue *q = mpmc_create(8);
  if (q == NULL) {
    fputs("mixed_abi: header create failed\n", stderr);
    return 1;
  }
  if (!mixed_lib_push(q, 41)) {
    fputs("mixed_abi: library push on header handle failed\n", stderr);
    mixed_lib_destroy(q);
    return 2;
  }
  {
    uint64_t value = 0;
    if (!mixed_lib_pop(q, &value) || value != 41) {
      fputs("mixed_abi: library pop on header handle failed\n", stderr);
      mixed_lib_destroy(q);
      return 3;
    }
  }
  mixed_lib_destroy(q);

  /* Library-created storage, header-only operations, library destruction. */
  q = mixed_lib_create(8);
  if (q == NULL) {
    fputs("mixed_abi: library create failed\n", stderr);
    return 4;
  }
  if (mixed_inline_roundtrip(q, 100, 4) != 0) {
    fputs("mixed_abi: header operation on library handle failed\n", stderr);
    mixed_lib_destroy(q);
    return 5;
  }
  mixed_lib_destroy(q);

  puts("mixed_abi: ok");
  return 0;
}
