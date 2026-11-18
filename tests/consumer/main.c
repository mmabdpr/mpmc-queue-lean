/*
 * Copyright (c) 2026 Mohammad Mahdi Abdollahpour.
 * The contents of this file are subject to the Common Public Attribution
 * License Version 1.0 (the "License"); you may not use this file except in
 * compliance with the License. You may obtain a copy of the License at
 * https://opensource.org/license/cpal-1-0.
 * The Original Code is mpmc-lean. The Initial Developer is Mohammad Mahdi
 * Abdollahpour. See LICENSE and NOTICE.
 */
/* Installed-package smoke test: this translation unit only sees the
 * installed `mpmc.h` and links `mpmc::mpmc` from the installed CMake package. */
#include <mpmc.h>

#include <stdint.h>
#include <stdio.h>

int main(void) {
  mpmc_queue *q = mpmc_create(8);
  if (q == NULL) {
    fputs("consumer: create failed\n", stderr);
    return 1;
  }
  for (uint64_t i = 0; i < 8; ++i) {
    if (!mpmc_push(q, i)) {
      fputs("consumer: push failed\n", stderr);
      mpmc_destroy(q);
      return 2;
    }
  }
  for (uint64_t i = 0; i < 8; ++i) {
    uint64_t value = 0;
    if (!mpmc_pop(q, &value) || value != i) {
      fputs("consumer: pop mismatch\n", stderr);
      mpmc_destroy(q);
      return 3;
    }
  }
  mpmc_destroy(q);
  puts("consumer: ok");
  return 0;
}
