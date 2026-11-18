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
 * Header-only regression test.
 *
 * This test includes only the public header and never links the static
 * library; it proves that the four public functions are self-contained.
 */
#include "mpmc.h"

#include <stdio.h>

static int failures = 0;

#define CHECK(cond)                                                          \
  do {                                                                       \
    if (!(cond)) {                                                           \
      fprintf(stderr, "FAIL %s:%d: %s\n", __FILE__, __LINE__, #cond);        \
      ++failures;                                                            \
    }                                                                        \
  } while (0)

int main(void) {
  mpmc_queue *q = mpmc_create(4);
  CHECK(q != NULL);
  if (q == NULL) {
    return 1;
  }

  CHECK(mpmc_push(q, 11));
  CHECK(mpmc_push(q, 22));
  CHECK(mpmc_size_approx_internal(q) == 2);

  uint64_t value = 0;
  CHECK(mpmc_pop(q, &value));
  CHECK(value == 11);
  CHECK(mpmc_pop(q, &value));
  CHECK(value == 22);
  CHECK(!mpmc_pop(q, &value));

  for (uint64_t i = 0; i < 4; ++i) {
    CHECK(mpmc_push(q, 100 + i));
  }
  CHECK(!mpmc_push(q, 999));

  mpmc_destroy(q);
  printf("header_only: %s\n", failures == 0 ? "ok" : "failed");
  return failures == 0 ? 0 : 1;
}
