/*
 * Copyright (c) 2026 Mohammad Mahdi Abdollahpour.
 * The contents of this file are subject to the Common Public Attribution
 * License Version 1.0 (the "License"); you may not use this file except in
 * compliance with the License. You may obtain a copy of the License at
 * https://opensource.org/license/cpal-1-0.
 * The Original Code is mpmc-lean. The Initial Developer is Mohammad Mahdi
 * Abdollahpour. See LICENSE and NOTICE.
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

static void test_basic_fifo(void) {
  mpmc_queue *q = mpmc_create(4);
  CHECK(q != NULL);
  if (q == NULL) {
    return;
  }
  CHECK(mpmc_size_approx_internal(q) == 0);

  for (uint64_t i = 0; i < 4; ++i) {
    CHECK(mpmc_push(q, 100 + i));
  }
  CHECK(!mpmc_push(q, 999));
  CHECK(mpmc_size_approx_internal(q) == 4);

  for (uint64_t i = 0; i < 4; ++i) {
    uint64_t value = 0;
    CHECK(mpmc_pop(q, &value));
    CHECK(value == 100 + i);
  }
  {
    uint64_t value = 77;
    CHECK(!mpmc_pop(q, &value));
    CHECK(value == 77);
  }
  CHECK(mpmc_size_approx_internal(q) == 0);

  CHECK(mpmc_push(q, 7));
  {
    uint64_t value = 0;
    CHECK(mpmc_pop(q, &value));
    CHECK(value == 7);
    CHECK(!mpmc_pop(q, &value));
  }
  CHECK(mpmc_push(q, 0));
  CHECK(mpmc_push(q, UINT64_MAX));
  CHECK(mpmc_push(q, UINT64_C(1) << 63));
  {
    uint64_t value = 1;
    CHECK(mpmc_pop(q, &value));
    CHECK(value == 0);
    CHECK(mpmc_pop(q, &value));
    CHECK(value == UINT64_MAX);
    CHECK(mpmc_pop(q, &value));
    CHECK(value == (UINT64_C(1) << 63));
  }

  mpmc_destroy(q);
}

static void test_wraparound(void) {
  mpmc_queue *q = mpmc_create(8);
  CHECK(q != NULL);
  if (q == NULL) {
    return;
  }
  for (uint64_t round = 0; round < 1000; ++round) {
    for (uint64_t i = 0; i < 8; ++i) {
      CHECK(mpmc_push(q, round * 8 + i));
    }
    CHECK(!mpmc_push(q, 0));
    for (uint64_t i = 0; i < 8; ++i) {
      uint64_t value = 0;
      CHECK(mpmc_pop(q, &value));
      CHECK(value == round * 8 + i);
    }
    {
      uint64_t value = 0;
      CHECK(!mpmc_pop(q, &value));
    }
  }
  mpmc_destroy(q);
}

static void test_exhaustion(void) {
  mpmc_queue *q = mpmc_new(8, 6);
  CHECK(q != NULL);
  if (q == NULL) {
    return;
  }
  for (uint64_t i = 0; i < 6; ++i) {
    CHECK(mpmc_push(q, i));
  }
  CHECK(!mpmc_push(q, 6));

  for (uint64_t i = 0; i < 6; ++i) {
    uint64_t value = 0;
    CHECK(mpmc_pop(q, &value));
    CHECK(value == i);
  }
  {
    uint64_t value = 0;
    CHECK(!mpmc_pop(q, &value));
  }
  mpmc_destroy(q);
}

static void test_min_capacity(void) {
  mpmc_queue *q = mpmc_create(2);
  CHECK(q != NULL);
  if (q == NULL) {
    return;
  }
  CHECK(mpmc_push(q, 1));
  CHECK(mpmc_push(q, 2));
  CHECK(!mpmc_push(q, 3));
  {
    uint64_t value = 0;
    CHECK(mpmc_pop(q, &value));
    CHECK(value == 1);
    CHECK(mpmc_pop(q, &value));
    CHECK(value == 2);
    CHECK(!mpmc_pop(q, &value));
  }
  mpmc_destroy(q);
}

static void test_mixed_calls(void) {
  mpmc_queue *q = mpmc_create(4);
  CHECK(q != NULL);
  if (q == NULL) {
    return;
  }
  uint64_t value = 0;
  CHECK(mpmc_push(q, 1));
  CHECK(mpmc_pop(q, &value) && value == 1);
  CHECK(mpmc_push(q, 2));
  CHECK(mpmc_push(q, 3));
  CHECK(mpmc_pop(q, &value) && value == 2);
  CHECK(mpmc_push(q, 4));
  CHECK(mpmc_pop(q, &value) && value == 3);
  CHECK(mpmc_pop(q, &value) && value == 4);
  CHECK(!mpmc_pop(q, &value));
  mpmc_destroy(q);
}

static void test_helping(void) {
  mpmc_queue *q = mpmc_create(4);
  CHECK(q != NULL);
  if (q == NULL) {
    return;
  }
  CHECK(mpmc_push(q, 10)); /* write_index = 1 */
  __atomic_store_n(&q->write_index, 0, __ATOMIC_RELAXED); /* stale hint */
  CHECK(mpmc_push(q, 11)); /* the helper advances 0 -> 1, then pushes at 1 */
  {
    uint64_t value = 0;
    CHECK(mpmc_pop(q, &value));
    CHECK(value == 10); /* read_index = 1, cell 0 reset */
  }
  __atomic_store_n(&q->read_index, 0, __ATOMIC_RELAXED); /* stale hint */
  {
    uint64_t value = 0;
    CHECK(mpmc_pop(q, &value)); /* the helper advances 0 -> 1 */
    CHECK(value == 11);
  }
  /* Move the write hint back by one full ring: slot 1 now carries position
   * 5, which is ahead of hint 1.  This forces the marker-ahead help path. */
  __atomic_store_n(&q->write_index, 1, __ATOMIC_RELAXED);
  CHECK(mpmc_push(q, 12));
  {
    uint64_t value = 0;
    CHECK(mpmc_pop(q, &value));
    CHECK(value == 12);
  }
  mpmc_destroy(q);
}

static void test_horizon(void) {
  const uint64_t limit = (UINT64_C(1) << 63) - 2;
  mpmc_queue *q = mpmc_new(2, limit);
  CHECK(q != NULL);
  if (q == NULL) {
    return;
  }
  const uint64_t w = limit - 1; /* highest publishable position */
  mpmc_cell cell = {w << 1, 0};
  __atomic_store(&mpmc_slots(q)[w & q->mask].value, &cell, __ATOMIC_RELAXED);
  __atomic_store_n(&q->write_index, w, __ATOMIC_RELAXED);
  CHECK(mpmc_push(q, 123));  /* marker 2*w+1 must not overflow */
  CHECK(!mpmc_push(q, 124)); /* horizon reached */
  __atomic_store_n(&q->read_index, w, __ATOMIC_RELAXED);
  {
    uint64_t value = 0;
    CHECK(mpmc_pop(q, &value));
    CHECK(value == 123); /* reset marker 2*(w+C) must not overflow */
  }
  mpmc_destroy(q);
}

static void test_abi_validation(void) {
  mpmc_queue *q = mpmc_create(2);
  CHECK(q != NULL && mpmc_valid(q));
  if (q == NULL) {
    return;
  }
  q->version = 0;
  CHECK(!mpmc_valid(q));
  q->version = MPMC_VERSION;
  q->abi_tag = 0;
  CHECK(!mpmc_valid(q));
  q->abi_tag = MPMC_ABI_TAG;
  CHECK(mpmc_valid(q));
  mpmc_destroy(q);
}

static void test_invalid(void) {
  CHECK(mpmc_create(0) == NULL);
  CHECK(mpmc_create(1) == NULL);
  CHECK(mpmc_create(3) == NULL);
  CHECK(mpmc_create(6) == NULL);
  CHECK(mpmc_create(UINT64_C(1) << 25) == NULL);
  CHECK(mpmc_create(UINT64_MAX) == NULL);
  CHECK(mpmc_new(4, 0) == NULL);
  CHECK(mpmc_new(4, UINT64_C(1) << 63) == NULL);
  CHECK(!mpmc_push(NULL, 1));
  {
    uint64_t value = 123;
    CHECK(!mpmc_pop(NULL, &value));
    CHECK(value == 123);
  }
  {
    mpmc_queue *q = mpmc_create(4);
    CHECK(q != NULL);
    if (q != NULL) {
      CHECK(!mpmc_pop(q, NULL));
      mpmc_destroy(q);
    }
  }
  mpmc_destroy(NULL);
}

int main(void) {
  test_basic_fifo();
  test_min_capacity();
  test_mixed_calls();
  test_helping();
  test_horizon();
  test_abi_validation();
  test_wraparound();
  test_exhaustion();
  test_invalid();
  if (failures != 0) {
    fprintf(stderr, "%d failure(s)\n", failures);
    return 1;
  }
  puts("basic: ok");
  return 0;
}
