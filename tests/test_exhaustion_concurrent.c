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
 * Concurrent exhaustion test.  Several threads race to publish into a queue
 * whose horizon is small enough to reach; exactly `limit` pushes may succeed,
 * and every successful value must be drained exactly once.
 */
#ifndef _POSIX_C_SOURCE
#define _POSIX_C_SOURCE 200809L
#endif

#include "mpmc.h"

#include <pthread.h>
#include <sched.h>
#include <stdatomic.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

#define THREADS 4
#define PER_THREAD 100
#define LIMIT 200

typedef struct {
  mpmc_queue *q;
  _Atomic uint32_t *counts;
  _Atomic uint64_t *successes;
  uint64_t base;
} push_arg;

static void *push_main(void *opaque) {
  push_arg *arg = (push_arg *)opaque;
  uint64_t i = 0;
  while (i < PER_THREAD) {
    const uint64_t value = arg->base + i;
    uint64_t sequence = 0;
    const uint64_t status = mpmc_kernel_push(
        arg->q, arg->q->capacity, arg->q->mask, arg->q->limit, value,
        &sequence);
    if (status == MPMC_KERNEL_EXHAUSTED) {
      return NULL;
    }
    if (status == MPMC_KERNEL_OK) {
      atomic_fetch_add_explicit(arg->counts + value, 1, memory_order_relaxed);
      atomic_fetch_add_explicit(arg->successes, 1, memory_order_acq_rel);
      ++i;
    } else {
      sched_yield(); /* FULL */
    }
  }
  return NULL;
}

int main(void) {
  /* Capacity exceeds LIMIT so pushes are never blocked by FULL; the only
   * stopping condition is the horizon. */
  mpmc_queue *q = mpmc_new(256, LIMIT);
  if (q == NULL) {
    fputs("exhaustion: create failed\n", stderr);
    return 1;
  }
  const uint64_t total_attempts = (uint64_t)THREADS * PER_THREAD;
  _Atomic uint32_t *counts =
      (_Atomic uint32_t *)calloc((size_t)total_attempts, sizeof(uint32_t));
  if (counts == NULL) {
    fputs("exhaustion: allocation failed\n", stderr);
    mpmc_destroy(q);
    return 1;
  }
  _Atomic uint64_t successes = 0;
  pthread_t threads[THREADS];
  push_arg args[THREADS];
  for (uint64_t i = 0; i < THREADS; ++i) {
    args[i].q = q;
    args[i].counts = counts;
    args[i].successes = &successes;
    args[i].base = i * PER_THREAD;
    if (pthread_create(&threads[i], NULL, push_main, &args[i]) != 0) {
      fputs("exhaustion: pthread_create failed\n", stderr);
      exit(1);
    }
  }
  for (uint64_t i = 0; i < THREADS; ++i) {
    pthread_join(threads[i], NULL);
  }

  const uint64_t published =
      atomic_load_explicit(&successes, memory_order_acquire);
  if (published != LIMIT) {
    fprintf(stderr, "exhaustion: published %llu, expected %d\n",
            (unsigned long long)published, LIMIT);
    free(counts);
    mpmc_destroy(q);
    return 1;
  }

  uint64_t popped = 0;
  for (;;) {
    uint64_t value = 0;
    if (!mpmc_pop(q, &value)) {
      break;
    }
    if (value >= total_attempts ||
        atomic_load_explicit(counts + value, memory_order_relaxed) != 1) {
      fprintf(stderr, "exhaustion: bad drained value\n");
      free(counts);
      mpmc_destroy(q);
      return 1;
    }
    ++popped;
  }
  printf("exhaustion: %llu published, %llu drained\n",
         (unsigned long long)published, (unsigned long long)popped);
  free(counts);
  mpmc_destroy(q);
  return popped == LIMIT ? 0 : 1;
}
