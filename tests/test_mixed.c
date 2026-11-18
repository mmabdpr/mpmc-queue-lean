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
 * Mixed-role concurrency test.
 *
 * Every worker pushes its own range and then drains any remaining values
 * until the global count reaches the total.  Unlike `test_stress`, no thread
 * is permanently a producer or a consumer, and the queue is run at capacity
 * two.  This exercises the "any mix" contract and competing cell CASes.
 */
#ifndef _POSIX_C_SOURCE
#define _POSIX_C_SOURCE 200809L
#endif

#include "mpmc.h"

#include <inttypes.h>
#include <pthread.h>
#include <sched.h>
#include <stdatomic.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

#define MIXED_MAGIC UINT64_C(0x9e3779b97f4a7c15)

typedef struct {
  mpmc_queue *q;
  uint64_t id;
  uint64_t per_thread;
  uint64_t total;
  uint64_t *payload;
  _Atomic uint32_t *counts;
  _Atomic uint64_t *consumed;
} worker_arg;

static void validate(worker_arg *arg, uint64_t value) {
  if (value >= arg->total ||
      arg->payload[value] != (value ^ MIXED_MAGIC)) {
    fprintf(stderr, "mixed: payload publication violation\n");
    abort();
  }
  atomic_fetch_add_explicit(arg->counts + value, 1, memory_order_relaxed);
  const uint64_t done =
      atomic_fetch_add_explicit(arg->consumed, 1, memory_order_acq_rel) + 1;
  if (done > arg->total) {
    fprintf(stderr, "mixed: duplicate consumption\n");
    abort();
  }
}

static void *worker_main(void *opaque) {
  worker_arg *arg = (worker_arg *)opaque;
  uint64_t pushed = 0;

  while (pushed < arg->per_thread) {
    const uint64_t value = arg->id * arg->per_thread + pushed;
    arg->payload[value] = value ^ MIXED_MAGIC;
    if (mpmc_push(arg->q, value)) {
      ++pushed;
      continue;
    }
    uint64_t out = 0;
    if (mpmc_pop(arg->q, &out)) {
      validate(arg, out);
    } else {
      sched_yield();
    }
  }

  while (atomic_load_explicit(arg->consumed, memory_order_acquire) <
         arg->total) {
    uint64_t out = 0;
    if (mpmc_pop(arg->q, &out)) {
      validate(arg, out);
    } else {
      sched_yield();
    }
  }
  return NULL;
}

int main(int argc, char **argv) {
  const uint64_t threads = argc > 1 ? strtoull(argv[1], NULL, 10) : 4;
  const uint64_t per_thread = argc > 2 ? strtoull(argv[2], NULL, 10) : 50000;
  const uint64_t capacity = argc > 3 ? strtoull(argv[3], NULL, 10) : 2;

  if (threads == 0 || per_thread == 0 || capacity < 2) {
    fprintf(stderr, "mixed: invalid arguments\n");
    return 1;
  }
  if (threads > UINT64_MAX / per_thread) {
    fprintf(stderr, "mixed: work size overflows\n");
    return 1;
  }
  if (threads > 64 || threads > SIZE_MAX / sizeof(pthread_t) ||
      threads > SIZE_MAX / sizeof(worker_arg)) {
    fprintf(stderr, "mixed: thread count too large\n");
    return 1;
  }

  const uint64_t total = threads * per_thread;
  if (total > SIZE_MAX / sizeof(uint64_t)) {
    fprintf(stderr, "mixed: work size too large\n");
    return 1;
  }
  mpmc_queue *q = mpmc_create(capacity);
  if (q == NULL) {
    fprintf(stderr, "mixed: create failed\n");
    return 1;
  }

  uint64_t *payload = (uint64_t *)calloc((size_t)total, sizeof(uint64_t));
  _Atomic uint32_t *counts =
      (_Atomic uint32_t *)calloc((size_t)total, sizeof(uint32_t));
  pthread_t *workers = (pthread_t *)calloc((size_t)threads, sizeof(pthread_t));
  worker_arg *args = (worker_arg *)calloc((size_t)threads, sizeof(worker_arg));
  if (payload == NULL || counts == NULL || workers == NULL || args == NULL) {
    fprintf(stderr, "mixed: allocation failed\n");
    free(payload);
    free(counts);
    free(workers);
    free(args);
    mpmc_destroy(q);
    return 1;
  }

  _Atomic uint64_t consumed = 0;
  for (uint64_t i = 0; i < threads; ++i) {
    args[i].q = q;
    args[i].id = i;
    args[i].per_thread = per_thread;
    args[i].total = total;
    args[i].payload = payload;
    args[i].counts = counts;
    args[i].consumed = &consumed;
    if (pthread_create(&workers[i], NULL, worker_main, &args[i]) != 0) {
      fprintf(stderr, "mixed: pthread_create failed\n");
      exit(1);
    }
  }

  for (uint64_t i = 0; i < threads; ++i) {
    pthread_join(workers[i], NULL);
  }

  const uint64_t done = atomic_load_explicit(&consumed, memory_order_acquire);
  uint64_t duplicates = 0;
  uint64_t missing = 0;
  for (uint64_t i = 0; i < total; ++i) {
    const uint32_t count =
        atomic_load_explicit(counts + i, memory_order_relaxed);
    if (count == 0) {
      ++missing;
    } else if (count != 1) {
      duplicates += count - 1;
    }
  }
  printf("mixed: %" PRIu64 " threads, %" PRIu64 " values, cap %" PRIu64
         ", consumed %" PRIu64 ", missing %" PRIu64 ", duplicate %" PRIu64
         "\n",
         threads, total, capacity, done, missing, duplicates);

  free(payload);
  free(counts);
  free(workers);
  free(args);
  mpmc_destroy(q);
  return done == total && missing == 0 && duplicates == 0 ? 0 : 1;
}
