/*
 * Copyright (c) 2026 Mohammad Mahdi Abdollahpour.
 * The contents of this file are subject to the Common Public Attribution
 * License Version 1.0 (the "License"); you may not use this file except in
 * compliance with the License. You may obtain a copy of the License at
 * https://opensource.org/license/cpal-1-0.
 * The Original Code is mpmc-lean. The Initial Developer is Mohammad Mahdi
 * Abdollahpour. See LICENSE and NOTICE.
 */
#ifndef _POSIX_C_SOURCE
#define _POSIX_C_SOURCE 200809L
#endif

/*
 * C header-only benchmark.
 *
 * `mpmc.h` is self-contained: the four public functions are `static inline`
 * and include the generated kernel, so this benchmark is the non-LTO
 * deployment path.
 */
#include "mpmc.h"

#include <inttypes.h>
#include <limits.h>
#include <pthread.h>
#include <stdatomic.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>

typedef struct worker {
  mpmc_queue *q;
  uint64_t count;
  uint64_t base;
  atomic_int *ready;
  atomic_bool *start;
  int is_producer;
} worker;

static inline void spin_pause(void) {
#if defined(__aarch64__)
  __asm__ volatile("yield" ::: "memory");
#elif defined(__x86_64__)
  __asm__ volatile("pause" ::: "memory");
#endif
}

static void *run_worker(void *arg) {
  worker *w = (worker *)arg;
  atomic_fetch_add_explicit(w->ready, 1, memory_order_release);
  while (!atomic_load_explicit(w->start, memory_order_acquire)) {
    spin_pause();
  }

  if (w->is_producer) {
    for (uint64_t i = 0; i < w->count; ++i) {
      while (!mpmc_push(w->q, w->base + i)) {
        spin_pause();
      }
    }
  } else {
    uint64_t value = 0;
    for (uint64_t i = 0; i < w->count; ++i) {
      while (!mpmc_pop(w->q, &value)) {
        spin_pause();
      }
    }
  }
  return NULL;
}

static double now_seconds(void) {
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return (double)ts.tv_sec + (double)ts.tv_nsec / 1e9;
}

int main(int argc, char **argv) {
  const uint64_t producers = argc > 1 ? strtoull(argv[1], NULL, 10) : 1;
  const uint64_t consumers = argc > 2 ? strtoull(argv[2], NULL, 10) : 1;
  const uint64_t per_producer = argc > 3 ? strtoull(argv[3], NULL, 10) : 5000000;
  const uint64_t capacity = argc > 4 ? strtoull(argv[4], NULL, 10) : 4096;

  if (producers == 0 || consumers == 0 || per_producer == 0) {
    fprintf(stderr, "producers, consumers, and work must be positive\n");
    return 1;
  }
  if (producers > UINT64_MAX / per_producer) {
    fprintf(stderr, "work size overflows\n");
    return 1;
  }
  if (producers > UINT64_MAX - consumers) {
    fprintf(stderr, "thread count overflows\n");
    return 1;
  }
  const uint64_t thread_count = producers + consumers;
  if (thread_count > (uint64_t)INT_MAX ||
      thread_count > SIZE_MAX / sizeof(pthread_t) ||
      thread_count > SIZE_MAX / sizeof(worker)) {
    fprintf(stderr, "thread count too large\n");
    return 1;
  }

  mpmc_queue *q = mpmc_create(capacity);
  if (q == NULL) {
    fprintf(stderr, "create failed\n");
    return 1;
  }

  const uint64_t total = producers * per_producer;
  const uint64_t per_consumer = total / consumers;
  const uint64_t remainder = total % consumers;

  atomic_int ready = 0;
  atomic_bool start = false;
  pthread_t *threads =
      (pthread_t *)calloc((size_t)thread_count, sizeof(pthread_t));
  worker *args = (worker *)calloc((size_t)thread_count, sizeof(worker));
  if (threads == NULL || args == NULL) {
    fprintf(stderr, "allocation failed\n");
    free(threads);
    free(args);
    mpmc_destroy(q);
    return 1;
  }

  uint64_t n = 0;
  for (uint64_t p = 0; p < producers; ++p) {
    args[n].q = q;
    args[n].count = per_producer;
    args[n].base = p * per_producer;
    args[n].ready = &ready;
    args[n].start = &start;
    args[n].is_producer = 1;
    if (pthread_create(&threads[n], NULL, run_worker, &args[n]) != 0) {
      fprintf(stderr, "pthread_create failed\n");
      exit(1);
    }
    ++n;
  }
  for (uint64_t c = 0; c < consumers; ++c) {
    args[n].q = q;
    args[n].count = per_consumer + (c < remainder ? 1 : 0);
    args[n].base = 0;
    args[n].ready = &ready;
    args[n].start = &start;
    args[n].is_producer = 0;
    if (pthread_create(&threads[n], NULL, run_worker, &args[n]) != 0) {
      fprintf(stderr, "pthread_create failed\n");
      exit(1);
    }
    ++n;
  }

  while (atomic_load_explicit(&ready, memory_order_acquire) !=
         (int)thread_count) {
    spin_pause();
  }

  const double begin = now_seconds();
  atomic_store_explicit(&start, true, memory_order_release);
  for (uint64_t i = 0; i < n; ++i) {
    pthread_join(threads[i], NULL);
  }
  const double seconds = now_seconds() - begin;

  printf("%" PRIu64 "P/%" PRIu64 "C cap %" PRIu64 ": %" PRIu64
         " values in %.3f s, %.1f M transfers/s, %.2f ns/transfer\n",
         producers, consumers, capacity, total, seconds,
         (double)total / seconds / 1e6, seconds * 1e9 / (double)total);

  free(threads);
  free(args);
  mpmc_destroy(q);
  return 0;
}
