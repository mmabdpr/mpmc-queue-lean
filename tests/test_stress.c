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

#include <inttypes.h>
#include <pthread.h>
#include <sched.h>
#include <stdatomic.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>

#ifdef MPMC_TEST_USE_LIBRARY
typedef struct mpmc_queue mpmc_queue;
extern mpmc_queue *mpmc_create(uint64_t capacity);
extern void mpmc_destroy(mpmc_queue *q);
extern bool mpmc_push(mpmc_queue *q, uint64_t value);
extern bool mpmc_pop(mpmc_queue *q, uint64_t *value);
#else
#include "mpmc.h"
#endif

typedef struct {
  mpmc_queue *q;
  uint64_t first;
  uint64_t per_producer;
  uint64_t *payload;
} producer_arg;

typedef struct {
  mpmc_queue *q;
  _Atomic uint32_t *counts;
  _Atomic uint64_t *consumed;
  uint64_t total;
  uint64_t producers;
  uint64_t consumers;
  uint64_t per_producer;
  uint64_t expected;
  uint64_t *payload;
  uint64_t *last; /* per-consumer last value seen for each producer */
} consumer_arg;

static void *producer_main(void *opaque) {
  producer_arg *arg = (producer_arg *)opaque;
  for (uint64_t i = 0; i < arg->per_producer; ++i) {
    const uint64_t value = arg->first + i;
    arg->payload[value] = value ^ UINT64_C(0x9e3779b97f4a7c15);
    while (!mpmc_push(arg->q, value)) {
      sched_yield();
    }
  }
  return NULL;
}

static void *consumer_main(void *opaque) {
  consumer_arg *arg = (consumer_arg *)opaque;
  for (;;) {
    uint64_t value = 0;
    if (mpmc_pop(arg->q, &value)) {
      if (value >= arg->total) {
        fprintf(stderr, "consumer: value out of range\n");
        abort();
      }
      if (arg->payload[value] !=
          (value ^ UINT64_C(0x9e3779b97f4a7c15))) {
        fprintf(stderr, "consumer: payload publication violation\n");
        abort();
      }
      {
        const uint64_t producer = value / arg->per_producer;
        if (producer >= arg->producers ||
            (arg->last[producer] != UINT64_MAX &&
             value <= arg->last[producer])) {
          fprintf(stderr, "consumer: per-producer order violation\n");
          abort();
        }
        arg->last[producer] = value;
      }
      if (arg->producers == 1 && arg->consumers == 1) {
        if (value != arg->expected) {
          fprintf(stderr, "consumer: FIFO violation: got %" PRIu64
                          ", expected %" PRIu64 "\n",
                  value, arg->expected);
          abort();
        }
        ++arg->expected;
      }
      atomic_fetch_add_explicit(&arg->counts[value], 1, memory_order_relaxed);
      const uint64_t done =
          atomic_fetch_add_explicit(arg->consumed, 1, memory_order_acq_rel) + 1;
      if (done == arg->total) {
        return NULL;
      }
    } else if (atomic_load_explicit(arg->consumed, memory_order_acquire) >=
               arg->total) {
      return NULL;
    } else {
      sched_yield();
    }
  }
}

static double now_seconds(void) {
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return (double)ts.tv_sec + (double)ts.tv_nsec * 1e-9;
}

int main(int argc, char **argv) {
  const uint64_t producers = argc > 1 ? strtoull(argv[1], NULL, 10) : 2;
  const uint64_t consumers = argc > 2 ? strtoull(argv[2], NULL, 10) : 2;
  const uint64_t per_producer = argc > 3 ? strtoull(argv[3], NULL, 10) : 250000;
  const uint64_t capacity = argc > 4 ? strtoull(argv[4], NULL, 10) : 1024;

  if (producers == 0 || consumers == 0 || per_producer == 0) {
    fprintf(stderr, "stress: producers, consumers, and work must be positive\n");
    return 1;
  }
  if (producers > UINT64_MAX / per_producer) {
    fprintf(stderr, "stress: work size overflows\n");
    return 1;
  }
  if (producers > SIZE_MAX / sizeof(pthread_t) ||
      consumers > SIZE_MAX / sizeof(pthread_t) ||
      producers > SIZE_MAX / sizeof(producer_arg) ||
      consumers > SIZE_MAX / sizeof(consumer_arg) ||
      (consumers != 0 &&
       producers > SIZE_MAX / consumers / sizeof(uint64_t))) {
    fprintf(stderr, "stress: thread count too large\n");
    return 1;
  }
  const uint64_t total = producers * per_producer;
  if (total > (UINT64_C(1) << 32)) {
    fprintf(stderr, "stress: total too large\n");
    return 1;
  }

  mpmc_queue *q = mpmc_create(capacity);
  if (q == NULL) {
    fprintf(stderr, "stress: create failed\n");
    return 1;
  }

  _Atomic uint32_t *counts =
      (_Atomic uint32_t *)calloc((size_t)total, sizeof(uint32_t));
  if (counts == NULL) {
    fprintf(stderr, "stress: allocation failed\n");
    mpmc_destroy(q);
    return 1;
  }

  _Atomic uint64_t consumed = 0;
  uint64_t *payload =
      (uint64_t *)calloc((size_t)total, sizeof(uint64_t));
  if (payload == NULL) {
    fprintf(stderr, "stress: payload allocation failed\n");
    free(counts);
    mpmc_destroy(q);
    return 1;
  }
  const size_t last_count = (size_t)(consumers * producers);
  uint64_t *last = (uint64_t *)malloc(last_count * sizeof(uint64_t));
  if (last == NULL) {
    fprintf(stderr, "stress: last-value allocation failed\n");
    free(payload);
    free(counts);
    mpmc_destroy(q);
    return 1;
  }
  for (size_t i = 0; i < last_count; ++i) {
    last[i] = UINT64_MAX;
  }
  pthread_t *prod = (pthread_t *)calloc((size_t)producers, sizeof(pthread_t));
  pthread_t *cons = (pthread_t *)calloc((size_t)consumers, sizeof(pthread_t));
  producer_arg *pargs =
      (producer_arg *)calloc((size_t)producers, sizeof(producer_arg));
  consumer_arg *cargs =
      (consumer_arg *)calloc((size_t)consumers, sizeof(consumer_arg));
  if (prod == NULL || cons == NULL || pargs == NULL || cargs == NULL) {
    fprintf(stderr, "stress: thread allocation failed\n");
    free(prod);
    free(cons);
    free(pargs);
    free(cargs);
    free(counts);
    free(payload);
    free(last);
    mpmc_destroy(q);
    return 1;
  }

  for (uint64_t p = 0; p < producers; ++p) {
    pargs[p].q = q;
    pargs[p].first = p * per_producer;
    pargs[p].per_producer = per_producer;
    pargs[p].payload = payload;
    if (pthread_create(&prod[p], NULL, producer_main, &pargs[p]) != 0) {
      fprintf(stderr, "stress: pthread_create failed\n");
      exit(1);
    }
  }
  for (uint64_t c = 0; c < consumers; ++c) {
    cargs[c].q = q;
    cargs[c].counts = counts;
    cargs[c].consumed = &consumed;
    cargs[c].total = total;
    cargs[c].producers = producers;
    cargs[c].consumers = consumers;
    cargs[c].per_producer = per_producer;
    cargs[c].expected = 0;
    cargs[c].payload = payload;
    cargs[c].last = last + (size_t)(c * producers);
    if (pthread_create(&cons[c], NULL, consumer_main, &cargs[c]) != 0) {
      fprintf(stderr, "stress: pthread_create failed\n");
      exit(1);
    }
  }

  const double start = now_seconds();
  for (uint64_t p = 0; p < producers; ++p) {
    pthread_join(prod[p], NULL);
  }
  for (uint64_t c = 0; c < consumers; ++c) {
    pthread_join(cons[c], NULL);
  }
  const double elapsed = now_seconds() - start;

  uint64_t duplicates = 0;
  uint64_t missing = 0;
  for (uint64_t i = 0; i < total; ++i) {
    const uint32_t count =
        atomic_load_explicit(&counts[i], memory_order_relaxed);
    if (count == 0) {
      ++missing;
    } else if (count != 1) {
      duplicates += count - 1;
    }
  }

  const double rate = (double)total / elapsed / 1e6;
  printf("stress: %" PRIu64 "P/%" PRIu64 "C, %" PRIu64
         " values, cap %" PRIu64 ", %.3f s, %.1f Mops/s, missing %" PRIu64
         ", duplicate %" PRIu64 "\n",
         producers, consumers, total, capacity, elapsed, rate, missing,
         duplicates);

  free(pargs);
  free(cargs);
  free(prod);
  free(cons);
  free(counts);
  free(payload);
  free(last);
  mpmc_destroy(q);
  return (missing == 0 && duplicates == 0) ? 0 : 1;
}
