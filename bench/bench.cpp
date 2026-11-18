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

#include <atomic>
#include <chrono>
#include <cinttypes>
#include <cstdio>
#include <cstdlib>
#include <exception>
#include <limits>
#include <memory>
#include <thread>
#include <vector>

namespace {

inline void spin_pause() {
#if defined(__aarch64__)
  asm volatile("yield" ::: "memory");
#elif defined(__x86_64__)
  asm volatile("pause" ::: "memory");
#endif
}

}  // namespace

int main(int argc, char **argv) {
  const std::uint64_t producers = argc > 1 ? std::strtoull(argv[1], nullptr, 10) : 1;
  const std::uint64_t consumers = argc > 2 ? std::strtoull(argv[2], nullptr, 10) : 1;
  const std::uint64_t per_producer =
      argc > 3 ? std::strtoull(argv[3], nullptr, 10) : 5000000;
  const std::uint64_t capacity =
      argc > 4 ? std::strtoull(argv[4], nullptr, 10) : 4096;

  if (producers == 0 || consumers == 0 || per_producer == 0) {
    std::fprintf(stderr, "producers, consumers, and work must be positive\n");
    return 1;
  }
  if (producers > UINT64_MAX / per_producer) {
    std::fprintf(stderr, "work size overflows\n");
    return 1;
  }
  if (producers > UINT64_MAX - consumers) {
    std::fprintf(stderr, "thread count overflows\n");
    return 1;
  }
  if (producers + consumers >
      std::numeric_limits<std::size_t>::max() / sizeof(std::thread)) {
    std::fprintf(stderr, "thread count too large\n");
    return 1;
  }

  std::unique_ptr<mpmc::queue> queue;
  try {
    queue = std::make_unique<mpmc::queue>(capacity);
  } catch (const std::exception &error) {
    std::fprintf(stderr, "create failed: %s\n", error.what());
    return 1;
  }

  const std::uint64_t total = producers * per_producer;
  const std::uint64_t per_consumer = total / consumers;
  const std::uint64_t consumer_remainder = total % consumers;

  std::atomic<bool> start{false};
  std::atomic<std::uint64_t> ready{0};
  std::vector<std::thread> threads;
  std::vector<std::uint64_t> consumer_sums(static_cast<std::size_t>(consumers), 0);
  threads.reserve(static_cast<std::size_t>(producers + consumers));

  for (std::uint64_t p = 0; p < producers; ++p) {
    threads.emplace_back([&, p] {
      ready.fetch_add(1, std::memory_order_release);
      while (!start.load(std::memory_order_acquire)) {
        spin_pause();
      }
      for (std::uint64_t i = 0; i < per_producer; ++i) {
        const std::uint64_t value = p * per_producer + i;
        while (!queue->push(value)) {
          spin_pause();
        }
      }
    });
  }
  for (std::uint64_t c = 0; c < consumers; ++c) {
    const std::uint64_t count = per_consumer + (c < consumer_remainder ? 1 : 0);
    threads.emplace_back([&, c, count] {
      ready.fetch_add(1, std::memory_order_release);
      while (!start.load(std::memory_order_acquire)) {
        spin_pause();
      }
      std::uint64_t value = 0;
      std::uint64_t sum = 0;
      for (std::uint64_t i = 0; i < count; ++i) {
        while (!queue->pop(value)) {
          spin_pause();
        }
        sum += value;
      }
      consumer_sums[static_cast<std::size_t>(c)] = sum;
    });
  }

  while (ready.load(std::memory_order_acquire) != producers + consumers) {
    spin_pause();
  }

  const auto begin = std::chrono::steady_clock::now();
  start.store(true, std::memory_order_release);
  for (auto &t : threads) {
    t.join();
  }
  const auto end = std::chrono::steady_clock::now();
  const double seconds = std::chrono::duration<double>(end - begin).count();

  std::uint64_t observed = 0;
  for (const std::uint64_t sum : consumer_sums) {
    observed += sum;
  }
  const std::uint64_t expected =
      (total % 2 == 0) ? (total / 2) * (total - 1)
                       : total * ((total - 1) / 2);
  if (observed != expected) {
    std::fprintf(stderr, "value check failed: got %" PRIu64 ", expected %" PRIu64 "\n",
                 observed, expected);
    return 1;
  }

  std::printf("%" PRIu64 "P/%" PRIu64 "C cap %" PRIu64 ": %" PRIu64
              " values in %.3f s, %.1f M transfers/s, %.2f ns/transfer\n",
              producers, consumers, capacity, total, seconds,
              static_cast<double>(total) / seconds / 1e6,
              seconds * 1e9 / static_cast<double>(total));

  return 0;
}
