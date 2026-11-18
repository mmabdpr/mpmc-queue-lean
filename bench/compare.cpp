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
 * Same-shape throughput comparison against the C++ reference queue.
 *
 * Build with:
 *   cmake -S . -B build-compare \
 *     -DMPMC_ENABLE_LTO=OFF \
 *     -DMPMC_REFERENCE_INCLUDE_DIR=/path/to/mpmc-queue/include
 *   cmake --build build-compare --target mpmc_compare
 *   ./build-compare/mpmc_compare 5 2000000
 *   ./build-compare/mpmc_compare 20 1000000 1 1   # one topology
 *
 * Reference: https://github.com/mmabdpr/mpmc-queue at commit
 * 0b980ff60ee9164252b3e4ff5a0c5f03a048ef84.
 *
 * Both queues run the same producer/consumer topology, the same value
 * sequence, and the same start barrier.  The numbers are medians of
 * `rounds` runs.  This is a parity check, not the calibrated comparison
 * profile of the C++ repository.
 */
#include "mpmc.h"

#include <mpmc/mpmc_queue.hpp>

#include <algorithm>
#include <atomic>
#include <chrono>
#include <climits>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <memory>
#include <thread>
#include <utility>
#include <vector>

namespace {

using u64 = std::uint64_t;
using clock_type = std::chrono::steady_clock;

inline void spin_pause() {
#if defined(__aarch64__)
  asm volatile("yield" ::: "memory");
#elif defined(__x86_64__)
  asm volatile("pause" ::: "memory");
#endif
}

struct ours {
  explicit ours(std::size_t capacity) : q(capacity) {}
  bool push(u64 v) { return q.push(v); }
  bool pop(u64 &v) { return q.pop(v); }
  mpmc::queue q;
};

struct reference {
  explicit reference(std::size_t) : q(std::make_unique<Q>()) {}
  bool push(u64 v) { return q->try_push(v); }
  bool pop(u64 &v) { return q->try_pop(v); }
  using Q = mpmc::mpmc_queue<u64, 4096, std::uint32_t>;
  std::unique_ptr<Q> q;
};

template <class Q>
double run_once(int producers, int consumers, u64 per_producer) {
  if (producers <= 0 || consumers <= 0 ||
      per_producer > UINT64_MAX / static_cast<u64>(producers) ||
      producers > INT_MAX - consumers) {
    std::fprintf(stderr, "invalid topology or work size\n");
    std::exit(1);
  }
  Q q(4096);
  const u64 total = per_producer * static_cast<u64>(producers);
  const u64 per_consumer = total / static_cast<u64>(consumers);
  const u64 remainder = total % static_cast<u64>(consumers);

  std::atomic<bool> start{false};
  std::atomic<u64> ready{0};
  std::vector<std::thread> threads;
  threads.reserve(producers + consumers);

  for (int p = 0; p < producers; ++p) {
    threads.emplace_back([&, p] {
      ready.fetch_add(1, std::memory_order_release);
      while (!start.load(std::memory_order_acquire)) spin_pause();
      for (u64 i = 0; i < per_producer; ++i) {
        const u64 value = static_cast<u64>(p) * per_producer + i;
        while (!q.push(value)) spin_pause();
      }
    });
  }
  for (int c = 0; c < consumers; ++c) {
    const u64 count = per_consumer + (c < static_cast<int>(remainder) ? 1 : 0);
    threads.emplace_back([&, count] {
      ready.fetch_add(1, std::memory_order_release);
      while (!start.load(std::memory_order_acquire)) spin_pause();
      u64 value = 0;
      for (u64 i = 0; i < count; ++i) {
        while (!q.pop(value)) spin_pause();
      }
    });
  }

  while (ready.load(std::memory_order_acquire) !=
         static_cast<u64>(producers + consumers)) {
    spin_pause();
  }
  const auto begin = clock_type::now();
  start.store(true, std::memory_order_release);
  for (auto &t : threads) t.join();
  const auto end = clock_type::now();
  const double seconds = std::chrono::duration<double>(end - begin).count();
  return static_cast<double>(total) / seconds / 1e6;
}

template <class A, class B>
void compare_pair(int producers, int consumers, u64 per_producer, int rounds,
                  double &a_rate, double &b_rate, bool print_rounds = false) {
  std::vector<double> a_rates;
  std::vector<double> b_rates;
  a_rates.reserve(static_cast<std::size_t>(rounds));
  b_rates.reserve(static_cast<std::size_t>(rounds));
  for (int r = 0; r < rounds; ++r) {
    // Alternate which queue runs first so slow drift in host load affects
    // both sides roughly equally.
    double a = 0.0;
    double b = 0.0;
    if ((r & 1) == 0) {
      a = run_once<A>(producers, consumers, per_producer);
      b = run_once<B>(producers, consumers, per_producer);
    } else {
      b = run_once<B>(producers, consumers, per_producer);
      a = run_once<A>(producers, consumers, per_producer);
    }
    if (print_rounds) {
      std::printf("  round %2d: ours %7.1f  reference %7.1f\n", r, a, b);
    }
    a_rates.push_back(a);
    b_rates.push_back(b);
  }
  std::sort(a_rates.begin(), a_rates.end());
  std::sort(b_rates.begin(), b_rates.end());
  a_rate = a_rates[a_rates.size() / 2];
  b_rate = b_rates[b_rates.size() / 2];
  if (print_rounds) {
    std::printf("  ours min/med/max %.1f / %.1f / %.1f\n",
                a_rates.front(), a_rate, a_rates.back());
    std::printf("  ref  min/med/max %.1f / %.1f / %.1f\n",
                b_rates.front(), b_rate, b_rates.back());
  }
}

}  // namespace

int main(int argc, char **argv) {
  const int rounds = argc > 1 ? std::atoi(argv[1]) : 5;
  const u64 per = argc > 2 ? std::strtoull(argv[2], nullptr, 10) : 2000000;
  const int only_p = argc > 3 ? std::atoi(argv[3]) : 0;
  const int only_c = argc > 4 ? std::atoi(argv[4]) : 0;
  const bool print_rounds = argc > 5 && std::atoi(argv[5]) != 0;
  if (rounds <= 0 || per == 0) {
    std::fprintf(stderr, "rounds and work must be positive\n");
    return 1;
  }
  std::printf("rounds=%d per_producer=%llu\n", rounds,
              static_cast<unsigned long long>(per));

  auto compare_one = [&](int p, int c, double &a, double &b) {
    compare_pair<ours, reference>(p, c, per, rounds, a, b, print_rounds);
  };
  if (only_p > 0 && only_c > 0) {
    double a = 0.0;
    double b = 0.0;
    compare_one(only_p, only_c, a, b);
    std::printf("%dP/%dC  ours %7.1f M/s   reference %7.1f M/s   ratio %.2f\n",
                only_p, only_c, a, b, a / b);
    return 0;
  }
  for (auto [p, c] : {std::pair{1, 1}, {2, 2}, {4, 4}, {4, 1}, {1, 4}}) {
    double a = 0.0;
    double b = 0.0;
    compare_one(p, c, a, b);
    std::printf("%dP/%dC  ours %7.1f M/s   reference %7.1f M/s   ratio %.2f\n",
                p, c, a, b, a / b);
  }
}
