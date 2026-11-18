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

#include <cstdint>
#include <cstdio>
#include <stdexcept>
#include <utility>

static int failures = 0;

#define CHECK(cond)                                                          \
  do {                                                                       \
    if (!(cond)) {                                                           \
      std::fprintf(stderr, "FAIL %s:%d: %s\n", __FILE__, __LINE__, #cond);   \
      ++failures;                                                            \
    }                                                                        \
  } while (0)

int main() {
  mpmc::queue q(4);

  for (std::uint64_t i = 0; i < 4; ++i) {
    CHECK(q.push(1000 + i));
  }
  CHECK(!q.push(9999));

  for (std::uint64_t i = 0; i < 4; ++i) {
    std::uint64_t value = 0;
    CHECK(q.pop(value));
    CHECK(value == 1000 + i);
  }
  {
    std::uint64_t value = 0;
    CHECK(!q.pop(value));
  }

  mpmc::queue moved(std::move(q));
  CHECK(moved.push(42));
  {
    std::uint64_t out = 0;
    CHECK(moved.pop(out));
    CHECK(out == 42);
  }
  CHECK(!q.push(1));
  {
    std::uint64_t out = 0;
    CHECK(!q.pop(out));
  }

  {
    mpmc::queue a(4);
    mpmc::queue b(4);
    CHECK(a.push(11));
    CHECK(b.push(22));
    a = std::move(b);  // destroys a's nonempty queue, takes b's
    std::uint64_t out = 0;
    CHECK(a.pop(out));
    CHECK(out == 22);
    CHECK(!b.push(33));  // moved-from
    a = std::move(a);    // self-move must leave a usable
    CHECK(a.push(44));
    CHECK(a.pop(out));
    CHECK(out == 44);
  }

  bool invalid_threw = false;
  try {
    mpmc::queue invalid(3);
  } catch (const std::invalid_argument &) {
    invalid_threw = true;
  }
  CHECK(invalid_threw);

  if (failures != 0) {
    std::fprintf(stderr, "%d failure(s)\n", failures);
    return 1;
  }
  std::puts("cpp: ok");
  return 0;
}
