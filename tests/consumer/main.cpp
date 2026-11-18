/*
 * Copyright (c) 2026 Mohammad Mahdi Abdollahpour.
 * The contents of this file are subject to the Common Public Attribution
 * License Version 1.0 (the "License"); you may not use this file except in
 * compliance with the License. You may obtain a copy of the License at
 * https://opensource.org/license/cpal-1-0.
 * The Original Code is mpmc-lean. The Initial Developer is Mohammad Mahdi
 * Abdollahpour. See LICENSE and NOTICE.
 */
#include <mpmc.h>

#include <cstdint>
#include <cstdio>

int main() {
  mpmc::queue q(8);
  for (std::uint64_t i = 0; i < 8; ++i) {
    if (!q.push(i)) {
      std::fputs("consumer-cpp: push failed\n", stderr);
      return 1;
    }
  }
  for (std::uint64_t i = 0; i < 8; ++i) {
    std::uint64_t value = 0;
    if (!q.pop(value) || value != i) {
      std::fputs("consumer-cpp: pop mismatch\n", stderr);
      return 2;
    }
  }
  std::puts("consumer-cpp: ok");
  return 0;
}
