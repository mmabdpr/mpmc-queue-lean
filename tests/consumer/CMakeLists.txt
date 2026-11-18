# Copyright (c) 2026 Mohammad Mahdi Abdollahpour.
# The contents of this file are subject to the Common Public Attribution
# License Version 1.0 (the "License"); you may not use this file except in
# compliance with the License. You may obtain a copy of the License at
# https://opensource.org/license/cpal-1-0.
# The Original Code is mpmc-lean. The Initial Developer is Mohammad Mahdi
# Abdollahpour. See LICENSE and NOTICE.
cmake_minimum_required(VERSION 3.20)
project(mpmc_consumer LANGUAGES C CXX)

find_package(mpmc CONFIG REQUIRED)

add_executable(mpmc_consumer main.c)
target_link_libraries(mpmc_consumer PRIVATE mpmc::mpmc)

add_executable(mpmc_consumer_ffi main_ffi.c)
target_link_libraries(mpmc_consumer_ffi PRIVATE mpmc::mpmc)

add_executable(mpmc_consumer_cpp main.cpp)
target_link_libraries(mpmc_consumer_cpp PRIVATE mpmc::mpmc)
