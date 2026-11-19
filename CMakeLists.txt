# Copyright (c) 2026 Mohammad Mahdi Abdollahpour.
# SPDX-License-Identifier: CPAL-1.0
# The contents of this file are subject to the Common Public Attribution
# License Version 1.0 (the "License"); you may not use this file except in
# compliance with the License. You may obtain a copy of the License at
# https://opensource.org/license/cpal-1-0.
# The Original Code is mpmc-lean. The Initial Developer is Mohammad Mahdi
# Abdollahpour. See LICENSE and NOTICE.
cmake_minimum_required(VERSION 3.20)
project(mpmc_lean VERSION 0.1.1 LANGUAGES C)

if(NOT CMAKE_C_COMPILER_ID MATCHES "GNU|Clang")
  message(FATAL_ERROR
    "mpmc requires GCC or Clang: the implementation uses the GCC/Clang "
    "__atomic builtins for lock-free 16-byte cell operations.")
endif()

include(GNUInstallDirs)

if(CMAKE_SOURCE_DIR STREQUAL PROJECT_SOURCE_DIR)
  set(MPMC_TOP_LEVEL ON)
else()
  set(MPMC_TOP_LEVEL OFF)
endif()

option(MPMC_BUILD_TESTS "Build the test suite" ${MPMC_TOP_LEVEL})
option(MPMC_BUILD_BENCH "Build benchmarks" ${MPMC_TOP_LEVEL})

if((MPMC_BUILD_TESTS OR MPMC_BUILD_BENCH) AND NOT MPMC_TOP_LEVEL AND
   NOT CMAKE_CXX_COMPILER_ID)
  message(FATAL_ERROR
    "MPMC_BUILD_TESTS/MPMC_BUILD_BENCH require CXX in the top-level project. "
    "Enable CXX before adding mpmc as a subdirectory, or build mpmc standalone.")
endif()
if(MPMC_BUILD_TESTS OR MPMC_BUILD_BENCH)
  enable_language(CXX)
  if(NOT CMAKE_CXX_COMPILER_ID MATCHES "GNU|Clang")
    message(FATAL_ERROR
      "mpmc tests and benchmarks require a GCC or Clang C++ compiler.")
  endif()
endif()

if(MPMC_TOP_LEVEL)
  set(CMAKE_C_STANDARD 11)
  set(CMAKE_C_STANDARD_REQUIRED ON)
  set(CMAKE_C_EXTENSIONS OFF)
  set(CMAKE_CXX_STANDARD 17)
  set(CMAKE_CXX_STANDARD_REQUIRED ON)
  set(CMAKE_CXX_EXTENSIONS OFF)
  if(NOT CMAKE_BUILD_TYPE)
    set(CMAKE_BUILD_TYPE Release CACHE STRING "" FORCE)
  endif()
endif()

option(MPMC_SANITIZE "Build with address/undefined sanitizers" OFF)
option(MPMC_TSAN "Build with the thread sanitizer" OFF)
option(MPMC_ENABLE_LTO "Enable link-time optimization for the benchmarks" ON)
option(MPMC_INSTALL "Install mpmc, its CMake package, and its pkg-config file" ${MPMC_TOP_LEVEL})
option(BUILD_SHARED_LIBS "Build mpmc as a shared library" OFF)

if(MPMC_SANITIZE AND MPMC_TSAN)
  message(FATAL_ERROR "MPMC_SANITIZE and MPMC_TSAN are mutually exclusive")
endif()

set(MPMC_PC_CFLAGS "")
set(MPMC_PC_LIBS "")

if(MPMC_BUILD_TESTS OR MPMC_BUILD_BENCH)
  find_package(Threads REQUIRED)
endif()

add_library(mpmc
  src/mpmc.c
)
add_library(mpmc::mpmc ALIAS mpmc)
set_target_properties(mpmc PROPERTIES
  EXPORT_NAME mpmc
  VERSION ${PROJECT_VERSION}
  SOVERSION 1
  INTERPROCEDURAL_OPTIMIZATION FALSE
)

target_include_directories(mpmc
  PUBLIC
    $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/include>
    $<INSTALL_INTERFACE:${CMAKE_INSTALL_INCLUDEDIR}>
  PRIVATE ${CMAKE_CURRENT_SOURCE_DIR}/src ${CMAKE_CURRENT_SOURCE_DIR}
)
target_compile_features(mpmc PUBLIC c_std_11)
target_compile_features(mpmc INTERFACE cxx_std_17)
target_compile_options(mpmc PRIVATE
  $<$<CONFIG:Release>:-O3>
  -Wall
  -Wextra
  -Wpedantic
)

# 16-byte lock-free compare-exchange on x86-64 needs cmpxchg16b, which some
# toolchains gate behind -mcx16.  The option is also INTERFACE because the
# optional inline header compiles the same cell operations in the consumer's
# translation unit.
set(MPMC_ATOMIC_TEST_FLAGS "")
set(MPMC_GCC_X86_ATOMIC OFF)
if(CMAKE_SYSTEM_PROCESSOR MATCHES "^(x86_64|amd64|AMD64)$")
  target_compile_options(mpmc PRIVATE -mcx16)
  target_compile_options(mpmc INTERFACE $<$<COMPILE_LANGUAGE:C,CXX>:-mcx16>)
  set(MPMC_PC_CFLAGS "-mcx16")
  set(MPMC_ATOMIC_TEST_FLAGS "-mcx16")
  if(CMAKE_C_COMPILER_ID STREQUAL "GNU")
    set(MPMC_GCC_X86_ATOMIC ON)
  endif()
endif()

# Probe the lock-free configuration used by `mpmc_create` on a 16-byte
# aligned cell.  GCC may need libatomic for the probe/call; if so, it is
# published as a link dependency.
include(CheckCSourceRuns)
set(MPMC_LOCKFREE_SOURCE "
  #include <stdint.h>
  typedef struct { _Alignas(16) uint64_t marker; uint64_t payload; } cell;
  int main(void) {
    cell c = {0, 0};
  #if defined(__x86_64__) && defined(__GNUC__) && !defined(__clang__) && \
      defined(__GCC_HAVE_SYNC_COMPARE_AND_SWAP_16)
    (void)c;
    return 0;
  #else
    return __atomic_is_lock_free(sizeof(cell), &c) ? 0 : 1;
  #endif
  }")
# Cross-compiling cannot run the probe.  Set `-DMPMC_LOCKFREE=TRUE` (and
# `-DMPMC_LOCKFREE_LIBATOMIC=TRUE` if `-latomic` is required) to skip it.
if(NOT DEFINED MPMC_LOCKFREE)
  set(CMAKE_REQUIRED_FLAGS "${MPMC_ATOMIC_TEST_FLAGS}")
  check_c_source_runs("${MPMC_LOCKFREE_SOURCE}" MPMC_LOCKFREE)
  unset(CMAKE_REQUIRED_FLAGS)
endif()
if(NOT MPMC_LOCKFREE AND NOT DEFINED MPMC_LOCKFREE_LIBATOMIC)
  set(CMAKE_REQUIRED_FLAGS "${MPMC_ATOMIC_TEST_FLAGS}")
  set(CMAKE_REQUIRED_LIBRARIES atomic)
  check_c_source_runs("${MPMC_LOCKFREE_SOURCE}" MPMC_LOCKFREE_LIBATOMIC)
  unset(CMAKE_REQUIRED_LIBRARIES)
  unset(CMAKE_REQUIRED_FLAGS)
endif()

if(NOT MPMC_LOCKFREE AND NOT MPMC_LOCKFREE_LIBATOMIC)
  message(FATAL_ERROR
    "mpmc requires lock-free 16-byte atomics: "
    "__atomic_is_lock_free(16, aligned-pointer) is false.  Use Clang, or a "
    "GCC configuration with -mcx16 (x86-64) / LSE (arm64) and libatomic.")
endif()
if(MPMC_LOCKFREE_LIBATOMIC OR MPMC_GCC_X86_ATOMIC)
  target_link_libraries(mpmc PUBLIC atomic)
  set(MPMC_PC_LIBS "-latomic")
endif()

if(MPMC_BUILD_BENCH AND MPMC_ENABLE_LTO AND NOT MPMC_SANITIZE AND NOT MPMC_TSAN)
  include(CheckIPOSupported)
  check_ipo_supported(RESULT MPMC_IPO_SUPPORTED OUTPUT MPMC_IPO_MESSAGE)
  if(NOT MPMC_IPO_SUPPORTED)
    message(STATUS "LTO not supported: ${MPMC_IPO_MESSAGE}")
  endif()
endif()

if(MPMC_SANITIZE)
  target_compile_options(mpmc PUBLIC -fsanitize=address,undefined -fno-omit-frame-pointer)
  target_link_options(mpmc PUBLIC -fsanitize=address,undefined)
endif()

if(MPMC_TSAN)
  target_compile_options(mpmc PUBLIC -fsanitize=thread -fno-omit-frame-pointer)
  target_link_options(mpmc PUBLIC -fsanitize=thread)
endif()

if(MPMC_BUILD_TESTS)
  enable_testing()

add_executable(mpmc_test_basic tests/test_basic.c)
target_link_libraries(mpmc_test_basic PRIVATE mpmc Threads::Threads)
add_test(NAME basic COMMAND mpmc_test_basic)

add_executable(mpmc_test_stress tests/test_stress.c)
target_link_libraries(mpmc_test_stress PRIVATE mpmc Threads::Threads)
add_test(NAME stress COMMAND mpmc_test_stress 2 2 200000 1024)
add_test(NAME stress_1p1c COMMAND mpmc_test_stress 1 1 200000 8)
add_test(NAME stress_2cap COMMAND mpmc_test_stress 1 1 20000 2)
add_test(NAME stress_2cap_4p4c COMMAND mpmc_test_stress 4 4 20000 2)
add_test(NAME stress_4p1c COMMAND mpmc_test_stress 4 1 100000 16)
add_test(NAME stress_1p4c COMMAND mpmc_test_stress 1 4 100000 16)

add_executable(mpmc_test_stress_ffi tests/test_stress.c)
target_compile_definitions(mpmc_test_stress_ffi PRIVATE MPMC_TEST_USE_LIBRARY=1)
target_link_libraries(mpmc_test_stress_ffi PRIVATE mpmc Threads::Threads)
add_test(NAME stress_ffi COMMAND mpmc_test_stress_ffi 2 2 100000 16)

add_executable(mpmc_test_mixed tests/test_mixed.c)
target_link_libraries(mpmc_test_mixed PRIVATE mpmc Threads::Threads)
add_test(NAME mixed_2p2c_cap2 COMMAND mpmc_test_mixed 2 50000 2)
add_test(NAME mixed_4p4c_cap8 COMMAND mpmc_test_mixed 4 50000 8)

add_executable(mpmc_test_exhaustion_concurrent
  tests/test_exhaustion_concurrent.c)
target_link_libraries(mpmc_test_exhaustion_concurrent PRIVATE mpmc Threads::Threads)
add_test(NAME exhaustion_concurrent COMMAND mpmc_test_exhaustion_concurrent)

add_executable(mpmc_test_mixed_abi
  tests/test_mixed_abi.c
  tests/mixed_abi_lib.c
  tests/mixed_abi_inline.c)
target_link_libraries(mpmc_test_mixed_abi PRIVATE mpmc)
add_test(NAME mixed_abi COMMAND mpmc_test_mixed_abi)

add_executable(mpmc_test_cpp tests/test_cpp.cpp)
target_link_libraries(mpmc_test_cpp PRIVATE mpmc Threads::Threads)
add_test(NAME cpp COMMAND mpmc_test_cpp)

add_executable(mpmc_test_header_only tests/test_header_only.c)
target_compile_features(mpmc_test_header_only PRIVATE c_std_11)
target_include_directories(mpmc_test_header_only PRIVATE
  ${CMAKE_CURRENT_SOURCE_DIR}/include)
if(CMAKE_SYSTEM_PROCESSOR MATCHES "^(x86_64|amd64|AMD64)$")
  target_compile_options(mpmc_test_header_only PRIVATE -mcx16)
endif()
if(MPMC_LOCKFREE_LIBATOMIC OR MPMC_GCC_X86_ATOMIC)
  target_link_libraries(mpmc_test_header_only PRIVATE atomic)
endif()
if(MPMC_SANITIZE)
  target_compile_options(mpmc_test_header_only PRIVATE
    -fsanitize=address,undefined -fno-omit-frame-pointer)
  target_link_options(mpmc_test_header_only PRIVATE -fsanitize=address,undefined)
endif()
if(MPMC_TSAN)
  target_compile_options(mpmc_test_header_only PRIVATE
    -fsanitize=thread -fno-omit-frame-pointer)
  target_link_options(mpmc_test_header_only PRIVATE -fsanitize=thread)
endif()
add_test(NAME header_only COMMAND mpmc_test_header_only)

add_executable(mpmc_test_layout tests/test_layout.c)
target_link_libraries(mpmc_test_layout PRIVATE mpmc)
add_test(NAME layout COMMAND mpmc_test_layout)
add_executable(mpmc_test_ffi tests/test_ffi.c)
target_link_libraries(mpmc_test_ffi PRIVATE mpmc)
add_test(NAME ffi COMMAND mpmc_test_ffi)

add_executable(mpmc_test_kernel_trace tests/test_kernel_trace.c)
target_link_libraries(mpmc_test_kernel_trace PRIVATE mpmc)
add_test(NAME kernel_trace
  COMMAND mpmc_test_kernel_trace
          ${CMAKE_CURRENT_SOURCE_DIR}/tests/kernel_trace.txt)
add_test(NAME kernel_trace_exhaust
  COMMAND mpmc_test_kernel_trace
          ${CMAKE_CURRENT_SOURCE_DIR}/tests/kernel_trace_exhaust.txt)
foreach(fuzz_id RANGE 1 6)
  add_test(NAME kernel_trace_fuzz_${fuzz_id}
    COMMAND mpmc_test_kernel_trace
            ${CMAKE_CURRENT_SOURCE_DIR}/tests/kernel_trace_fuzz_${fuzz_id}.txt)
endforeach()

set(MPMC_TEST_NAMES
  basic stress stress_1p1c stress_2cap stress_2cap_4p4c stress_4p1c
  stress_1p4c stress_ffi mixed_2p2c_cap2 mixed_4p4c_cap8
  exhaustion_concurrent mixed_abi cpp header_only layout ffi
  kernel_trace kernel_trace_exhaust)
foreach(fuzz_id RANGE 1 6)
  list(APPEND MPMC_TEST_NAMES kernel_trace_fuzz_${fuzz_id})
endforeach()
set_tests_properties(${MPMC_TEST_NAMES} PROPERTIES TIMEOUT 300)
endif()

if(MPMC_BUILD_BENCH)
add_executable(mpmc_bench bench/bench.cpp)
target_link_libraries(mpmc_bench PRIVATE mpmc Threads::Threads)
target_compile_options(mpmc_bench PRIVATE -O3)
if(MPMC_IPO_SUPPORTED)
  set_property(TARGET mpmc_bench PROPERTY INTERPROCEDURAL_OPTIMIZATION TRUE)
endif()

# Deliberately no IPO: measures the header-only path at the caller's
# optimization level.
add_executable(mpmc_bench_header bench/bench_header.c)
target_link_libraries(mpmc_bench_header PRIVATE mpmc Threads::Threads)
target_compile_options(mpmc_bench_header PRIVATE -O3)

set(MPMC_REFERENCE_INCLUDE_DIR "" CACHE PATH
    "Path to the C++ reference's include directory (enables mpmc_compare)")
if(MPMC_REFERENCE_INCLUDE_DIR)
  add_executable(mpmc_compare bench/compare.cpp)
  target_include_directories(mpmc_compare PRIVATE ${MPMC_REFERENCE_INCLUDE_DIR})
  target_link_libraries(mpmc_compare PRIVATE mpmc Threads::Threads)
  target_compile_options(mpmc_compare PRIVATE -O3)
  if(MPMC_IPO_SUPPORTED)
    set_property(TARGET mpmc_compare PROPERTY INTERPROCEDURAL_OPTIMIZATION TRUE)
  endif()
endif()

if(MPMC_BUILD_TESTS)
  add_test(NAME bench_smoke COMMAND mpmc_bench 1 1 1000 4)
  add_test(NAME bench_header_smoke COMMAND mpmc_bench_header 1 1 1000 4)
  set_tests_properties(bench_smoke bench_header_smoke PROPERTIES TIMEOUT 120)
endif()
endif()

# ---------------------------------------------------------------------------
# Install / package configuration
# ---------------------------------------------------------------------------

if(MPMC_INSTALL)
include(CMakePackageConfigHelpers)

install(TARGETS mpmc
  EXPORT mpmcTargets
  ARCHIVE DESTINATION ${CMAKE_INSTALL_LIBDIR}
  LIBRARY DESTINATION ${CMAKE_INSTALL_LIBDIR}
  RUNTIME DESTINATION ${CMAKE_INSTALL_BINDIR}
  INCLUDES DESTINATION ${CMAKE_INSTALL_INCLUDEDIR}
)
install(DIRECTORY include/ DESTINATION ${CMAKE_INSTALL_INCLUDEDIR})

install(EXPORT mpmcTargets
  FILE mpmcTargets.cmake
  NAMESPACE mpmc::
  DESTINATION ${CMAKE_INSTALL_LIBDIR}/cmake/mpmc
)

configure_package_config_file(cmake/mpmcConfig.cmake.in
  ${CMAKE_CURRENT_BINARY_DIR}/mpmcConfig.cmake
  INSTALL_DESTINATION ${CMAKE_INSTALL_LIBDIR}/cmake/mpmc
)
write_basic_package_version_file(
  ${CMAKE_CURRENT_BINARY_DIR}/mpmcConfigVersion.cmake
  VERSION ${PROJECT_VERSION}
  COMPATIBILITY SameMinorVersion
)
install(FILES
  ${CMAKE_CURRENT_BINARY_DIR}/mpmcConfig.cmake
  ${CMAKE_CURRENT_BINARY_DIR}/mpmcConfigVersion.cmake
  DESTINATION ${CMAKE_INSTALL_LIBDIR}/cmake/mpmc
)

file(RELATIVE_PATH MPMC_PC_PREFIX_REL
  "${CMAKE_INSTALL_FULL_LIBDIR}/pkgconfig"
  "${CMAKE_INSTALL_PREFIX}")
string(REGEX REPLACE "/$" "" MPMC_PC_PREFIX_REL "${MPMC_PC_PREFIX_REL}")
configure_file(cmake/mpmc.pc.in ${CMAKE_CURRENT_BINARY_DIR}/mpmc.pc @ONLY)
install(FILES ${CMAKE_CURRENT_BINARY_DIR}/mpmc.pc
  DESTINATION ${CMAKE_INSTALL_LIBDIR}/pkgconfig
)
install(FILES LICENSE NOTICE CHANGELOG.md CONTRIBUTING.md RELEASING.md
  DESTINATION ${CMAKE_INSTALL_DATAROOTDIR}/doc/mpmc
)

endif()
