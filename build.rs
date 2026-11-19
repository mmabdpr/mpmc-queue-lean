// Copyright (c) 2026 Mohammad Mahdi Abdollahpour.
// SPDX-License-Identifier: CPAL-1.0
// The contents of this file are subject to the Common Public Attribution
// License Version 1.0 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// https://opensource.org/license/cpal-1-0.
// The Original Code is mpmc-lean. The Initial Developer is Mohammad Mahdi
// Abdollahpour. See LICENSE and NOTICE.

//! Build script: compile the generated C kernel and link its platform atomics.

use std::env;

fn main() {
    let target = env::var("TARGET").expect("Cargo sets TARGET");
    let target_os = env::var("CARGO_CFG_TARGET_OS").expect("Cargo sets target OS");
    let target_arch = env::var("CARGO_CFG_TARGET_ARCH").expect("Cargo sets target arch");

    if target_os != "linux" && target_os != "macos" {
        panic!(
            "mpmc-lean supports GCC/Clang on Linux and macOS; \
             {target} is not a supported target"
        );
    }
    if target_arch != "x86_64" && target_arch != "aarch64" {
        panic!(
            "mpmc-lean requires 16-byte lock-free atomics on x86_64 or aarch64; \
             {target} is not a supported target"
        );
    }

    for path in [
        "src/mpmc.c",
        "include/mpmc.h",
        "include/mpmc/detail/impl.h",
        "include/mpmc/detail/kernel.inc",
    ] {
        println!("cargo:rerun-if-changed={path}");
    }
    println!("cargo:rerun-if-env-changed=CC");
    println!("cargo:rerun-if-env-changed=CFLAGS");

    let mut build = cc::Build::new();
    build
        .file("src/mpmc.c")
        .include("include")
        .std("c11")
        .warnings(true)
        .extra_warnings(true)
        .pic(true)
        .flag_if_supported("-Wpedantic");

    let gcc = build.get_compiler().is_like_gnu();

    if target_arch == "x86_64" {
        // The C implementation needs cmpxchg16b.  Clang accepts -mcx16 on
        // both Linux and macOS; GCC uses it to expose the 16-byte builtins.
        build.flag_if_supported("-mcx16");
    } else if target_arch == "aarch64" && target_os == "linux" && gcc {
        panic!(
            "mpmc-lean requires Clang on Linux arm64: GCC's 16-byte libatomic \
             implementation is only guaranteed lock-free on newer runtimes. \
             Set CC=clang (Clang 18 is tested)."
        );
    }

    build.compile("mpmc");

    // GCC's 16-byte helpers can require libatomic on Linux.  Clang's
    // supported inline-atomic paths do not, so linking it unconditionally
    // would impose an unnecessary dependency on minimal Clang deployments.
    if target_os == "linux" && gcc {
        println!("cargo:rustc-link-lib=atomic");
    }
}
