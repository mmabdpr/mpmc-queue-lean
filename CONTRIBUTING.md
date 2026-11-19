# Contributing

Contributions are accepted under the Common Public Attribution License 1.0
(CPAL-1.0). By submitting a change you agree that it may be distributed under
those terms. See `LICENSE` and `NOTICE`.

## Before sending a change

```sh
lake build
lake env lean scripts/CheckAxioms.lean
lake exe mpmc-codegen
lake exe mpmc-kernel-trace
test -z "$(git status --porcelain -- include/mpmc/detail/kernel.inc 'tests/kernel_trace*.txt')"
cmake -S . -B build -DCMAKE_BUILD_TYPE=Release
cmake --build build -j
ctest --test-dir build --output-on-failure
cargo fmt --all -- --check
cargo clippy --all-targets -- -D warnings
cargo test --all-targets --locked
cargo test --release --all-targets --locked
cargo test --doc --locked
cargo package --locked
```

The Lean sources must contain no `sorry` or `admit`, and no new `axiom`
declarations. The axiom audit allows only `propext`, `Quot.sound`, and
`Classical.choice`.

Rust tests compile the same `src/mpmc.c` and generated kernel through
`build.rs`; no CMake build is required for the crate. The crate supports Rust
1.74 and newer on Linux x86-64 with GCC or Clang, Linux arm64 with Clang 18,
and macOS with Apple Clang.

## Generated files

`include/mpmc/detail/kernel.inc` and `tests/kernel_trace*.txt` are generated.
Change the Lean IR or trace generator, then regenerate and commit the result.
CI rejects generated-file drift.

## Scope

The machine-checked result is the SC kernel-event core described in
`docs/proof.md`. The C printer, compiler/atomic lowering, allocator/init
wrapper, C11/C++ lowering, the Rust ownership/FFI wrapper, and kernel-level
progress are trusted or unmechanized. Do not describe the C code as verified
end to end.
