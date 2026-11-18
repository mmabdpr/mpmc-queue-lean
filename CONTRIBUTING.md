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
```

The Lean sources must contain no `sorry` or `admit`, and no new `axiom`
declarations. The axiom audit allows only `propext`, `Quot.sound`, and
`Classical.choice`.

## Generated files

`include/mpmc/detail/kernel.inc` and `tests/kernel_trace*.txt` are generated.
Change the Lean IR or trace generator, then regenerate and commit the result.
CI rejects generated-file drift.

## Scope

The machine-checked result is the SC kernel-event core described in
`docs/proof.md`. The C printer, compiler/atomic lowering, allocator/init
wrapper, C11/C++ lowering, and kernel-level progress are trusted or
unmechanized. Do not describe the C code as verified end to end.
