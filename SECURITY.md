# Security policy

`mpmc-lean` is a bounded MPMC queue for critical software. The C/C++ library is
small and allocation-free on the hot path, but it is not formally verified end
to end; see the "Trusted computing base" section of `docs/proof.md`.

## Reporting a vulnerability

Please report suspected memory-safety, undefined-behavior, data-race, or
API-contract issues privately to:

**git@mohammadmahdi.com**

Include the platform, compiler, sanitizer output if available, and a minimal
reproducer. Please do not open a public issue before a fix is available.

## Supported versions

Only the latest tagged release is supported with security fixes. Please include
the release tag/commit in any report. We aim to acknowledge reports within
seven days.

## Scope

In scope:

- the public C API in `include/mpmc.h` and the C++ wrapper;
- the hand-written allocation/initialization wrapper in `src/mpmc.c` and
  `include/mpmc/detail/impl.h`;
- the safe Rust wrapper in `src/lib.rs` and its build script;
- the generated kernel in `include/mpmc/detail/kernel.inc`;
- the build, install, and packaging files.

Out of scope for this repository:

- the correctness of the C compiler or its 16-byte atomic lowering;
- formal-proof obligations that are documented as unmechanized: lock-freedom/
  liveness and the full C11/C++ refinement;
- misuse such as destroying a queue while another thread is using it, or
  passing a non-NULL pointer that was not returned by `mpmc_create`.

An unmechanized guarantee is not a license for implementation defects:
wrong values, data races, or contract violations in the advertised API are
in scope even when the corresponding refinement theorem is not proved.
