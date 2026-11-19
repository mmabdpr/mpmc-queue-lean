#!/usr/bin/env python3
# Copyright (c) 2026 Mohammad Mahdi Abdollahpour.
# SPDX-License-Identifier: CPAL-1.0
# The contents of this file are subject to the Common Public Attribution
# License Version 1.0 (the "License"); you may not use this file except in
# compliance with the License. You may obtain a copy of the License at
# https://opensource.org/license/cpal-1-0.
# The Original Code is mpmc-lean. The Initial Developer is Mohammad Mahdi
# Abdollahpour. See LICENSE and NOTICE.
"""Validate and package mpmc-lean release tags."""

from __future__ import annotations

import argparse
import hashlib
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
STABLE_TAG = re.compile(
    r"^v(0|[1-9][0-9]*)\.(0|[1-9][0-9]*)\.(0|[1-9][0-9]*)$"
)
HEADER_PATHS = (
    "include",
    "LICENSE",
    "NOTICE",
    "README.md",
    "CHANGELOG.md",
    "CONTRIBUTING.md",
    "RELEASING.md",
    "SECURITY.md",
    "docs",
)


class ReleaseError(RuntimeError):
    """A release invariant was not satisfied."""


def _run(command: list[str]) -> str:
    completed = subprocess.run(
        command,
        cwd=ROOT,
        check=False,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if completed.returncode != 0:
        message = (completed.stderr or "").strip() or (
            completed.stdout or ""
        ).strip()
        raise ReleaseError(message or "command failed")
    return completed.stdout


def _git(*arguments: str) -> str:
    return _run(["git", *arguments]).strip()


def _tag_version(tag: str) -> str:
    match = STABLE_TAG.fullmatch(tag)
    if match is None:
        raise ReleaseError(
            "tag must have the form vMAJOR.MINOR.PATCH"
        )
    return ".".join(match.groups())


def _tag_commit(tag: str) -> str:
    reference = f"refs/tags/{tag}"
    try:
        tag_type = _git("cat-file", "-t", reference)
    except ReleaseError as error:
        raise ReleaseError(f"tag {tag} does not exist") from error
    if tag_type != "tag":
        raise ReleaseError(f"tag {tag} must be annotated")
    return _git("rev-parse", f"{reference}^{{commit}}")


def _require_on_main(commit: str) -> None:
    completed = subprocess.run(
        [
            "git",
            "merge-base",
            "--is-ancestor",
            commit,
            "refs/remotes/origin/main",
        ],
        cwd=ROOT,
        check=False,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.PIPE,
        text=True,
    )
    if completed.returncode == 1:
        raise ReleaseError(
            f"tag commit {commit} is not reachable from origin/main"
        )
    if completed.returncode != 0:
        detail = completed.stderr.strip() or (
            "fetch origin/main before validating the release"
        )
        raise ReleaseError(detail)


def _commit_file(commit: str, path: str) -> str:
    return _git("show", f"{commit}:{path}")


def _project_version(cmake: str) -> str:
    matches = re.findall(
        r"^project\(mpmc_lean\s+VERSION\s+(\d+\.\d+\.\d+)\b",
        cmake,
        re.MULTILINE,
    )
    if len(matches) != 1:
        raise ReleaseError(
            "CMakeLists.txt must contain exactly one project VERSION"
        )
    return matches[0]


def _lake_version(lakefile: str) -> str:
    matches = re.findall(
        r'^version = "([0-9]+\.[0-9]+\.[0-9]+)"$',
        lakefile,
        re.MULTILINE,
    )
    if len(matches) != 1:
        raise ReleaseError(
            'lakefile.toml must contain exactly one version = "X.Y.Z"'
        )
    return matches[0]


def _cargo_version(manifest: str) -> str:
    matches = re.findall(
        r'^version = "([0-9]+\.[0-9]+\.[0-9]+)"$',
        manifest,
        re.MULTILINE,
    )
    if len(matches) != 1:
        raise ReleaseError(
            'Cargo.toml must contain exactly one package version = "X.Y.Z"'
        )
    return matches[0]


def _changelog_section(changelog: str, version: str) -> str:
    heading = re.compile(
        rf"^## {re.escape(version)}(?: - [^\r\n]*)?[ \t]*$",
        re.MULTILINE,
    )
    matches = list(heading.finditer(changelog))
    if len(matches) != 1:
        raise ReleaseError(
            f"CHANGELOG.md must contain exactly one ## {version} section"
        )
    start = matches[0].end()
    following = re.search(r"^## ", changelog[start:], re.MULTILINE)
    end = start + following.start() if following is not None else len(changelog)
    body = changelog[start:end].strip()
    if not body:
        raise ReleaseError(f"CHANGELOG.md section ## {version} is empty")
    return body


def validate_tag(tag: str) -> tuple[str, str]:
    version = _tag_version(tag)
    commit = _tag_commit(tag)
    _require_on_main(commit)

    cmake_version = _project_version(_commit_file(commit, "CMakeLists.txt"))
    lake_version = _lake_version(_commit_file(commit, "lakefile.toml"))
    if cmake_version != version:
        raise ReleaseError(
            f"CMake project version is {cmake_version}, expected {version}"
        )
    if lake_version != version:
        raise ReleaseError(
            f"lakefile.toml version is {lake_version}, expected {version}"
        )
    try:
        cargo_manifest = _commit_file(commit, "Cargo.toml")
    except ReleaseError:
        # Tags before the Rust crate was added did not have this file.
        cargo_manifest = None
    if cargo_manifest is not None:
        cargo_version = _cargo_version(cargo_manifest)
        if cargo_version != version:
            raise ReleaseError(
                f"Cargo.toml version is {cargo_version}, expected {version}"
            )
    _changelog_section(_commit_file(commit, "CHANGELOG.md"), version)
    return version, commit


def release_notes(tag: str) -> str:
    version, commit = validate_tag(tag)
    body = _changelog_section(
        _commit_file(commit, "CHANGELOG.md"), version
    )
    has_cargo = True
    try:
        _commit_file(commit, "Cargo.toml")
    except ReleaseError:
        has_cargo = False
    rust_clause = "the safe Rust crate, " if has_cargo else ""
    rust_requirements = (
        "The Rust crate needs Rust 1.74 or newer and a GCC/Clang C11 toolchain;\n"
        "on Linux arm64, use Clang 18 (GCC arm64 is rejected).\n"
        if has_cargo
        else ""
    )
    rust_test = (
        "The source archive's Rust crate can be tested from its extracted root:\n\n"
        "```sh\n"
        "cargo test --all-targets\n"
        "```\n\n"
        if has_cargo
        else ""
    )
    return (
        f"{body}\n\n"
        "## Install\n\n"
        "The source archive contains the Lean proofs, the generated C kernel,\n"
        f"the C and C++ headers, {rust_clause}tests, benchmarks, and\n"
        "CMake/pkg-config packaging. A C11 compiler and CMake 3.20 or newer are\n"
        "required for the library; the test suite also needs a C++17 compiler.\n"
        f"{rust_requirements}"
        "Lean 4.36 and elan are required only to rebuild the proofs.\n\n"
        "```sh\n"
        f"tar -xzf mpmc-lean-{version}.tar.gz\n"
        f"cmake -S mpmc-lean-{version} -B build -DCMAKE_BUILD_TYPE=Release\n"
        "cmake --build build -j\n"
        "ctest --test-dir build --output-on-failure\n"
        "cmake --install build --prefix /usr/local\n"
        "```\n\n"
        "The headers archive is self-contained: add its `include/` directory to\n"
        "the compiler include path. The C++ wrapper needs C++17; the C API\n"
        "needs C11. On x86-64, pass `-mcx16` and link `-latomic` if the\n"
        "toolchain requires them.\n\n"
        f"{rust_test}"
        "## Downloads\n\n"
        f"- `mpmc-lean-{version}.tar.gz`: complete tagged source tree.\n"
        f"- `mpmc-lean-{version}-headers.tar.gz`: public and detail headers,\n"
        "  documentation, and license files.\n"
        "- `SHA256SUMS`: checksums for both archives.\n\n"
        "```sh\n"
        "# Linux\n"
        "sha256sum -c SHA256SUMS\n"
        "# macOS\n"
        "shasum -a 256 -c SHA256SUMS\n"
        "```\n\n"
        "The machine-checked result covers the sequentially consistent\n"
        "kernel-event core described in `docs/proof.md`. The C printer,\n"
        "compiler and 16-byte atomic lowering, allocation/initialization\n"
        "wrapper, C11/C++ lowering, and kernel-level progress remain trusted or\n"
        "unmechanized. The C library does not carry an end-to-end proof.\n\n"
        "Tested in CI on Ubuntu 24.04 (GCC 13 and Clang 18), Ubuntu 24.04 arm64\n"
        "(Clang 18), and macOS 15 (Apple Clang). Windows and MSVC are not\n"
        "supported. Licensed under CPAL-1.0; see `LICENSE` and `NOTICE`.\n"
    )


def _archive(
    commit: str,
    output: Path,
    prefix: str,
    paths: tuple[str, ...],
) -> None:
    if output.exists():
        output.unlink()
    command = [
        "git",
        "-c",
        "tar.tar.gz.command=gzip -cn",
        "-c",
        "tar.umask=0002",
        "-c",
        "core.autocrlf=false",
        "archive",
        "--format=tar.gz",
        f"--prefix={prefix}/",
        "-o",
        str(output),
        commit,
        *paths,
    ]
    _run(command)


def package_release(tag: str, destination: str) -> None:
    version, commit = validate_tag(tag)
    dist = Path(destination).resolve()
    dist.mkdir(parents=True, exist_ok=True)
    prefix = f"mpmc-lean-{version}"

    source = dist / f"{prefix}.tar.gz"
    headers = dist / f"{prefix}-headers.tar.gz"
    _archive(commit, source, prefix, ())
    _archive(commit, headers, prefix, HEADER_PATHS)

    checksum_path = dist / "SHA256SUMS"
    lines = []
    for path in (source, headers):
        digest = hashlib.sha256(path.read_bytes()).hexdigest()
        lines.append(f"{digest}  {path.name}\n")
    checksum_path.write_bytes("".join(lines).encode("ascii"))

    for path in (source, headers, checksum_path):
        print(path, file=sys.stderr)


def check_publication_checkout(tag: str) -> None:
    version, commit = validate_tag(tag)
    try:
        _commit_file(commit, "Cargo.toml")
    except ReleaseError as error:
        raise ReleaseError(
            f"tag {tag} has no Cargo.toml; it predates the Rust crate"
        ) from error
    head = _git("rev-parse", "HEAD")
    if head != commit:
        raise ReleaseError(
            f"HEAD is {head}, expected tagged commit {commit}"
        )
    if _git("status", "--porcelain"):
        raise ReleaseError(
            "working tree is not clean; commit or discard changes before publishing"
        )
    print(
        f"publication checkout is clean: {tag} at {commit} ({version})",
        file=sys.stderr,
    )


def _build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Validate and package a tagged mpmc-lean release."
    )
    subparsers = parser.add_subparsers(dest="command", required=True)

    check = subparsers.add_parser(
        "check", help="validate a tag and print its numeric version"
    )
    check.add_argument("tag")

    notes = subparsers.add_parser(
        "notes", help="write release notes for a tag"
    )
    notes.add_argument("tag")
    notes.add_argument("output")

    package = subparsers.add_parser(
        "package", help="write source, headers, and checksum archives"
    )
    package.add_argument("tag")
    package.add_argument("destination")

    publish_check = subparsers.add_parser(
        "publish-check",
        help="require a clean checkout at an exact release tag",
    )
    publish_check.add_argument("tag")
    return parser


def main() -> int:
    arguments = _build_parser().parse_args()
    try:
        if arguments.command == "check":
            version, commit = validate_tag(arguments.tag)
            print(f"tag {arguments.tag} -> {commit} ({version})", file=sys.stderr)
            print(version)
        elif arguments.command == "notes":
            output = Path(arguments.output)
            output.parent.mkdir(parents=True, exist_ok=True)
            output.write_bytes(release_notes(arguments.tag).encode("utf-8"))
        elif arguments.command == "package":
            package_release(arguments.tag, arguments.destination)
        elif arguments.command == "publish-check":
            check_publication_checkout(arguments.tag)
        else:
            raise ReleaseError(f"unknown command: {arguments.command}")
    except ReleaseError as error:
        print(f"error: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
