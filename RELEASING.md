# Releasing

Releases are built and published by `.github/workflows/release.yml` from
annotated tags on `main`. Do not create a GitHub release by hand.

## Repository settings

Enable immutable releases before the first release. This is a one-time
repository setting:

```sh
gh api --method PUT repos/mmabdpr/mpmc-queue-lean/immutable-releases
gh api repos/mmabdpr/mpmc-queue-lean/immutable-releases --jq .enabled
```

The release workflow cannot enable this setting.

## Prepare

1. On a `dev/<topic>` branch, update the version in `CMakeLists.txt`,
   `lakefile.toml`, `Cargo.toml`, and `CHANGELOG.md`.
2. Run `cargo check --all-targets` to refresh the root `Cargo.lock`, then
   commit the manifest and lockfile together on the development branch.
3. Push the development branch, address review findings, and wait for the
   complete `CI` matrix to pass on its head.
4. Squash-merge the reviewed development branch into `main` as one commit, as
   required by `AGENTS.md`.
5. Wait for the `CI` workflow to pass on that exact `main` commit.
6. Confirm the working tree is clean and `main` matches `origin/main`.

## Publish

```sh
version=X.Y.Z
git switch main
git pull --ff-only
test "$(git rev-parse HEAD)" = "$(git rev-parse origin/main)"
test -z "$(git status --porcelain)"
git tag -a "v$version" -m "mpmc-lean $version"
git push origin "v$version"
```

The tag starts the release workflow. It checks that:

- the tag is annotated;
- its commit is reachable from `origin/main`;
- the CMake, Lake, crate, and changelog versions agree;
- `CI` passed for the tagged commit.

It then builds source and headers archives, checks their contents, builds and
tests the source archive, verifies both archives and the checksums, creates a
draft release, downloads the draft assets to verify their bytes, and publishes
the release.

Assets:

- `mpmc-lean-X.Y.Z.tar.gz`: complete tagged source tree.
- `mpmc-lean-X.Y.Z-headers.tar.gz`: headers, documentation, and licenses.
- `SHA256SUMS`: checksums for both archives.

## Rust crate

For tags that include the crate, the source archive contains the `mpmc-lean`
crate. The GitHub release workflow runs its debug and release tests and package
verification but does not publish to crates.io. The published `v0.1.0` release
predates the crate; its first crates.io publication must use the next version.
After the GitHub release is green, publish the crate only from its tagged
commit:

```sh
git fetch --force --tags origin main
git checkout "v$version"
python3 tools/release.py publish-check "v$version"
cargo package --locked
cargo publish --dry-run --locked
cargo publish --locked
```

Do not publish a crate version that differs from the tagged C/Lean version.
`tools/release.py` validates the CMake, Lake, crate, and changelog versions
when the crate manifest is present.

## Verify

```sh
gh release view "v$version" -R mmabdpr/mpmc-queue-lean
gh release verify "v$version" -R mmabdpr/mpmc-queue-lean
```

## Recovery

If verification fails before publication, first check whether a draft or
published release exists. If only a draft exists, you can fix a transient
problem and re-run the workflow with the same tag; the workflow replaces the
draft. If the source needs a change, update `main`, wait for the new `CI` run,
then delete and recreate the unpublished tag:

```sh
version=X.Y.Z
git push origin ":refs/tags/v$version"
git tag -d "v$version"
git tag -a "v$version" -m "mpmc-lean $version"
git push origin "v$version"
```

A failed `publish` job does not prove the release is unpublished; check
`gh release view "v$version" -R mmabdpr/mpmc-queue-lean` first. Once a release is published, do not move
or reuse its tag; publish a new patch version instead.
