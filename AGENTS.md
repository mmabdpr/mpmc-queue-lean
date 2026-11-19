# Agent Workflow

## Branches

- `main` is the release/integration branch. Do not make implementation,
  review-fix, formatting, or documentation commits directly on `main`.
- Start every change on a short-lived branch from the current `main`:
  `dev/<topic>`.
- Do all edits, review iterations, regenerated files, tests, and CI runs on
  that development branch.
- Keep one development branch per change. Do not create extra worktrees for
  the same change; switch branches or work in the existing checkout.
- Delete the development branch after it is integrated.

## Merge Gate

Before a development branch reaches `main`:

1. The working tree is clean.
2. The complete `.github/workflows/ci.yml` matrix is green on the branch head.
3. Review findings are addressed, with no unresolved blocker or should-fix.
4. The branch contains no generated-file drift or temporary artifacts.
5. The final tree is ready to be represented by one commit.

Integrate with a **squash merge**: `main` receives one commit containing the
complete reviewed change. Do not merge the development branch's WIP,
review-fix, formatting, or test-iteration commits into `main`.

Do not create review commits such as "address review", "polish docs", or
"fix CI" on `main`; those belong on the development branch and must be
squashed before integration.

## Rewrites and Releases

- Do not move, delete, or rewrite a published release tag.
- Do not force-push a shared branch unless the repository owner explicitly
  approves a history correction.
- A release is tagged only after the exact `main` commit has passed CI and the
  release checks. Do not tag a development branch.
- Keep `main` linear and small. One integrated change should normally appear
  as one commit.

## Reviews

- For consequential changes, use independent read-only review before
  integration.
- Address all material findings and rerun the relevant reviews/tests on the
  final development branch head.
- Do not push review-only or fixup commits to `main` after integration; open a
  new development branch and integrate it as one commit.

## Verification

Run the checks in `CONTRIBUTING.md` on the development branch before
integration. If a check is not applicable to the change, record why. Do not
duplicate the command list here; `CONTRIBUTING.md` is the canonical source.
