#!/usr/bin/env bash
# Fail unless the checkout this is run in holds exactly what HEAD holds, as far as a build can see it:
# no modified, staged, deleted or untracked file, and no ignored file under a src directory, which
# Maven compiles or packages the same as a tracked one. `-Prelease` runs it, because the commit the
# build writes into every jar's manifest describes the jar only if nothing else went into it.
#
# The tree that is asked is the one the script is in, so a linked worktree answers for itself.
set -euo pipefail

root="$(cd "$(dirname "$0")/.." && pwd)"
cd "$root"

changed="$(git status --porcelain)"
ignored="$(git ls-files --others --ignored --exclude-standard | grep -E '(^|/)src/' || true)"

if [ -n "$changed$ignored" ]; then
  echo "This is not a clean checkout of $(git rev-parse HEAD):" >&2
  [ -z "$changed" ] || echo "$changed" >&2
  [ -z "$ignored" ] || sed 's/^/ignored  /' <<<"$ignored" >&2
  exit 1
fi
