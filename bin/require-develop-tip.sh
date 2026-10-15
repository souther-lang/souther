#!/usr/bin/env bash
# Fail unless HEAD is the commit `develop` points at on origin now. `-Psnapshot` runs it, because a
# snapshot is published under one coordinate that every publication overwrites, and what that
# coordinate is said to hold is the tip of develop: a commit anywhere else, a feature branch's or an
# older one of develop's, would be published as if it were.
#
# The tree that is asked is the one the script is in, so a linked worktree answers for itself.
set -euo pipefail

root="$(cd "$(dirname "$0")/.." && pwd)"
cd "$root"

head="$(git rev-parse HEAD)"
tip="$(git ls-remote --exit-code origin refs/heads/develop | cut -f1)"

if [ "$head" != "$tip" ]; then
  echo "HEAD is $head, and develop on origin is $tip: this is not what develop holds." >&2
  exit 1
fi
