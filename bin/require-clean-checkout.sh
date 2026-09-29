#!/usr/bin/env bash
# Fail unless the working tree contains exactly the files and contents recorded by HEAD: no modified,
# staged, deleted or untracked file, and no ignored one either. `-Prelease` runs it, because the commit
# the build writes into every jar's manifest describes the jar only if nothing else went into it.
#
# Ignored files are refused too, whatever they are. A `target` left by an earlier build, a file under
# `syntax` that a pom copies into a jar, or anything a plugin reads that a later change to the build
# adds would each get through a check that named the places the build reads. The way to satisfy this is
# a fresh clone of the tag.
#
# The tree that is asked is the one the script is in, so a linked worktree answers for itself.
set -euo pipefail

root="$(cd "$(dirname "$0")/.." && pwd)"
cd "$root"

state="$(git status --porcelain --ignored)"

if [ -n "$state" ]; then
  echo "This is not an exact checkout of $(git rev-parse HEAD):" >&2
  echo "$state" >&2
  exit 1
fi
