#!/usr/bin/env bash
# Fail unless what the build makes an artifact from is what HEAD records. `-Prelease` and `-Psnapshot`
# run it, because the commit the build writes into every jar's manifest describes the jar only if
# nothing else went into it.
#
# Two things could put something else in. A change HEAD does not record — a modified, staged or
# deleted file, or an untracked one — anywhere in the tree. And an ignored file in a place the build
# reads, such as a `.log` under `src/main/resources`, which a resource copy would carry into a jar
# though git never sees it. Ignored files anywhere else are not read and are not asked about: an
# editor's settings, `.DS_Store`, the `.surefire-*` timings kept beside a module. What an earlier
# build wrote is not asked about either, because the profiles clean every module before they build.
#
# The places the build reads are the arguments, absolute or from the repository root: each module's own
# `src` is handed in by that module, and what is read from outside every module's `src` is
# `souther.build.reads` in the root pom, which WhatACleanCheckoutAsksIsWhatTheBuildReadsTest holds
# to what the poms copy from. With no arguments, only the first is asked.
#
# The tree that is asked is the one the script is in, so a linked worktree answers for itself.
set -euo pipefail

root="$(cd "$(dirname "$0")/.." && pwd)"
cd "$root"

changed="$(git status --porcelain)"
if [ -n "$changed" ]; then
  echo "HEAD $(git rev-parse HEAD) does not record all of this tree:" >&2
  echo "$changed" >&2
  exit 1
fi

if [ $# -gt 0 ]; then
  read_but_ignored="$(git ls-files --others --ignored --exclude-standard -- "$@")"
  if [ -n "$read_but_ignored" ]; then
    echo "The build reads these, and git does not record them:" >&2
    echo "$read_but_ignored" >&2
    exit 1
  fi
fi
