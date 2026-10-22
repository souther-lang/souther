#!/usr/bin/env bash
# Fail unless the commit the build read, the one argument, is HEAD of the tree being built.
# `-Prelease` and `-Psnapshot` run it, because that commit is written into every jar's manifest as
# `Implementation-Revision`, and `-Prelease` asks whether it is tagged for the version.
#
# The build reads it through the git-commit-id plugin, which in a linked worktree reads the main
# checkout's repository and answers with the main checkout's HEAD. Built from a worktree that
# stands anywhere else, a jar would name a commit it was not built from, and the tag asked about
# would be that commit's. Asked of git here, the answer is about this tree.
#
# The tree that is asked is the one the script is in, so a linked worktree answers for itself.
set -euo pipefail

if [ $# -ne 1 ]; then
  echo "usage: $0 <the commit the build read>" >&2
  exit 2
fi

root="$(cd "$(dirname "$0")/.." && pwd)"
cd "$root"

head="$(git rev-parse HEAD)"

if [ "$1" != "$head" ]; then
  echo "The build read $1 as the commit it builds, and HEAD here is $head." >&2
  echo "A linked worktree is read as the main checkout: publish from the main checkout or a clone." >&2
  exit 1
fi
