#!/usr/bin/env bash
# Set the Souther version across the reactor: the root pom plus every souther-* module's own version
# and parent reference. Run from anywhere:
#
#   bin/set-version.sh 0.1.0-SNAPSHOT
#
# develop stays on a snapshot: the version a release is cut at is set on main, where the tag goes.
# docs/releasing.md is the whole of it.
#
# The examples pin the version separately, in souther-lang/examples — they are not reactor modules
# and cannot inherit ${project.version}. Bumping a release means running that repository's
# bin/set-version.sh too.
set -euo pipefail

if [ $# -ne 1 ]; then
  echo "usage: bin/set-version.sh <version>" >&2
  exit 1
fi
version="$1"
root="$(cd "$(dirname "$0")/.." && pwd)"
cd "$root"

mvn -q versions:set -DnewVersion="$version" -DgenerateBackupPoms=false

echo "Set Souther version to $version."
