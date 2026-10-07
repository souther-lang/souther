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

# A version that is not a snapshot ships the adequacy schema the compiler writes, and that
# schemaVersion is frozen from then on: the schema as it first shipped is kept beside the tests, and
# AShippedSchemaAcceptsEveryDocumentItShippedAcceptingTest holds every later edit of it to accepting
# what it accepted then. Written once. A later release writing the same schemaVersion keeps the
# copy rather than moving it, so a narrowing made in between cannot become the new starting point.
if [[ "$version" != *-SNAPSHOT ]]; then
  # Asked as the condition, so that finding nothing reaches the message below rather than ending
  # the script where pipefail first sees it.
  if ! schema_version="$(grep -o 'int SCHEMA_VERSION = [0-9][0-9]*' \
      souther-compiler/src/main/java/souther/compiler/report/AdequacyReport.java \
      | grep -o '[0-9][0-9]*$')"; then
    echo "found no SCHEMA_VERSION in AdequacyReport.java" >&2
    exit 1
  fi
  shipped="souther-compiler/src/test/resources/souther/compiler/schema/released/adequacy-schema-$schema_version.json"
  if [ -e "$shipped" ]; then
    echo "Schema $schema_version was already frozen; kept its released contract."
  else
    mkdir -p "$(dirname "$shipped")"
    cp "souther-compiler/src/main/resources/souther/adequacy-schema-$schema_version.json" "$shipped"
    git add "$shipped"
    echo "Froze schema $schema_version as it ships, in $shipped."
  fi
fi
