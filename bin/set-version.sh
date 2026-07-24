#!/usr/bin/env bash
# Set the Souther version in every place it is declared. The version lives in more than one build:
# the core Maven reactor, the independent examples build (which pins it through the souther.version
# property, since examples are not core reactor modules and cannot inherit ${project.version}), the
# Clojure account example's deps.edn, and the annotation-processor snippet in the examples README.
# A release bump has to touch all of them; doing it by hand is how the rc3 bump first missed the
# examples. Run from anywhere:
#
#   bin/set-version.sh 0.1.0-SNAPSHOT
#
# Then verify with bin/check-version-consistency.sh (CI runs the same check).
set -euo pipefail

if [ $# -ne 1 ]; then
  echo "usage: bin/set-version.sh <version>" >&2
  exit 1
fi
version="$1"
root="$(cd "$(dirname "$0")/.." && pwd)"
cd "$root"

# 1. Core reactor: root pom + every souther-* module's own version and parent reference.
mvn -q versions:set -DnewVersion="$version" -DgenerateBackupPoms=false

# 2. Independent examples build: the version is a property, not a reactor version.
mvn -q versions:set-property -Dproperty=souther.version -DnewVersion="$version" \
    -DgenerateBackupPoms=false -f examples/pom.xml

# 3. Clojure account example (deps.edn, outside Maven): the runtime dep and the :gen compiler dep.
perl -pi -e "s{(org\.souther-lang/souther-(?:runtime|compiler) \{:mvn/version )\"[^\"]*\"}{\${1}\"$version\"}g" \
    examples/account/deps.edn

# 4. The annotation-processor snippet in the examples README (${1} delimits the backreference so a
#    version starting with a digit is not read as $1<digit>).
perl -pi -e "s{(org\.souther-lang:souther-compiler:)[^<\s\"]*}{\${1}$version}g" \
    examples/README.md

echo "Set Souther version to $version (core, examples, account, README)."
