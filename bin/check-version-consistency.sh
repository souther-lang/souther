#!/usr/bin/env bash
# Fail if the Souther version is not identical everywhere it is declared. The core reactor root pom is
# the authority; the independent examples build, the Clojure account example's deps.edn, and the
# README annotation-processor snippet must all match it. This is the guardrail against a version bump
# landing in some files and being forgotten in others (the rc3 bump first missed the examples build).
# CI runs this; run it locally after bin/set-version.sh.
set -euo pipefail
root="$(cd "$(dirname "$0")/.." && pwd)"
cd "$root"

# Authority: the first <version> in the core reactor root pom (its own project version).
core="$(sed -n 's#.*<version>\(.*\)</version>.*#\1#p' pom.xml | head -1)"
if [ -z "$core" ]; then
  echo "could not read the core version from pom.xml" >&2
  exit 2
fi

fail=0
check() { # <label> <found>
  if [ "$2" != "$core" ]; then
    echo "version drift: $1 = '$2' (core is '$core')" >&2
    fail=1
  fi
}

check "examples/pom.xml <souther.version>" \
  "$(sed -n 's#.*<souther.version>\(.*\)</souther.version>.*#\1#p' examples/pom.xml | head -1)"
check "account deps.edn souther-runtime" \
  "$(sed -n 's#.*souther-runtime {:mvn/version "\([^"]*\)".*#\1#p' examples/account/deps.edn | head -1)"
check "account deps.edn souther-compiler" \
  "$(sed -n 's#.*souther-compiler {:mvn/version "\([^"]*\)".*#\1#p' examples/account/deps.edn | head -1)"
check "README souther-compiler snippet" \
  "$(sed -n 's#.*souther-compiler:\([^<]*\)</path>.*#\1#p' examples/README.md | head -1)"

if [ "$fail" -ne 0 ]; then
  echo "Souther version is inconsistent. Reconcile with: bin/set-version.sh $core" >&2
  exit 1
fi
echo "Souther version consistent everywhere: $core"
