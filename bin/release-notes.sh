#!/usr/bin/env bash
# The text of the GitHub Release for a version: docs/releases/<version>.md with each paragraph and
# each list item on one line.
#
#     bin/release-notes.sh <version>
#
# The notes are wrapped as every document here is, and a Release renders a line break inside a
# paragraph as a break, so a paragraph wrapped in the source comes out broken at each line. Code
# blocks, headings, tables and quotations are written as they stand. Refuses a version that has no
# notes or empty ones.
set -euo pipefail
if [ $# -ne 1 ]; then
  echo "usage: $0 <version>" >&2
  exit 2
fi
notes="$(dirname "$0")/../docs/releases/$1.md"
if [ ! -s "$notes" ]; then
  echo "$1 has no release notes: $notes is missing or empty" >&2
  exit 1
fi
awk '
  function flush() { if (held != "") { print held; held = "" } }
  /^```/ { flush(); fence = !fence; print; next }
  fence { print; next }
  /^[[:space:]]*$/ { flush(); print; next }
  /^(#|\||>)/ { flush(); print; next }
  /^[[:space:]]*([-*+]|[0-9]+\.)[[:space:]]/ { flush(); held = $0; next }
  {
    line = $0
    if (held != "") { sub(/^[[:space:]]+/, "", line); held = held " " line }
    else { held = line }
  }
  END { flush() }
' "$notes"
