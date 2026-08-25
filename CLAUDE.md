# CLAUDE.md

## Build

Build from the reactor root. Never `-pl`, never `clean`, never `CI=1` or
`-Plint`.

    mvn -o test -Dtest=<Class> -Dsurefire.failIfNoSpecifiedTests=false   # iterating
    mvn -o test                                                          # before pushing

`clean` only when tests you did not touch fail with `VerifyError`.

## Commit hook

`.githooks/pre-commit` runs Checkstyle's `UnusedImports` over the staged Java
files and refuses the commit on a finding. It is the cheap half of what CI's
Error Prone run says, moved to where the import was written. A clone turns it on
once:

    git config core.hooksPath .githooks

`git commit --no-verify` skips it. The rule is `config/checkstyle.xml`; the
plugin is in the root pom's `pluginManagement` and bound to no phase, so `mvn
verify` does not run it.

## Error Prone

- `Map.get`, `containsKey`, `remove` and `contains` take `Object`. Change a key
  type and javac accepts every stale call site. Visit them by hand.
- Never call a value-returning method for the exception it throws. Ask the
  question and use the answer.
- A text block puts the `%s` far from the `.formatted()` arguments. Count both
  when you edit either.
