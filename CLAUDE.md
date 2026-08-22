# CLAUDE.md

## Build

Build from the reactor root. Never `-pl`, never `clean`, never `CI=1` or
`-Plint`.

    mvn -o test -Dtest=<Class> -Dsurefire.failIfNoSpecifiedTests=false   # iterating
    mvn -o test                                                          # before pushing

`clean` only when tests you did not touch fail with `VerifyError`.

## Error Prone

- `Map.get`, `containsKey`, `remove` and `contains` take `Object`. Change a key
  type and javac accepts every stale call site. Visit them by hand.
- Never call a value-returning method for the exception it throws. Ask the
  question and use the answer.
- A text block puts the `%s` far from the `.formatted()` arguments. Count both
  when you edit either.
