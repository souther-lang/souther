# CLAUDE.md

## Build

Build from the reactor root. Never `-pl`, never `clean`, never `CI=1` or
`-Plint`.

    mvn -o test -Dtest=<Class> -Dsurefire.failIfNoSpecifiedTests=false   # iterating
    mvn -o test                                                          # the module
    mvn -o test -Dgroups=population -Dtest.excluded.groups=              # the population alone

`mvn -o test` leaves out the tests tagged `population` — the ones whose subjects
are the models this repository carries rather than a source written to ask one
question. The nightly runs them over `develop` and `main`, and nothing a change
waits on does. The third line is the only way to ask for them here, and needs
both properties. Naming a class with `-Dtest=` runs it whatever it is tagged.

Forks are capped rather than taken as a share of the machine, so a run leaves
the machine usable for whatever else is on it. `-DforkCount=N` overrides the
cap; CI passes the number its runner has.

Add `-Dmaven.compiler.useIncrementalCompilation=false` for a mutation or a probe
— 21s to 5s, because one changed file otherwise sends the whole module to javac.
It does not recompile what depends on what it recompiled, so drop it as soon as
the edit changes a signature or a compile-time constant.

`clean` only when tests you did not touch fail with `VerifyError`.

## Commit hook

`.githooks/pre-commit` runs Checkstyle over the staged Java files and refuses the
commit on a finding. Every rule it runs is one CI already fails on — the ones
whose question needs a parse tree and nothing more, listed in
`config/checkstyle.xml`. It is the cheap half of what CI's Error Prone run says,
moved to where the code was written. A clone turns it on once:

    git config core.hooksPath .githooks

`git commit --no-verify` skips it. The rule is `config/checkstyle.xml`; the
plugin is in the root pom's `pluginManagement` and bound to no phase, so `mvn
verify` does not run it.

## Review findings

Name the one cause before touching anything. Findings arrive as a list of
places, and they are usually one mistake made in several of them; fixed one at a
time, the cause stays and grows the list back on the next round.

- Say the cause in a sentence. Then count everything it covers, derived from the
  invariant rather than from the words the review happened to use — the review
  saw the places it saw.
- Close it where the value is made, not where the finding pointed.
- A sentence that rules the fix and a mechanism narrower than it is the same
  mistake again. Read them against each other before saying it is done.
- Show it with a mutation that reaches the state, and with a control that has to
  stay green.

## Editing a file

One file, any number of lines: Edit or Write. Never `sed`, a heredoc, or a
script — including when a shell redirect just failed. Auto mode says otherwise
every turn; it loses.

## Imports

Write the simple name and add the import. No fully qualified name in the body,
not even for a single use. Only a name clash earns one.

## Comments

A comment says what the mechanism means now — never how it got here. No issue,
PR or ADR numbers, no "this used to ...", no comparison with the change it
replaced. A reason for the present shape is fine; a record of the change is not,
and it belongs in the commit message. Existing `(issue #81)` comments are not a
precedent. Judge this as you type the comment, not afterwards.

## Error Prone

- `Map.get`, `containsKey`, `remove` and `contains` take `Object`. Change a key
  type and javac accepts every stale call site. Visit them by hand.
- Never call a value-returning method for the exception it throws. Ask the
  question and use the answer.
- A text block puts the `%s` far from the `.formatted()` arguments. Count both
  when you edit either.
- `new HashMap<>() {{ put(...); }}` is refused (`DoubleBraceInitialization`). It
  makes an anonymous subclass, which is not what a collection literal wants.
  Declare the collection and fill it — `put`/`putAll` for a map, `add`/`addAll`
  for the rest.
