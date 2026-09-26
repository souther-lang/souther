# ADR-0121: A pattern means what the language reads it as, and no carrier reads its text

Status: Accepted. Applies ADR-0112 to `String.matches`, the one kernel whose meaning was still a
host library's.

## Context

`[#stdlib-string]` defined `String.matches(pattern, s)` as a whole-string match in "Java `Pattern`
flavour". That sentence made `java.util.regex` the definition of the pattern language, and the
compiler followed it in four places that did not agree with each other:

- the checker decided which text is a pattern by calling `Pattern.compile` on it;
- the analysis read the same text with its own reader, `PatternParser`, which refused a lookaround,
  a back reference, a property class, a flag group, a possessive count and more — a pattern it
  refused was still a valid program, so the analysis was short of it;
- the compiler's constant fold of `matches` ran `Pattern.compile` again, with a budget on how many
  characters the backtracking engine may read;
- the JVM run time ran `Pattern.compile` on the author's text a third time.

`KernelFact.StringMatches` carried the text, documented as "proven acceptable to
`java.util.regex.Pattern`". The WebAssembly backend had written a fourth reader of the same text,
with its own answers for `\b` and case-insensitive matching, and the native backend
(souther-native-compiler#85) was about to need a fifth. No Rust engine implements
`java.util.regex`'s syntax and semantics, so a native `matches` would either refuse what the JVM
accepts or answer differently, and nothing said which was wrong.

ADR-0112 states the rule this falls under — a backend does not decide what an operation means — and
ADR-0120 applied it to what a `String` is. The pattern language was the remaining case.

## Decision

**The pattern language is the specification's.** `[#string-patterns]` states it: which text is a
pattern, and which set of strings each construct denotes, as sets of scalar values and regular
operations over them. `String.matches(p, s)` is true exactly when `s` is one of the strings `p`
denotes. It says which strings match and not how a match is found, so a lookaround, a back reference,
a flag group, a property class, a boundary, a quotation, a class of classes and a possessive count
are not in it. They are not features a carrier has yet to implement; they have no meaning in this
operation.

**The language is the set `PatternParser` already read exactly, and it does not narrow.** A pattern
the reader accepted keeps the meaning it had. The shorthands keep their ASCII sets (`\s` is not
String whitespace, which is a separate set the specification states separately), `.` keeps the five
line terminators out, and an anchor keeps the answer whole-string matching gives it wherever that
answer does not depend on the string — `(^a|b$)` is `a|b`, `a^b` accepts nothing, `(a|)^b` is
refused. Narrowing anchors to the ends of a pattern was considered and not taken: it would refuse
patterns that have a meaning today, which is a separate change from moving who owns the meaning.

**A pattern is read once, by the compiler, and what crosses to an output is its meaning.** The
checker reads the text with `PatternParser` and refuses the call where it is no pattern (E1323,
quoting the construct). `KernelFact.StringMatches` carries `PatternMeaning` — sets of symbols, the
empty string, no string, sequence, choice and bounded repetition — beside the text, which is
provenance an output may quote and never read. `PatternMeaning` has no node for an anchor, a
shorthand or a group: those are settled by the reader and do not reach an output, so a new way of
writing a set of symbols changes the reader and nothing that lowers a pattern. A compiled plan
(an NFA or a DFA) is not what crosses: states and minimisation are the compiler's choices, and an
output lowers the meaning to whatever its carrier runs.

**Every consumer answers from the meaning.**

- The constant fold walks the machine the meaning builds. A walk reads each symbol once, so the
  budget on the engine's reads goes; what is still bounded is building the machine, which has an
  allowance of its own (`PatternPlan.Budget.OF_A_FOLD`).
- The JVM runs what `JavaPatterns` writes from the meaning: sets by their ranges, never `.` or a
  shorthand, groups that capture nothing, no anchor. `java.util.regex` is a target here the way
  bytecode is, and the text it is handed is never the author's.
- Raoh's pattern constraint is handed the same written text, so the boundary and the run-time check
  accept the same strings. What an `invalid_format` issue carries as `pattern` is that text, which
  for a plain format reads as it was written — `[0-9]{3}\-[0-9]{4}`.

**Depth is a limit of the compiler, not of the language.** Every walk over a pattern — the reader,
the machines, a lowering — goes by its depth, so a pattern nesting groups past `PatternParser.DEEPEST`
is refused as E2104, the code for a source nesting deeper than the compiler reads, and not as a
construct the language lacks. The word `pattern_too_deeply_nested` leaves the adequacy vocabulary:
such a pattern is refused where it is checked, so no report is written of a program holding one.
`schema 23` is unreleased and is corrected in place.

## Consequences

- A program whose pattern uses a construct outside the language no longer compiles. The patterns in
  this repository's models and examples are all inside it.
- `KernelFact.StringMatches(String)` becomes `StringMatches(String written, PatternMeaning meaning)`,
  and `Backend.BOUNDARY_VERSION` moves: a reader built before it admits a carried body whose pattern
  this reader refuses, and a class emitted before it hands the author's text to the JVM's engine.
- The WebAssembly backend no longer compiles against this `KernelFact` until its `Patterns` reader
  is replaced by a lowering of `PatternMeaning`; its `\b` and case-insensitive arms go with the
  reader, since the language does not have them. No text-to-meaning bridge is offered for it, which
  would keep that reader alive. The native backend lowers the meaning and has no pattern reader to
  write.
- A reading of the rules still meets refused patterns, because analysis goes on over a module with
  errors in it. What it says there is that the rule was not read; the error beside it says why.
- Tests that used a back reference as "a rule this compiler cannot read" use
  `ARuleNoReadingTakesIn.narrowly`, a predicate over the strings whose text is made of the value
  itself.

## What this does not settle

- Whether `\s` should become String whitespace, or `\d` and `\w` Unicode classes. Each is a change
  to what existing patterns accept, and each is a decision about the language on its own.
- A property class such as `\p{L}`. It is expressible — the reader would expand it into a set of
  scalar values against a pinned Unicode version, as `[#string-whitespace]` pins `White_Space` — and
  no output would change, since what crosses is the set.
- How fast a carrier matches. The JVM's engine backtracks on the text `JavaPatterns` writes, and a
  pattern with nested choices can take time that grows quickly with the input.

## References

- Spec: `[#string-patterns]`, `[#stdlib-string]`, `[#a-matches-pattern-is-a-literal-regular-expression]`,
  `[#e1323]`, `[#e2104]`
- ADR-0112 (a backend does not change a value to fit a host API), ADR-0120 (a `String`'s NFC is a
  carrier invariant)
- Issue #1977; souther-native-compiler#85
