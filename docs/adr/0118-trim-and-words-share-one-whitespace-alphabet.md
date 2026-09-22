# ADR-0118: `trim` and `words` share one whitespace alphabet

Status: Accepted. Narrows ADR-0112's consequences for `String.trim`.

## Context

`String.trim` was emitted as `Intrinsics.JdkVirtual` straight to `java.lang.String.trim`, which
strips every code point `<= U+0020`. `String.words` was `Strings.words`, splitting on the Java
regex class `\s`, which is the six ASCII characters `[ \t\n\x0B\f\r]`. The two agreed on far less
than either author likely assumed: both treated NBSP (U+00A0) and every non-ASCII Unicode space
such as the full-width IDEOGRAPHIC SPACE (U+3000) as ordinary characters, neither `trim` stripping
them nor `words` splitting on them. Where they disagreed was the C0 control range below U+0020 that
is not TAB/LF/VT/FF/CR: `String.trim("\u001Ca\u001C")` removed the FILE SEPARATOR control character
(it is `<= U+0020`), while `String.words("a\u001Cb")` did not split on it (`\s` does not include
it). `words` and `trim` are read as one concept in `[#stdlib-string]` — a caller trims a field and
then reads its words — and the specification named neither set: `+words(s)+` said only "runs of
whitespace", and `+trim+` had no defining sentence at all, only an entry in the function table
(issue #1871).

ADR-0112 already states the general rule this falls under — a backend may reach for a host
primitive only where "the primitive is semantically equivalent to the language contract" — and
its consequences list kept `String.trim` on `JdkVirtual`, reasoning that "the values go over
unchanged and the operations answer on all of them". That check is necessary but was not
sufficient here: totality and representation are not the whole of a language contract, and the
meaning of "whitespace" the JDK's `trim` answers to was never compared against the one `words`
already used. The two carriers of one Souther concept had silently drifted, and no rule in either
carrier or in the specification said which of them was right — because neither host method's
whitespace set had been chosen as *the* Souther one.

Unlike `[#a-string-is-ordered-by-utf16-code-units]`, there was no existing, internally-consistent
behaviour to promote to a rule: `trim`'s `<= U+0020` and `words`'s ASCII `\s` are two different,
independently-arrived-at sets, not one convention observed from two angles. This is a case for
settling new specification, not for writing down what the JVM happened to do.

## Decision

**A Souther program has one whitespace alphabet, `[#string-whitespace]`, and `trim` and `words`
are both defined over it.** The set is the 25 code points of Unicode 18.0's `White_Space`
property, enumerated in the specification rather than named by reference to that property, so a
future JDK's or a future Unicode version's table cannot change what a Souther program means
without a specification change alongside it.

`Strings.isWhitespace(int)` is the one predicate both `Strings.trim` and `Strings.words` scan
code points against; `Strings.words`'s Java-regex `\s` split is gone. `Kernel.STRING_TRIM` moves
from `Intrinsics.JdkVirtual` (`java.lang.String.trim`) to `Intrinsics.RuntimeStatic`
(`Strings.trim`), next to `STRING_WORDS` in the emitter table, and out of
`TheRuntimeAnswersEveryKernelAtItsDeclaredAbiTest`'s `ANSWERED_BY_THE_HOST` set.

## What this raised, and does not settle by itself

The same question — does a host method's meaning match the one Souther has committed to, or only
its totality and representation — applies next and most sharply to `String.lowercase`/`uppercase`
(`java.lang.String.toLowerCase`/`toUpperCase` with no `Locale` argument, so both the mapping table
a JVM ships and the *default locale it happens to be running under* decide the answer). Case
conversion has no sibling operation like `words` to expose a disagreement the way this issue did.
ADR-0119 settles that one, fixing a locale the same way this ADR fixes a whitespace set.
`contains`/`startsWith`/`endsWith`/`append` stay on `JdkVirtual` under ADR-0112 for a different
reason and are not part of either risk: each is a sequence operation over the representation
Souther already shares with the JDK, with no Unicode property table or locale behind it.

## Consequences

- ADR-0112's consequences bullet naming `String.trim` as staying on `JdkVirtual` no longer holds;
  `trim` moved to `Strings`, alongside `words`, `characters` and the runtime's other code-point
  operations. `lowercase`/`uppercase` move too, under ADR-0119. The rest of that bullet —
  `contains`/`startsWith`/`endsWith`/`append` and the `DateTime` conversions staying on
  `JdkVirtual` — is unchanged.
- `String.trim` on a control character below U+0020 that is not TAB/LF/VT/FF/CR (e.g. U+0007 BEL,
  U+001C FILE SEPARATOR) no longer strips it; that behaviour was never specified and came only
  from the JDK method's own `<= U+0020` rule.
- `String.trim` on U+00A0 (NBSP), U+2000-U+200A, U+2028, U+2029, U+202F, U+205F and U+3000 now
  strips them, matching `words`.
- `String.words(trim(s)) == String.words(s)` holds for every `s`, and no element `words` returns
  contains a String-whitespace code point — the algebraic property `[#string-whitespace]` states.

## References

- Issue #1871
- Specification: `[#stdlib-string]`, `[#string-whitespace]`
- ADR-0112: a backend does not change a value to fit a host API
- Unicode 18.0 `White_Space` property (`PropList.txt`)
