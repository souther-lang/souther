# ADR-0119: String case conversion fixes a locale

Status: Accepted. Narrows ADR-0112's consequences for `String.lowercase`/`uppercase`.

## Context

`String.lowercase` and `String.uppercase` were emitted as `Intrinsics.JdkVirtual` straight to
`java.lang.String.toLowerCase()`/`toUpperCase()` — the no-argument overloads, which map every
character using `Locale.getDefault()` rather than a locale the call names. A JVM's default locale
comes from the platform it starts on, not from anything a Souther program writes down, so the same
program could answer `"i".uppercase() == "I"` on one machine and `"i".uppercase() == "İ"` (dotted
capital I) on another whose default locale is Turkish — the standard example, `Locale`'s own
Javadoc names it, of a case mapping that a plain `i`/`I` is not stable under. ADR-0118, discovered
while settling issue #1871, raised this as the next instance of the same question and left it
open rather than folding an unrelated decision into a whitespace fix.

ADR-0112 kept `lowercase`/`uppercase` on `JdkVirtual` in the same consequences bullet as `trim`,
by the same reasoning: the value passes through unchanged and the operation answers on every
`String`. That reasoning checks totality and representation, and neither speaks to the *locale*
question — a JVM-default-dependent answer is not a partial function or an information loss, it is
one Souther program computing two different results depending on where it runs, which is a defect
independent of anything issue #1871 raised about whitespace.

## Decision

**`lowercase`/`uppercase` fix `Locale.ROOT`.** `Strings.lowercase`/`Strings.uppercase` call
`String#toLowerCase(Locale)`/`toUpperCase(Locale)` with `Locale.ROOT` explicitly, never the
no-argument overload. `Kernel.STRING_LOWERCASE`/`STRING_UPPERCASE` move from `Intrinsics.JdkVirtual`
to `Intrinsics.RuntimeStatic`, out of `TheRuntimeAnswersEveryKernelAtItsDeclaredAbiTest`'s
`ANSWERED_BY_THE_HOST` set. `[#string-case]` states the rule the specification never had: case
conversion is Unicode's locale-independent simple mapping, not a mapping a Souther program can
select or that its running environment selects for it.

`contains`/`startsWith`/`endsWith`/`append` are unaffected: none of the four takes a `Locale`
overload at all, because none of them maps a character. They stay on `JdkVirtual` per ADR-0112.

## What was weighed and rejected

**Add a `Locale` parameter, or a `String.lowercaseIn(locale, s)`.** Souther has no `Locale` type
and no BCP-47 tag primitive, so this would need one built and validated before the casing question
could even be asked, for a feature nothing in the language motivates today. A model that needs
locale-sensitive casing writes it as a domain lookup table over `Map<String, String>`, the same way
any other business-specific text transform would be written; it is not a good the standard library
owes for free at the risk of every other caller's program depending on where it runs.

**Follow `Character.toLowerCase(int)` per code point instead of `String#toLowerCase(Locale)`.**
`Character`'s per-code-point mapping does not perform the locale-independent *special* casing
Unicode also specifies (`ß` to `SS` on uppercasing, German sharp s, is the standard one-to-many
example) — `String#toLowerCase(Locale.ROOT)`/`toUpperCase(Locale.ROOT)` do. Per-code-point mapping
would silently narrow what "case conversion" means for exactly the inputs a caller is least likely
to test.

## Consequences

- `String.uppercase("i")` is `"I"` and `String.lowercase("İ")` is `"i̇"` (dotted, with a combining
  dot above) everywhere this runs, never `"İ"`/`"i"` under a Turkish default locale or any other
  locale a JVM might start with.
- ADR-0112's consequences bullet for `lowercase`/`uppercase` no longer holds; ADR-0118 already
  updated it to say so.
- The published-declaration boundary version is unaffected: this changes what a call answers, not
  what a signature admits.

## References

- Issue #1871
- Specification: `[#stdlib-string]`, `[#string-case]`
- ADR-0112: a backend does not change a value to fit a host API
- ADR-0118: `trim` and `words` share one whitespace alphabet
- `java.util.Locale` Javadoc, "Special case for dotted-I / dotless-i in Turkish"
