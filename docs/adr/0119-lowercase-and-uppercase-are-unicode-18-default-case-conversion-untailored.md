# ADR-0119: `lowercase`/`uppercase` are Unicode 18.0.0's default case conversion, untailored

Status: Accepted. Settles what ADR-0118's "What this does not settle" section left open, and
narrows ADR-0112's and ADR-0118's consequences for `String.lowercase`/`String.uppercase` the same
way ADR-0118 narrowed ADR-0112's for `String.trim`: both ADR-0112's "stay on `JdkVirtual`" bullet
and ADR-0118's "is unchanged" bullet, each naming `lowercase`/`uppercase` among the operations
untouched by that ADR, no longer hold for those two.

## Context

`String.lowercase`/`String.uppercase` were emitted as `Intrinsics.jdk` straight to
`java.lang.String`'s no-argument `toLowerCase()`/`toUpperCase()`, which map using
`Locale.getDefault()`. One Souther program computes two answers for `String.uppercase("i")`
depending on the JVM's default locale — `"I"` normally, `"İ"` under a Turkish default — from
nothing the program itself wrote down (issue #1873).

A first attempt (PR #1872) pinned `Locale.ROOT`. Review found this settles only one of three
questions the JDK method conflates:

- **Locale tailoring.** Which locale's conventions apply. `Locale.ROOT` settles this one.
- **Mapping width.** Unicode's *simple* case mapping is one code point to one code point;
  its *full* mapping can be one-to-many (`ß` → `SS` on uppercasing, Turkish `İ` → `i` + a combining
  dot above on lowercasing) and, in one case, string-context-sensitive (Greek `Σ` → `ς` only at the
  end of a cased run, `Σ` → `σ` elsewhere). `String#toLowerCase(Locale)`/`toUpperCase(Locale)`
  perform full mapping; a spec sentence saying "simple" while the implementation does full mapping
  would be wrong as written.
- **Unicode version.** Which version's mapping tables are meant. This JDK (25) is built against an
  older Unicode version for casing than the one ADR-0118 already pinned `String` whitespace to:
  `Character.toUpperCase(0xAB4B)` — LATIN SMALL LETTER SCRIPT R, given an uppercase pair only in a
  later Unicode revision — returns the code point unchanged, because this JVM's casing tables do
  not carry that pair yet, even though `Character.isDefined` already knows the code point.

Settling only locale tailoring would have left the other two implicit — the same kind of
unstated-semantics gap ADR-0118 closed for whitespace, one level up, and found only because a
reviewer worked out a concrete diverging example rather than because a rule named it.

Reopening `String`'s canonical-form guarantee (ADR-0096: NFC at exactly two boundaries, not on
every String-producing operation) to also cover casing's result is a separate question, tracked as
its own issue (#1874) — casing composing with a combining mark is not a defect this contract
introduces, and does not block it either way.

WASM backend parity is tracked in `souther-wasm-compiler`#21, filed against this decision.

## Decision

**`String.lowercase`/`String.uppercase` are Unicode 18.0.0's default case conversion, with no
locale or language tailoring.**

Concretely: the full case mapping `UnicodeData.txt` and `SpecialCasing.txt` define together —
one-to-many expansions included — plus the one context-dependent condition
`SpecialCasing.txt` states that is not itself a locale (`Final_Sigma`, over the derived `Cased` and
`Case_Ignorable` properties). Every `SpecialCasing.txt` entry that names a language (`tr`, `az`,
`lt`) is read and discarded at generation time; none of it reaches the mapping. There is no
`CaseMode` or `Locale` parameter — a locale-sensitive Turkish/Azeri casing, if ever needed, is a
distinct, explicitly named operation (e.g. `lowercaseIn`/`uppercaseIn`), never a hidden mode of
these two.

This does not add an `NFC(lowercase(s)) == lowercase(s)` postcondition. Whether that should hold —
for every String-producing operation, not only these two — is issue #1874's question, not this
one's; ADR-0096 already documents that an internally-built `String` can leave NFC, and Unicode
itself does not promise casing preserves a normalization form.

### Implementation

`Kernel.STRING_LOWERCASE`/`STRING_UPPERCASE` move off `Intrinsics.jdk` onto
`Strings.lowercase`/`Strings.uppercase` in `souther-runtime` — the same move ADR-0118 made for
`trim`, and for the same reason: a host method may be called directly only when it is proven
semantically equivalent, invariant included, and `String#toLowerCase()`/`toUpperCase()` are not,
on any of the three axes above.

The mapping and property data spans thousands of code points across both directions and hundreds
of `Cased`/`Case_Ignorable` ranges — too large for a hand-enumerated `switch`, the way ADR-0118's
25-code-point whitespace set is written, and a count here would rot on the next Unicode version
this same file regenerates against. It is generated: `bin/GenerateCaseTables.java`,
run manually (never during `mvn`, since a Unicode version bump is a specification change, not a
dependency bump) against a downloaded `UnicodeData.txt`/`SpecialCasing.txt`/`DerivedCoreProperties.txt`
for one pinned version, emits `souther-runtime/.../souther/runtime/CaseTables.java` — generated
*data*, recorded as compact encoded strings decoded once at class-load (a literal `int[][]` this
size does not fit the JVM's 64&nbsp;KB per-method bytecode limit as an initializer), headed with the
Unicode version and the three input files' SHA-256 checksums so a reviewer can tell a regeneration
from the version it claims from one that silently wasn't. The `Final_Sigma` algorithm itself —
"preceded by `Cased`, skipping `Case_Ignorable`, and not immediately followed by `Cased` the same
way" — is ordinary reviewed Java in `Strings.mapCase`/`isFinalSigmaContext`, reading the generated
tables rather than being generated itself: the data is generated, the logic that reads it is not.

## Consequences

`String.uppercase`/`String.lowercase` can change a string's length in code points (`ß` → `SS`,
`İ` → `i` + a combining mark) — a caller relying on `length(uppercase(s)) == length(s)` was relying
on a coincidence true only for the ASCII subset, same shape as ADR-0096's length consequence.

Casing a `Souther` program produces the same answer on every JVM it runs on, and — once
`souther-wasm-compiler`#21 lands — the same answer under WASM, regardless of both the process's
default locale and the host's own Unicode version.

A Unicode version bump is now a decision with a visible trail: rerun
`java bin/GenerateCaseTables.java <ucd-directory>` against the new version's files, review the
regenerated `CaseTables.java`'s changed checksums and diffed mappings, and add whatever witness case
the new version's changes call for — not something that happens by upgrading the JDK or a
dependency. The generator fails rather than regenerating on two things it cannot itself resolve: an
input file whose own version header does not match the pinned version, and a `SpecialCasing.txt`
condition that is neither the unconditional case, `Final_Sigma`, nor a language in its known
tailoring set — the file format's own documentation warns that a later version may add either a new
language or a new language-insensitive context, and only a human deciding which one a new condition
is keeps the untailored/tailored line where ADR-0119 draws it.

`ACaseConversionIsUnicode18DefaultUntailoredTest` (`souther-runtime`) covers the full-mapping
expansions (`ß`, Turkish-locale `İ`'s untailored full form), `Final_Sigma` on both sides of the
sigma and through a `Case_Ignorable` code point in between — including the one code point
(`U+0345`) that is both `Cased` and `Case_Ignorable`, where Unicode's possessive
`Case_Ignorable*` skip means "preceded by Cased" is not satisfied — the absence of Turkish
tailoring, and a Unicode 18.0.0 case pair this JVM's own casing does not currently answer. That
last case asserts the contract directly rather than by comparison with the host: `Strings.uppercase`
must answer it regardless of what any particular JDK's own tables know, now or after a future JDK
catches up.
