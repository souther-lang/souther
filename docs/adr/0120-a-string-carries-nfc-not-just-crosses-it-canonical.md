# ADR-0120: A `String`'s NFC is a carrier invariant, not a boundary property

Status: Accepted. Supersedes ADR-0096 in one respect only — that ADR canonicalizes text where it
crosses in from outside and states nothing about `String`-producing operations inside the domain,
and this makes every one of them hold NFC too. Its decisions about code-point counting, the two
original boundary doors, and NFC over NFKC stand unchanged.

## Context

ADR-0096 canonicalizes text at the two doors where it enters from outside — a derived decoder's
string leaf, and a source file's string literal — and says so deliberately:

> "This does not close everything, and does not claim to. [...] a string built inside the domain can
> still leave NFC: `characters` of a string that contains a combining mark, reassembled, is whatever
> it was. The two boundaries are where foreign text enters, which is where the problem comes from."

Those were not the only two doors, and one of the two was not even fully closed on its own terms —
both turned out to matter once this was looked at as a carrier invariant rather than as two fixed
sites.

`append` and its neighbors are exactly the "built inside the domain" case, and Unicode's
normalization guarantees do not cover it. Substring preserves NFC; concatenation does not:

```text
U+0061                       // "a", NFC
U+0302                       // COMBINING CIRCUMFLEX ACCENT alone, NFC on its own
U+0061 U+0302                // String.append("a", <U+0302>) — two code points, NOT NFC
U+00E2                       // NFC(U+0061 U+0302) — "â", one code point
```

So under ADR-0096 as written, `append`/`concat`/`join`/`replace`/`reverse`/`repeat`/`padLeft`/
`padRight`/`lowercase`/`uppercase` can each hand back a `String` that is not NFC, even though the
boundary already canonicalizes every value that reaches them from outside. Two canonically
equivalent strings built this way — `String.append("a", <U+0302>)` and the literal `"â"` — are
different `Map` keys, different `Set` members, and `==` false, which is the exact incoherence
ADR-0096 introduced NFC to close. It is closed for text that arrives; it is open for text a program
builds.

`++`, the operator form of `append` (spec §stdlib-string states `append(a, b) == a ++ b`), turned
out to be a *second*, independent lowering of the same operation: `BodyGen`'s `CONCAT` arm emitted a
direct `String.concat` rather than reaching for `Strings.append`, and `ConstantAlgebra`'s compile-time
fold of `CONCAT` did the same in Java (`x + y`, no canonicalization) for a constant expression the
checker can evaluate ahead of time. Both are exactly the mistake ADR-0096 already names once — "the
first attempt ... was a `.normalize()` written wherever a string leaf happened to be built" — recurring
one level up, at the operator instead of the named function. Fixing `Strings.append` alone left `"a"
++ "̂"` non-NFC and, worse, left it disagreeing with `append("a", "̂")`, which the
specification states is the same expression.

An injected behavior's answer is a *third* door ADR-0096 never named at all. Its implementation is
Java, supplied from outside the compiler, and can hand back a `String` (or a data whose field is one)
exactly as freely as JSON can — `behavior now : () -> String` with a Java `apply()` returning a
decomposed spelling is not a hypothetical. The same is true of a data's own generated factory
(`Backend.emitDataFactory`): it is `protected` precisely so an injected behavior's Java subclass can
call it directly with field values that Java code holds, not only from another generated class in the
same module.

`Values.equal` was already refused as the place to close any of this, for its own reason (ADR-0096):
a comparison that ignored normalization form would disagree with `length`/`characters`/`slice`, which
all see the raw form. The same reasoning rules it out here — canonicalizing on read would make two
equal values answer different lengths.

### Which Unicode version this reaches for

`java.text.Normalizer` is not this decision's implementation, for the same reason ADR-0119 did not
read casing off `String.toUpperCase`: this JDK's own Unicode data lags the version this language
publishes. Java 25 carries Unicode 16.0. Unicode 18.0.0 assigned code points this JDK has never
heard of — `Character.isDefined(0x1E6E3)` is `false` here — and one of them, U+1E6E3 TAI YO SIGN UE,
carries canonical combining class 230, which decides where it reorders relative to other combining
marks. A `Normalizer` that does not know the code point exists answers combining class 0 for it,
and gets Unicode 18.0.0's own conformance corpus wrong on witnesses that use it:

```text
NormalizationTest.txt, Unicode 18.0.0:
0061 1E6E3 0315 0300 05AE 0062  ;  0061 05AE 1E6E3 0300 0315 0062  ; ...
```

The right of the two normalizes the same combining marks into an order that depends on knowing
U+1E6E3's combining class is 230; a version that thinks it is 0 sorts differently.

## Decision

**`∀ s : String. NFC18(s) = s`.** Every `String` a Souther program can observe is Unicode 18.0.0
Normalization Form C, not only the ones that crossed a boundary to get there. Where a
`String`-producing site cannot preserve that by construction alone, it canonicalizes its own result
rather than leaving a caller to notice.

The implementation is `souther.unicode.Normalization.nfc`, one Unicode 18.0.0 NFC shared by every
door, generated from Unicode 18.0.0's own `UnicodeData.txt` and `CompositionExclusions.txt`
(`bin/GenerateNormalizationTables.java`, checked at generation time against
`DerivedNormalizationProps.txt`'s `Full_Composition_Exclusion`, and against the full
`NormalizationTest.txt` corpus by `bin/VerifyNormalization.java`, which checks that file's own
version header the same fail-closed way the generator checks its three inputs'), the same
regeneration discipline ADR-0119 states for its case tables. Hangul syllable decomposition and
composition are algorithmic (UAX #15), not table lookups — `UnicodeData.txt` states none for them.

### Every String-producing kernel, not just the ones spelled `String`

Every standard-library kernel whose declared result reaches a `String` — bare, or under a
`List`/`Set`/`Option`/`Map`/tuple it returns — falls into exactly one of three kinds, and a
closed-world test (`EveryStringProducingKernelPreservesOrEstablishesNfcTest`) derives the population
from `KernelSignatures.signatureOf(kernel).result()`, the checker's own resolved `Type`, walked
structurally through `ListOf`/`SetOf`/`OptionOf`/`MapOf`/`TupleOf` — not from a second parse of the
`.sou` source a declaration happens to be written in, and not from a filter that only recognizes the
bare `String` case, which would leave a future `Option<String>`-returning kernel uncovered the same
way `split`'s `List<String>` almost was here:

- **Preserves.** `slice`, `trim`, `split`, `words`, `lines` and `characters` read code points `s`
  already has and create no seam between ones that were not already adjacent. Unicode's own
  guarantee that a substring of a normalized string is normalized is what makes this true without
  help — the last four split into a `List<String>` by the same rule, one piece at a time.
- **Intrinsically canonical.** `fromInt` and `fromDecimal` produce ASCII decimal digits, which are
  NFC independent of any input — not because an invariant on the input is preserved, but because
  nothing here reads a code point wide enough to leave it.
- **Must canonicalize.** `append`, `join`, `concat`, `replace`, `reverse`, `repeat`, `lowercase`,
  `uppercase`, `padLeft` and `padRight` each canonicalize their own result. `STRING_APPEND` moves
  off the direct `String.concat` dispatch this backend gave it and into the runtime alongside the
  rest, and so does `++`'s codegen (`BodyGen`'s `CONCAT` arm now calls `Strings.append`) and its
  compile-time fold (`ConstantAlgebra`'s `CONCAT` case now canonicalizes too, so a folded `"a" ++
  <mark>` and the same expression run at the runtime it would otherwise compile to cannot answer
  differently).

Not walked into a `Type.Union`'s members: none of today's kernels answer one that carries a
`String`, and resolving what a union member's own declaration is would ask the checker's symbol
table a question this test has no business asking. Left open until a kernel makes it a live
question.

### A required behavior's answer is canonicalized at the crossing

`BodyGen.requiredCall` canonicalizes a bare `String` result the same way a decoder canonicalizes its
leaf — right where `stackCast` would otherwise hand the value straight to the caller, via a
`stackCastAtCrossing` that adds one `Normalization.nfc` call when the declared type is `String`.
`Backend.emitDataFactory` does the same for a `String`-typed field before it reaches `__construct`,
since the same `protected` factory is what an injected behavior's Java subclass calls directly.

**Scoped to bare `String` only.** A required behavior answering `List<String>`, `Option<String>`, a
`Map` keyed or valued by one, or a data whose own field is one of those, crosses the same door
uncanonicalized still. Closing that needs a recursive, `Type`-driven canonicalizing transform over an
already-materialized Java value — the same shape of problem a decoder solves by walking the *type*
it is generating a decoder *for*, but here over a value that already exists — and is deliberately
left for a follow-up rather than rushed into this decision. It is a known, named gap, not a silent
one.

### `reverse`'s law is retracted, not narrowed

ADR-0096 states `String.codePoints(String.reverse(s)) == List.reverse(String.codePoints(s))`. It
does not survive canonicalization: reversing puts a combining mark before the base character it can
now compose with, which the code points' own reversal does not do. `String.reverse` is redefined as
`NFC(reverse(codePoints(s)))`. A caller who wants the exact code-point permutation writes
`String.codePoints(s) |> List.reverse` instead — a `List<Int>` carries no canonical-form obligation,
so nothing is lost, only relocated to where the obligation does not apply.

### `padLeft`/`padRight` keep their law, at the cost of a second seam

ADR-0096's `String.length(padLeft(width, pad, s)) == Int.max(width, String.length(s))` still holds,
but the width can no longer be reached by repeating `pad` and cutting to a precomputed count: a
combining `pad` can compose into the character it is appended next to, so one copy can add fewer
code points than `pad` itself has. The fill is built by repeating `pad` a whole number of times,
canonicalizing once, and cutting to the code points still needed from its own front; the fill is
then joined to `s` and canonicalized again, because that second seam — where the fill meets `s` —
can absorb a code point neither side had alone. On the rare occasion the join still comes up one
code point short, the whole fill is rebuilt one code point wider, not grown one copy of `pad` at a
time with a fresh canonicalization each time — the difference between a linear cost and a quadratic
one when `pad` is short and `width` is not.

## Consequences

`Normalization`/`NormalizationTables` live under `souther.unicode`, a package of their own inside
the `souther-runtime` module rather than `souther.runtime` itself. NFC is a fact of the language, the
same as the code-point counting ADR-0096 already states — a WASM backend would need the identical
algorithm — and `TheRuntimePackageIsTheBackendsToNameTest` already enforces exactly that distinction
for a physical name versus a semantic one: `souther.compiler.check` (`ConstantAlgebra`'s package,
where `++`'s compile-time fold lives) reasons about declarations and may not name
`souther.runtime`, the JVM backend's own package, but naming `souther.unicode` is not what that rule
is about. Moving the two files a package sideways, with no change to which Maven module or which
dependency graph holds them, is what keeps the fold backend-neutral without duplicating the
algorithm a second time in `check`.

`CanonicalNames.name` — a new, small class in `souther-compiler`, holding exactly the one function
`Reserved.name` used to — and a source file's string literal (`AstBuilder`) call `Normalization.nfc`
directly now, not `java.text.Normalizer`, so the two ADR-0096 boundary doors move onto Unicode 18.0.0
with everything else. `Reserved` itself stays in `souther-syntax`, unchanged apart from losing that
one method: it is the standard-library namespace registry (`MODULES`/`QUALIFIERS`), which
`souther-fmt` reads without depending on the compiler, and canonicalizing an arbitrary language name
is a different responsibility that happens to need `souther-runtime` — giving it a class of its own
in `souther-compiler`, where every caller already sits, avoids handing `souther-syntax` (and
`souther-fmt` through it) a dependency on `souther-runtime`, and the Raoh dependency that carries,
for a function neither of them calls. A derived decoder's string leaf (`CodecGen.emitStringLeaf`)
and the compiler's own JSON-boundary decoder (`JsonBoundary.text`) stop calling Raoh's
`StringDecoder.normalize()` — which is `java.text.Normalizer` under its own name — and instead lift
`Normalization::nfc` through `Decoder.map`, wrapped back into a `StringDecoder` by
`StringDecoder.from` so a constraint chained after it still resolves. Raoh itself is unchanged.
`souther-compiler`'s own dependency on `souther-runtime` moves from `provided` to compile scope:
`CanonicalNames`, `AstBuilder`, `CodecGen`, `BodyGen` and `Backend` now call `Normalization.nfc`
unconditionally, not only when a generated `$Ctfe.check` class happens to load.

`Values.equal`, `Map`, `Set` and `==` were already reading `String` as canonical text for whatever
arrived from outside; they now read every `String` that way, which is what makes
`String.append("a", <U+0302>)`, `"a" ++ <U+0302>`, and the literal `"â"` the same value everywhere a
`String` is compared, not only when one of them happened to cross a boundary.

`TheRuntimeAnswersEveryKernelAtItsDeclaredAbiTest` loses `STRING_APPEND` from the kernels a JDK
method answers directly, since it now dispatches to `Strings.append` like the rest of the module.
