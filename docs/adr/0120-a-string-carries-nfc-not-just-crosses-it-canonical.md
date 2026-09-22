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

`append` and its neighbors are exactly that case, and Unicode's normalization guarantees do not cover
it. Substring preserves NFC; concatenation does not:

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

`Values.equal` was already refused as the place to close it, for its own reason (ADR-0096): a
comparison that ignored normalization form would disagree with `length`/`characters`/`slice`, which
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
`String`-producing operation cannot preserve that by construction alone, it canonicalizes its own
result rather than leaving the caller to notice.

The implementation is `souther.runtime.Normalization.nfc`, one Unicode 18.0.0 NFC shared by every
door — the two ADR-0096 already named, and every `String`-producing standard-library operation —
generated from Unicode 18.0.0's own `UnicodeData.txt` and `CompositionExclusions.txt`
(`bin/GenerateNormalizationTables.java`, checked at generation time against
`DerivedNormalizationProps.txt`'s `Full_Composition_Exclusion`, and against the full
`NormalizationTest.txt` corpus by `bin/VerifyNormalization.java`), the same regeneration discipline
ADR-0119 states for its case tables. Hangul syllable decomposition and composition are algorithmic
(UAX #15), not table lookups — `UnicodeData.txt` states none for them.

Every `String`-producing kernel falls into exactly one of three kinds, and a closed-world test
(`EveryStringProducingKernelPreservesOrEstablishesNfcTest`) derives the population mechanically from
the standard library's own `intrinsic` declarations rather than from a hand-kept list, so a kernel
added later and left unclassified fails there rather than shipping silently non-canonical:

- **Preserves.** `slice` and `trim` read code points `s` already has and create no seam between
  ones that were not already adjacent. Unicode's own guarantee that a substring of a normalized
  string is normalized is what makes this true without help. (`split`, `words`, `lines` and
  `characters` are the same shape but are outside this population: each returns `List<String>`, and
  every element it hands back is one of these substrings.)
- **Intrinsically canonical.** `fromInt` and `fromDecimal` produce ASCII decimal digits, which are
  NFC independent of any input — not because an invariant on the input is preserved, but because
  nothing here reads a code point wide enough to leave it.
- **Must canonicalize.** `append`, `join`, `concat`, `replace`, `reverse`, `repeat`, `lowercase` and
  `uppercase` each canonicalize their own result. `STRING_APPEND` moves off the direct
  `String.concat` dispatch this backend gave it and into the runtime alongside the rest.

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
code points than `pad` itself has. The fill is built by repeating and canonicalizing `pad`, cut to
the code points still needed from its own front; the fill is then joined to `s` and canonicalized
again, because that second seam — where the fill meets `s` — can absorb a code point neither side
had alone. Building the fill one code point wider and re-cutting, as many times as the second seam
costs one, is what keeps the law exact rather than approximate.

## Consequences

`Reserved.name` and a source file's string literal (`AstBuilder`) call `Normalization.nfc` directly
now, not `java.text.Normalizer`, so the two ADR-0096 boundary doors move onto Unicode 18.0.0 with
everything else — they were answering a different, JDK-dependent Unicode version themselves, which
this closes as a side effect of unifying on one implementation rather than as a defect pursued on
its own. A derived decoder's string leaf (`CodecGen.emitStringLeaf`) and the compiler's own
JSON-boundary decoder (`JsonBoundary.text`) stop calling Raoh's `StringDecoder.normalize()` — which
is `java.text.Normalizer` under its own name — and instead lift `Normalization::nfc` through
`Decoder.map`, wrapped back into a `StringDecoder` by `StringDecoder.from` so a constraint chained
after it still resolves. Raoh itself is unchanged. `souther-syntax` — where `Reserved` lives, read by
both the frontend and `souther-fmt`, which cannot depend on `souther-compiler` — gains a compile
dependency on `souther-runtime` for `Normalization.nfc`; `souther-runtime` depends on neither, so the
edge is one-way. `souther-compiler`'s own dependency on `souther-runtime` moves from `provided` to
compile scope: `AstBuilder` and `CodecGen` now call `Normalization.nfc` unconditionally, not only
when a generated `$Ctfe.check` class happens to load.

`Values.equal`, `Map`, `Set` and `==` were already reading `String` as canonical text for whatever
arrived from outside; they now read every `String` that way, which is what makes
`String.append("a", <U+0302>)` and the literal `"â"` the same value everywhere a `String` is
compared, not only when one of them happened to cross a boundary.

`TheRuntimeAnswersEveryKernelAtItsDeclaredAbiTest` loses `STRING_APPEND` from the kernels a JDK
method answers directly, since it now dispatches to `Strings.append` like the rest of the module.
