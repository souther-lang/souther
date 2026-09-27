# ADR-0096: A string is measured in Unicode code points, and arrives canonical

Status: Accepted. Revised 2026-09-26 and 2026-09-27 — see *Revision*.

## Revision (2026-09-27, who owns the bound)

The Revision below keeps one decision and replaces another. Kept: whether text has a place is part
of whether it is a `String`, so every `String` has one and no operation over a `String` the program
holds can end for want of a place. Replaced: the bound is no longer the carrier's. It is the
language's, and `[#what-a-string-holds]` states it.

A `String` holds at most 2^28 − 1 code points, counted in what `String.length` counts. The bound
was the carrier's, in the units the carrier keeps text in, and that made the language's own value
domain depend on a host's array limit. Every carrier that was not the JVM had two choices: declare
its own bound, so that a program ended in one place on one carrier and in another on the next, or
copy the JVM's number, so that the language's answer was a JVM constant by another route. The second
is what the native compiler did. A carrier now represents a `String` of that length or is not an
implementation of the language; that is the same rule that keeps `Int` 64 bits wide wherever it is
carried.

Two refusals are kept apart. Text or an answer past the bound has no place, and that is a refusal
of the language, said the same on every carrier. A `String` within the bound that the host cannot
allocate is the host's resource failing, like a `String` of one character when the heap is full; it
is not an answer with no place, and the language does not promise against it.

What is bounded is a `String` and not the numbers an operation is given. `repeat(n, "")` builds
nothing for any `n`, and a pad that is empty, or a `String` already as wide as the width, builds
nothing for any width. `repeat` and the pads refuse where what they would build is past the bound,
before they build it.

Why 2^28 − 1 and not another number. The value is a choice and is not derived from a host. The
constraints it has to meet are these. It has to be well inside what the JVM holds in one array in
either of its encodings even when every code point is outside the basic plane, which takes two
units, so that whether a text has a place never depends on which characters it holds or on how the
JVM was started; the largest bound that meets that is 2^29 − 3, and choosing it would make the
language's number the JVM's again. It has to be below the largest `Int` a host
array index takes, so that a count that passes the check narrows without loss. And it should be a
number no domain text comes near: two hundred and sixty-eight million code points is far past any
name, code or message this language writes. It is a power of two less one, so it can be said and
checked without a table. Because it is now a value of the language, changing it changes what a
program answers. Raising it turns an abort into an answer and lowers no program that answered;
lowering it aborts programs that answered. The change is an ADR, and `Strings.LONGEST_TEXT` and the
specification move together, which `TheStringBoundTheSpecificationStatesIsTheOneTheRuntimeHoldsTest`
holds.

## Revision (2026-09-27)

The bound this Revision speaks of as the carrier's is the language's now; see the Revision above.

Admission decided whether text is a sequence of scalar values and canonical, and stopped there. A
`String` also holds no more text than the carrier declares one to hold
(`[#what-a-string-holds]`), and that was asked only of the operations that build one. The bound is
what a carrier declares a `String` to hold and not what its own representation of text could, so
text can arrive that the host holds and the carrier declares no `String` to. A `java.lang.String` in
the narrower encoding can be longer than the JVM declares, and a carrier that counts lengths in more
bits can be handed a great deal more. Kept, that text would make `append("", s)` end for want of a
place on a `String` the program already holds, and a `String` would not be an identity for the
operation that is defined over it.

Whether text has a place is now part of whether it is a `String`. Admission answers one of three:
the text as the canonical `String` it is, text that is not scalar values, or text whose canonical
value has no place. It is the canonical value that is measured, since that is the `String` the text
would be, and the canonicalizing is itself bounded, so text that cannot be one is not built out to
find that out. A derived decoder reports the second and the third at the path with the same Raoh
code, `invalid_format`, each with its own message; a crossing from Java aborts; a literal is a
diagnostic. The doors still differ in how they say no and not in what they refuse. Operations that
build a `String` keep their own bound, which is what lets them refuse before building.

## Revision (2026-09-26)

The Decision below says counting in code points makes a broken string unreachable, and that holds
only of what a `String` was to begin with. `slice` and the rest cannot cut a pair in two, but a
`java.lang.String` can hold half of one before any operation touches it, and this ADR let such text
in wherever text arrived: `Normalization.nfc` passes a lone surrogate through as it is. So an
operation over code points was answering about a value that was not text.

A `String` is now a sequence of Unicode scalar values (`[#a-string-is-a-sequence-of-scalar-values]`),
and the doors this ADR canonicalizes at are the doors that refuse text holding half a pair
(`[#a-string-holds-no-half-of-a-surrogate-pair]`). That is what makes the laws below hold of every
`String`: none holds half a pair, so no operation over code points answers with one. `<` now counts
in the same unit as the operations here (`[#a-string-is-ordered-by-scalar-value]`).

## Context

The naming audit behind ADR-0095 asked what `String.substring`'s `to` bound meant, and the answer
turned out to be about units rather than about names. The String module was measuring in two
different units at once:

| Operation | Unit it used |
| --- | --- |
| `length` | UTF-16 code unit (Java's `String.length()`) |
| `substring` | UTF-16 index (Java's `String.substring`) |
| `padLeft` / `padRight` | UTF-16 (`n - s.length()` decided the fill) |
| `toChars` | code point |
| `reverse` | code point (`StringBuilder.reverse` keeps surrogate pairs) |

So for `𠮷` — one character, two UTF-16 units — `String.length` answered `2` while
`List.length(String.toChars(s))` answered `1`, and `substring(0, 1, s)` answered a lone high
surrogate: a `String` value that is not any text.

This is not a rare shape in the domains Souther is for. `𠮷田`, `髙橋`, an emoji in a remarks field are
ordinary Japanese business data. An `invariant String.length(value) <= 20` on a name field admitted a
different number of characters depending on which characters they were.

The boundary made it worse. A derived decoder lowers a length invariant to Raoh's
`StringDecoder.minLength` / `maxLength` / `fixedLength`, and those counted `value.length()` — UTF-16.
So one invariant had two answers: the model's and the decoder's, with the decoder's being the one a
caller sees, as a `too_long` business failure on a value the model accepts.

## Decision

**The String API defines its lengths and indices in Unicode code points. The UTF-16 code unit is the
JVM backend's representation and does not reach the language.**

In scope — every one of these counts code points:

```
length  slice  characters  codePoints  reverse  padLeft  padRight
```

Out of scope, and deliberately a different question: grapheme clusters, display cell width, byte
length, UTF-16 unit count. A base letter with a combining accent is two code points; a family emoji
joined with zero-width joiners is several. `String.length` does not answer what a reader counts, and
a function that does would be named for what it counts.

The laws this makes true are what the choice is for:

```
String.length(s) == List.length(String.characters(s))
String.length(s) == List.length(String.codePoints(s))
String.slice(0, String.length(s), s) == s
String.codePoints(String.reverse(s)) == List.reverse(String.codePoints(s))
String.length(String.padLeft(width, pad, s)) == Int.max(width, String.length(s))   // non-empty pad
```

`slice` converts both code-point indices to UTF-16 offsets with `offsetByCodePoints` before cutting,
so no result holds half a surrogate pair. An index the string has not got, or a `toExclusive` before
`fromInclusive`, aborts — a model bug, treated as `IntMath` treats an overflow.

`padLeft`/`padRight` repeat `pad` and cut it to the code points still needed, so the width is exact
rather than a whole number of copies and `pad` need not be one character. An empty `pad` fills
nothing and returns the string, the one input the width law does not hold for; nothing can be
repeated into a width.

### Raoh counts the same way

`net.unit8.raoh` was changed rather than worked around: `StringDecoder`'s `minLength`, `maxLength` and
`fixedLength` count code points, in the check and in the `actual` they report. It is a defect there on
its own terms — a `maxLength` on a name field should not depend on which characters the name has —
and fixing it at the source means the bound in the invariant and the bound at the boundary are one
number in one unit, with no translation layer in the middle. `nonBlank` is unchanged: it asks about
whitespace, not about length. The internal caps that guard the email/URL/IP regexes are unchanged
too; they bound work, not domain values.

This makes souther depend on raoh 0.7.0.

### Text that arrives is canonical

Counting code points fixes the unit and leaves a second way the same text can be two values.
Unicode calls `が` written as one code point and as か plus a combining mark *canonically
equivalent* — the same text. Souther compares strings by their code units, so it calls them
different: two `Map` keys, two `Set` members, `==` false, and a length bound that still depends on
who typed the value. macOS filenames, some clipboard paths and some IMEs deliver the decomposed
form.

`Values.equal` already carries the shape of this problem, with a comment saying so: `BigDecimal`
has an arm of its own because "Java's equality is finer than the language's". `String` is the second
case and nobody had noticed.

**Text that arrives from outside is canonicalized to NFC.** There are two places it arrives, and each
has one place that does it:

- A derived decoder, at the string leaf. Every leaf comes from one method, so a field, a newtype's
  base, a map's key, a list or set element, a sum's discriminator and an enumeration's name are all
  the same path, and a constraint chained after it — a length bound, a pattern — sees the canonical
  form. Writing the normalization at each site instead was the first attempt and it left four paths
  behind, found one at a time in review.
- A **name**, wherever one enters. Not only an identifier in a source file: a type variable, the
  module name a header-less source is given, the file stem the CLI derives one from, and the
  identifiers an invocation names (`--behavior`, `--module`). They all go through one function,
  `Reserved.name`.

  Names matter because a name is compared by its code units wherever it is looked up — a declaration
  against a reference, a case against a wire tag, an argument against what a module declares — and
  because a name becomes text at a boundary: a case name is a wire tag. Canonicalizing the tag where
  it was emitted, and leaving the name alone, was the second wrong answer: two cases that no reader
  can tell apart stayed two names in the compiler and became one tag on the wire, so the second was
  unreachable from outside. Canonicalizing the identifier and not the other four doors was the third:
  the same file was one module on a machine that delivers composed names and `main` on one that does
  not, because the stem was judged for being a usable identifier before it was canonicalized.

  It is one function rather than a rule to remember at each door, which is what those two rounds
  bought. And it is applied as the tree is built rather than to the source text, because normalizing
  before lexing would shorten a line and move every position after it, so a diagnostic's caret would
  start at the wrong column of the file the author is reading.

  Starting in the right place is only half of it, and the first version of this got the other half
  wrong. Canonicalizing as the tree is built put the canonical name where the spelling had been, and
  a name carries two answers that are not each other's: which name is this, and which characters
  spell it here. A decomposed name is wider than the composed name it denotes, so everything measured
  in the name came out short — a caret stopping mid-word, a rename leaving the combining marks behind,
  a cursor on the last character answered about nothing — and an editor matching a declaration to a
  reference by comparing the two spellings answered no for two spellings of one name. So a name in
  the tree is an occurrence, `WrittenName`, holding the canonical name, the characters the source
  spells it with, and where they are; the invariant that they are a name and a spelling of that name
  is checked where one is made. Every question about identity reads the name and every question
  about the file reads the spelling, and neither is recovered from the other.

  Two names that are one name are then one name to every check that was already there — a duplicate
  declaration, a case listed twice in a sum — so none of those needed a rule of its own.

The fix is that *values are canonical*, not that comparison ignores the difference. Normalizing
inside `Values.equal` was considered and refused: `String.length`, `characters` and `slice` all see
the normalization form, so a comparison that ignored it would leave two values that compare equal
answering different lengths — a worse incoherence than the one it closes. `Decimal` can be compared
by amount because ADR-0094 removed the last operation that could observe scale; normalization form
has several, so it has to be settled in the value.

NFC and not NFKC. Compatibility folding turns ① into 1 and a half-width kana into a full-width one,
which is a different claim about the text than "these are the same characters" — right for a search
key, wrong for a stored name. If a domain wants it, that is a per-type decision and not a boundary
default.

This does not close everything, and does not claim to. A variation sequence — 葛 followed by
U+E0101 — is stable under every normalization form and stays two code points. Grapheme clusters are
untouched. And a string built inside the domain can still leave NFC: `characters` of a string that
contains a combining mark, reassembled, is whatever it was. The two boundaries are where foreign
text enters, which is where the problem comes from.

## Consequences

`String.length` is O(n) rather than a field read. That is the price and it is the smaller half of the
trade: what the change actually buys is that no operation the language publishes can produce a broken
string, which is an abstraction boundary rather than a constant factor. A domain that needs a length
in a hot loop can hold it in a binding.

An `invariant String.length(value) <= 20` now means twenty code points everywhere — in the model, in
the derived decoder, and in the `actual` a `too_long` failure reports. A model that was relying on the
UTF-16 count to bound a database column's byte width was relying on a coincidence; a byte-width
constraint is a different constraint and needs a different function.

At a JVM interop boundary, a caller converting between a Souther index and a Java `String` index has
to convert units. Nothing in the language does that implicitly.

A decoder now transforms as well as validates, which it did not before — no derived decoder emitted
`trim` or `lowercase`, and this is the first. What a decoder answers is therefore not always byte-for-byte
what arrived. Anything that needs the bytes as sent — a signature over the raw payload, a record of
what was received — holds them outside the decoder, which is where it already had to hold them.
Encoding a decoded value gives the canonical form, so the round trip is idempotent rather than the
identity; ADR-0094's law is that equal values write the same JSON, and canonicalizing serves it.

`AStringIsMeasuredInCodePointsTest` covers the laws over ASCII, BMP Japanese, a supplementary-plane
kanji, a variation sequence, a ZWJ emoji and the empty string, plus the abort cases for an index out
of range. `AStringIsCanonicalAtTheBoundaryTest` covers the canonicalizing half — including the
premise, that the two forms really are different strings to the JVM, so the rest of it cannot pass
by accident. `CompileInvariantConstraintTest` covers the one that spans the two repositories: a
two-code-point value under a bound of two decodes, and a three-code-point one fails with `actual` of
three.

The name half is covered from both ends, because either end alone passes while the other is wrong.
`ANameIsCanonicalWhereverItEntersTest` drives each door — an identifier, a type variable, a
header-less source's module name, a file stem, and the three an invocation names — rather than
describing them, since a door is one line in an argument parser and a line is what gets deleted by
someone who cannot see what it is for. `ANameKeepsTheSpellingItWasWrittenWithTest` and
`AReportUnderlinesWhatTheAuthorTypedTest` cover the other end: a composed reference reaching a
decomposed declaration, a rename that leaves no combining mark, a cursor on the last unit of a name
three units wide, a report quoting what was typed, and a qualified name whose last segment is the
only part a rename rewrites.
