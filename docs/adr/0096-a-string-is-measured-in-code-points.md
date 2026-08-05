# ADR-0096: A string is measured in Unicode code points, and arrives canonical

Status: Accepted

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

**Text that arrives from outside is canonicalized to NFC.** There are two places it arrives, and both
do it:

- A derived decoder normalizes at the string leaf, before any constraint chained after it. A length
  bound, a pattern, a fixed length all see the canonical form.
- A string literal in a `.sou` file is normalized when it is read. A source file is bytes from an
  editor, and which form an editor writes is not something the author chose. Without this a pattern
  written in one form would not match a value that arrived in the other.

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
