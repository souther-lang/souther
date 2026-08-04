# ADR-0009: Decimal does not include scale in identity

Status: Accepted (the Consequences below said an Encoder emits the scale it read; ADR-0094 reversed
that half — a boundary writes the amount — because keeping the scale meant two equal values wrote
two ways. The decision itself, that scale is no part of identity, is unchanged and is what makes the
reversal safe)

## Context

`Decimal` maps to `java.math.BigDecimal`. The same amount arrives through different paths
with different scales — read from a DB column it is `1.00`, from JSON it is `1.0`. Scale
records *how the number was written*, not *how much it is*. If identity took scale into
account, equality would depend on which path a value entered through.

## Decision

`Decimal` ignores scale in identity: `1.0` and `1.00` are equal. Equality compares data
fields recursively, and the `Decimal` comparison at the leaves ignores scale. The
`hashCode` of any data containing a `Decimal` strips trailing zeros
(`stripTrailingZeros`) before hashing, so equality and hashing agree.

## Consequences

Scale is not lost from the value: it is carried, and Java reading the value sees it. What a boundary
*writes* is the amount (ADR-0094) — `1.50` goes out as `1.5` — and the round-trip
`decode(encode(v)) == v` (`[#round-trip]`) still holds, by the same argument that lets identity drop
scale. Equal values therefore write the same JSON (`[#encode-law]`). If rounding precision is a
domain concern, model it as an invariant or a separate field rather than leaning on incidental
`Decimal` scale — advice that was here from the start and is now the only thing that works, since
the digits a rounding call produced are not what crossing the boundary shows.

Both sides must be fixed together. If only equality were made scale-insensitive and
`hashCode` were left alone, `1.0` and `1.00` would land in different buckets and break the
moment such data became a `Map` key. Groovy made `==` value-based but left `hashCode`
alone; the report GROOVY-2334 (2007) is still open. Clojure aligned equality and hash in
one fix, CLJ-1118.

Prior art converges on ignoring scale in value identity: Clojure (1.6 changed
`BigDecimal.equals` to `compareTo`), Scala (`scala.math.BigDecimal`), Ceylon, and — off
the JVM — Python and C#. The C# documentation states the tradeoff outright: *trailing
zeros do not affect the value ... however, trailing zeros might be revealed by the
ToString method*.

Note that `java.math.BigDecimal.equals` compares scale, so Souther does not follow it. The
generated data class implements `equals`/`hashCode` from all fields (value-based), which
is distinct from both Java's `==` (reference comparison) and `BigDecimal.equals`
(scale-sensitive). This value equality also holds when the data is viewed from Java, so it
works directly as a `Map` key (`[#jvm-product]`).

## References

- Specification: `[#primitives]`, `[#round-trip]`, `[#jvm-product]`
- Clojure CLJ-1118; Groovy GROOVY-2334 (2007); Scala `scala.math.BigDecimal`; Ceylon; C# / Python `Decimal`
