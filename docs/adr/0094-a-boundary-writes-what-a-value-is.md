# ADR-0094: A boundary writes what a value is, not how it was built or written

Status: Accepted

## Context

A `Set` and a `Map` cross the boundary as a JSON array and a JSON object, and something has to
decide what order the members are written in. Until now nothing did: the encoder walked whatever the
runtime handed it, and #299 removed the specification's claim that equal collections write alike,
because they do not.

Three separate mechanisms make what is written follow the history of the collection rather than the
collection:

- **A hash-collision bucket holds its members in the order they were put.** `HashCollisionNode`
  appends on insert and the iterator walks that array. `ValueClassGen` folds `hashCode` over the
  fields from `1`, and a unit data has no fields, so *every* unit data in a program hashes to `1` —
  which puts every `Set` of two or more enumeration cases in one bucket.
- **A decoded `Map` was never a trie.** The decoders leave the map the decode produced, and only
  `insert` / `remove` rebuild it into one. Worse than "the document's order": the map a decode leaves
  is a `java.util.ImmutableCollections$MapN`, whose iteration order is randomised per JVM by that
  class's `SALT`. The same program, given the same request, does not answer with the same bytes
  twice.
- **`Decimal` keeps the scale it was read with.** `1.0` and `1.00` are one amount (ADR-0009) and two
  numbers on the wire.

An author who assumes a response body is a function of the answer gets one most of the time. It
reaches golden tests, response diffs, cache keys, ETags and content addressing.

## Decision

**Equal values write the same JSON at a given boundary position**, and two things are settled on the
way out to make it so.

The position is part of it. A boundary position declares a type and that declaration fixes one
derived Encoder; a case value equals itself at both its own type and at its sum's, and the two write
it differently, because a case's Encoder writes no discriminator and its sum's writes one. So the law
is about one declared type at a time — `E.encode(a) == E.encode(b)` for equal `a` and `b` — and not
about a value having one representation wherever it appears. Both sides of that are already pinned by
`RunnerTest`, which drives a behavior declaring a case and one declaring the sum.

**A `Decimal` is written as its amount.** `1.50` goes out as `1.5`, `100.00` as `100`. Scale records
how a number was written, which ADR-0009 already decided is no part of what it is; keeping it at the
boundary meant two equal values wrote two ways, and no ordering could reach that — `1.0` and `1.00`
are one member of a `Set` by the time an encoder sees it, and which of the two the set kept was
decided by whichever arrived first.

Spelling the amount out is bounded, and has to be. An exponent is what lets a caller name a large
amount without paying for it: `1E+1000000` is eleven characters and a million and one digits, so a
boundary that always spelt out would let a small input ask for an arbitrarily large one. An exponent
is therefore spelt out into at most a thousand digits and otherwise written as it stands.

What that bounds is the *expansion*, not the output. A value that already carries a thousand
significant digits is written with all of them — no rule here shortens what a value is — and a sign
is not a digit, so `-1E+999` is spelt out as 1001 characters. A thousand is also where a reader gives
up (`jackson-core`'s `StreamReadConstraints.DEFAULT_MAX_NUM_LEN`), which is where the figure came
from, but that is a reference point rather than the definition: that limit is per-factory and
configurable, and what a boundary writes is part of the language.

The bound falls on the amount and not on the value that carried it, which is what keeps the form a
function of the amount: `1E+1000000` and `10E+999999` reach the same side of it.

`stripTrailingZeros` is not by itself the fewest digits an amount can be carried by, because a scale
is an `int` with an end: taking the zero off `(10, MIN_VALUE)` asks for a scale the type cannot say
and it throws. Stopping at the floor keeps one form per amount — `(10, MIN_VALUE)` and
`(100, MIN_VALUE + 1)` are one amount and both stop at `(10, MIN_VALUE)` — because fixing the scale
fixes the digits. An Encoder is total over the values it is given (`[#encoder]`), so this is not an
edge case to be left throwing: a `Decimal` is whatever Java handed the model, and Java can hand it
either end of the scale.

**A collection's members are written in ascending order of their external representations.** A
`Set`'s array is ordered by each member's own representation; a boundary `Map`'s object by its
rendered keys. The order over representations is:

```
null < false < true < number < string < array < object
  number : by amount — an amount is written one way, so two of one amount are one number
  string : by UTF-16 code unit
  array  : element by element, the shorter one first where one runs out
  object : its members read in ascending key order, each key before its value
```

Four things follow, and each is the reason for a choice that could have gone otherwise.

**Representations, not values.** #328 rejected sorting because a `Set`'s element is only required to
answer *equality* — `TypeOps.isOrdered` gives an ordering to five primitives, ordered newtypes and
enumerations, and to nothing else — so ordering only where an ordering exists would make the wire
format depend on the element type. Ordering by the representation answers that: having an external
representation is what being a boundary type *means*, so it is defined for every member a boundary
can carry, and no total order over Souther values has to be invented.

**Comparing answers zero exactly when two representations are the same.** This is what makes the
order remove construction history rather than merely reduce it: any pair a comparison cannot separate
would keep whatever order the trie gave. The comparison keeps a tie-break on the written form of a
number for that reason, though the encoders now hand it only amounts and so never reach it — it is
what leaves the order total for any pair it is given rather than only for the ones it expects.

**An object's member order does not count towards that sameness**, and the comparison reads members
in key order. A comparison used to decide an order must not depend on the order it is given. Under
the generated encoders the two coincide anyway — a data's members are in declaration order, a map's
in key order — so representations this calls the same are also byte for byte the same.

**UTF-16 code unit order for strings.** It is the order the language's own `<` on a `String` already
uses (`String.compareTo`), and the one RFC 8785 (JCS) settled on. Unicode code point order differs
for characters outside the BMP, so one of the two had to be written down.

## Consequences

The law is now stated (`[#encode-law]`), which #327 asked for and #328 could not give. It is stated
about the *derived* Encoders: a custom one is written by hand and is bound by nothing here.

The order is applied where the type is still known — the four `Set`/`Map` arms of `CodecGen` and the
two top-level arms of `Runner` — and not once over the finished tree. After encoding, a `Set` and a
`List` are both a `java.util.List`, and only one of them may be reordered. `Representations` in
`souther-runtime` holds the order itself, and refuses a carrier outside the closed set the encoders
emit (`String`, `Long`, `Boolean`, `BigDecimal`, `List`, `Map`, `null`) rather than giving it some
order, because a silently wrong order is the failure that would not be noticed.

The order is paid for per encode of a `Set` or a `Map`. What it costs is dominated by the members
that are objects, because comparing two of those reads both in key order: sorting a shuffled
`Set<Data>` of six-field members takes about 52 µs at 100 members and 1.0 ms at 1000, against 12 µs
and 180 µs for a `Set<String>` of the same size. The key order a member is read in is worked out once
per sort rather than once per comparison — a sort asks about the same member O(log n) times — which
is what brings the object case down from 143 µs and 2.3 ms.

That list is the *boundary*, and it is not everywhere a collection is shown to somebody. A diagnostic
that prints a live value — `FixtureReader.showAny`, which renders the actual and expected sides of an
example mismatch — walks the collection itself, and so still shows a decoded map in the per-JVM order
above. It is not the wire and no contract is stated about it, but it is the same defect in a place
this decision does not reach: what it holds are Souther values, which may be tuples, and a tuple has
no representation to be ordered by. Closing it needs something other than this order.

The boundary's order is now specified and `Set.toList`'s is still not. They were one order before and
are two now, which is the price of specifying the one that can be specified: only what is written has
a representation to be ordered by, and a `Set` inside a behavior body may hold a tuple, which has
none (ADR-0036).

**What writing the amount costs.** A rounding call's digits stop being visible on the wire: a rate
rounded to two places is written `86.4`, not `86.40`. A money API that showed two decimal places by
rounding to two decimal places must now say so in the model — which is what ADR-0009 advised from the
start ("model it as an invariant or a separate field rather than leaning on incidental `Decimal`
scale"), and is now the only thing that works. The scale is still on the value, so Java reading it
sees it and a test may assert it there; it is the *boundary* that stops showing it.

That price bought the law. Ordering alone could not: a `Set` holds one member per equality class and
which of `1.0` and `1.00` it kept was decided by whichever was inserted first, so two `==` sets went
out as two byte sequences however carefully the members were ordered. Leaving that as "unspecified"
was the alternative, and it would have left #327's own sentence — equal `Set` values can encode
differently — true at the end of the issue that reports it.

**Which member a `Set` keeps is still not specified**, and now nothing at the boundary depends on it:
the two write the same. `Set.toList` hands back the one the set kept, so a program reading a scale off
that is reading something the language does not decide. Writing "the first inserted" down would give a
`Set` an insertion-order semantics it does not otherwise have.

## References

- Specification: `[#encode-law]`, `[#primitives]`, `[#collections]`, `[#stdlib-set]`, `[#stdlib-map]`
- ADR-0039 (a `Set`'s external representation), ADR-0040 (what a boundary map key may be),
  ADR-0009 (`Decimal` ignores scale), ADR-0036 (a tuple has no external representation)
- Issues #299 (the order was unstated), #327 (equal collections encoded differently); RFC 8785 (JCS)
