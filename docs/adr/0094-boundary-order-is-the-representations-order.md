# ADR-0094: A boundary orders a collection by its members' representations, not by their values

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

**A boundary writes a collection's members in ascending order of their external representations.** A
`Set`'s array is ordered by each member's own representation; a boundary `Map`'s object by its
rendered keys. The order over representations is:

```
null < false < true < number < string < array < object
  number : by amount; two of one amount by the form each is written in, as a string
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
would keep whatever order the trie gave. It is why numbers that are one amount are then separated by
the form they are written in, and why `1`, `1.0` and `1.00` are three numbers here while being one
`Decimal`.

**An object's member order does not count towards that sameness**, and the comparison reads members
in key order. A comparison used to decide an order must not depend on the order it is given. Under
the generated encoders the two coincide anyway — a data's members are in declaration order, a map's
in key order — so representations this calls the same are also byte for byte the same.

**UTF-16 code unit order for strings.** It is the order the language's own `<` on a `String` already
uses (`String.compareTo`), and the one RFC 8785 (JCS) settled on. Unicode code point order differs
for characters outside the BMP, so one of the two had to be written down.

## Consequences

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

**Two things this deliberately does not do.**

It does not add a law relating `==` to `encode`. `a == b` implying `encode(a) == encode(b)` is a
statement about every value type the language will ever have, and what was implemented and verified
here is two rules about two collections. That the wire stops depending on construction history is a
consequence of those rules, not a general property to be promised.

It does not fix which member a `Set` keeps. Where two equal elements are written differently — today
only `Decimal`s differing in scale — equality says they are one member and the set keeps one of them.
No ordering can reach this: there is one member by the time the encoder sees it. The implementation
currently keeps the first one inserted, and the specification says the choice is *unspecified*
instead, because writing "first" down would give a `Set` an insertion-order semantics it does not
otherwise have. Normalising the scale was the alternative and is worse: an Encoder emits the scale it
read (ADR-0009), and a `1.50` that is written `1.5` is a regression for the money field that reads it.

## References

- Specification: `[#collections]`, `[#stdlib-set]`, `[#stdlib-map]`
- ADR-0039 (a `Set`'s external representation), ADR-0040 (what a boundary map key may be),
  ADR-0009 (`Decimal` ignores scale), ADR-0036 (a tuple has no external representation)
- Issues #299 (the order was unstated), #327 (equal collections encoded differently); RFC 8785 (JCS)
