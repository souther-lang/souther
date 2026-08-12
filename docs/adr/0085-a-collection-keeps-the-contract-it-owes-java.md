# ADR-0085: A collection keeps the contract it owes Java, except where its index decides membership

Status: Accepted.

## Context

Souther's value equality is not always the equality of the Java object carrying the value. A
`Decimal` is carried by a `BigDecimal`, whose `equals` calls 1.0 and 1.00 different; ADR-0009 decided
that scale is not part of a Decimal's identity, so the two disagree. Every other carrier — a String,
a Long, a LocalDate, a generated data class — already answers what the language means.

That single disagreement leaks through anything that asks a value its own equality. A `Set<Decimal>`
held both amounts, a `Map<Decimal, _>` did not find its own key, `[1.0m] == [1m]` was false, and a
`Set<Decimal>` field decoded from a JSON array arrived already holding a duplicate — before a
behavior had run, of a type whose own definition says it has none.

The fix is one definition of sameness that every reader calls. The question this ADR answers is what
that does to `java.util.List`, `Set` and `Map`, which Souther's collections implement so that a value
crosses to Java unchanged (ADR-0008). Those interfaces specify their `equals`: a List compares
elements with the elements' own `equals`, and any List may be on the other side. A collection that
answered the language's question there would be equal to a JDK collection that was not equal back —
`a.equals(b)` true and `b.equals(a)` false.

## Decision

Sameness is defined once, in the runtime, and everything asks it there: the generated `==`, a
generated data's `equals` and `hashCode`, a `fake`'s rows, an `example`'s expected value, and the
collections themselves.

A collection that implements a JDK collection interface keeps that interface's `equals` and
`hashCode` and carries the language's semantics on a separate pair of methods — **except** where its
own index decides membership.

- A `List` compares positionally and has no index. It keeps the `List` contract, and its language
  equality is beside it.
- A `Set` and a `Map` are indexed by the hash of their elements and keys. There is one index and not
  two, so `contains` and `get` answer the language's question and cannot also answer the JDK's;
  `equals` and `hashCode` follow membership rather than being inherited. The alternative is a set
  whose `contains` finds an element and whose hash says it is not there, which is worse than an
  asymmetry against a foreign implementation.
- A type that implements no JDK collection interface — a generated data, a newtype, an `Option`, a
  tuple — compares only with its own kind, so its `equals` is the language's directly.

A probe — `Map.get`, `Map.containsKey`, `Set.member` — reads the container it was given, by the index
that container carries. Every container Souther builds is indexed by the language, and so is the
`Set` a field decodes into. A map a field decodes into is a JDK map, and its keys are the ones a
boundary map may have — a String, a temporal, an enumeration, a newtype over one of those (ADR-0040) —
for every one of which Java's index and the language's agree. So the probe is already answering the
language's question wherever the language can produce the container, and normalizing it first would
cost the whole map on every lookup to buy nothing there. A `java.util.Map` handed in from Java with
some other key is answered by its own index, which is the same thing this ADR already says about
comparing one.

Comparing two containers is a different question and is answered differently: there both sides are
normalized first, because a foreign container is a value being compared rather than an index being
read, and Java's equality being finer than the language's means it may hold two elements the language
calls one. Counted as it stands, both of those would find the same element of the other side and
nothing would notice what the other side has and it does not.

Clojure reached the same place from the same starting point: `clojure.lang.Util/equiv` and
`Util/hasheq` are one definition every collection calls, and `IHashEq` is the parallel hash that
leaves `Object.hashCode` to Java — `(hash 1M)` and `(.hashCode 1M)` disagree there for the reason
they disagree here.

## Consequences

A `Set` or a `Map` Souther built, compared against a foreign `java.util.Set` or `Map` holding the
same amount at another scale, is not symmetric under `equals`. Only Java interop can construct that
pair; a collection Souther built is compared with a collection Souther built. The specification says
so rather than leaving it to be discovered (`[#jvm-collection-equality]`).

A container reached by a route Souther did not build — a list literal is a `List.copyOf`, a decoded
map is a `LinkedHashMap` — is walked by the interface it implements, so both routes give the same
answer and the same hash. Which route a value arrived by is not something a model can see.

The definition is asked once per comparison, which put it on the hot path of every map and set
operation. Two things follow. The carriers that answer for themselves are tested by their exact
class first, so the common key never reaches the rest. And the trie a `Map` is indexed by calls a
key's `hashCode` from its own site rather than through the shared function: routed through the
shared one, that call sees every key type in the program and goes megamorphic. With both, the map
benchmarks are at or slightly better than before this change.

A conformance table names the type constructors rather than the classes implementing them, and asks
each both questions — whether `==` calls two values one, and whether a `Set` built from both holds
one element. The second is the half that goes wrong alone.

## References

- Specification: `[#equality]`, `[#collections]`, `[#jvm-product]`, `[#jvm-collection-equality]`
- Related: ADR-0009 (Decimal does not include scale in identity), ADR-0008 (Java interop is
  asymmetric), ADR-0084 (a tuple is a value that compares by its elements)
