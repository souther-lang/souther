# ADR-0084: A tuple is a value that compares by its elements

Status: Accepted.

## Context

ADR-0036 added tuples as expression-level first-class values, carried at runtime as an `Object[]`.
An array's `equals` is reference identity, so two tuples built from the same values were not the same
tuple. The language never said they were not: the equality rule (`[#equality]`) listed primitives,
data, sums, `List`, `Map` and `Option` and did not mention tuples, and the checker's equality
predicate admitted anything that was not a function — so a tuple reached `==`, a `Set`'s element and
a `Map`'s key, and each answered by identity.

What that costs shows up where a model states a rule. A composite uniqueness rule is the natural
thing to want — one row per `(from, event)` — and `allUniqueBy` takes a single projection, so a
tuple is what a modeller reaches for:

```
data Machine = { transitions: List<Transition> }
    invariant deterministic = List.allUniqueBy(t -> (t.from, t.event), transitions)
```

This compiled and then never rejected anything. An invariant is the one place a model states a rule
and expects it enforced, and this one held of every input, including the ones it was written to
exclude. Nothing was reported.

The alternative a modeller has without tuples is joining the parts into a `String`, which makes the
separator the model's problem: `"a/b" ++ "/" ++ "c"` and `"a" ++ "/" ++ "b/c"` collide, and two
distinct keys are reported as a duplicate.

## Decision

A tuple compares by its elements, left to right, and is a value like any other: an operand of `==`, a
`Set`'s element, a `Map`'s key. It has no ordering — `sort` and a `sortBy` key still refuse one — and
it still has no external form, so it is still refused at a data field and a behavior's input and
output. F# and Elm both give tuples structural equality without ordering being implied, which is the
ground Souther's surface takes (ADR-0028).

At runtime a tuple is a value of its own class rather than an `Object[]`. Giving `Values` an arm for
arrays would have made the language's own answers right at no cost, because every Souther-visible
comparison already routes through it — but a tuple's `equals` would have stayed identity, and the
next reader written without that knowledge would be silently wrong in exactly the way this ADR
exists to end.

## Consequences

A tuple answers what it is, so no reader has to know anything to get it right, and there is no route
by which the old answer can return.

It costs a construction. A pair is the same size as the two-element array it replaced and allocates
no more often, and an isolated benchmark times the two the same — but building it is a call where an
array was an instruction, and an inlined call spends the caller's inlining budget. In the walks that
fold a tuple accumulator — `partition`, `take`, `drop`, `indexedMap`, `distinct`, `zip` — that budget
was what `PersistentVector.append` was being inlined on, and it no longer is. Measured interleaved
against the previous representation over three runs, those walks cost about 11% more per element
(`parted` 7.85 → 8.71 ns/element); every other benchmark is unchanged. On this JVM there is no way to
have a named value without the call. The `run` benchmark gained the row that measures it.

The pair has a class of its own and `Tuple` is an interface rather than a base class, so that
constructor chains straight to `Object`'s; the generated code names the pair and reads its fields
rather than indexing. Wider tuples, which no combinator folds, carry an array.

Because a tuple now supports equality honestly, the checker's capability table answers `equality` for
it as it always did, and the two now agree.

## References

- Specification: `[#tuple]`, `[#equality]`, `[#stdlib-list]`
- Related: ADR-0036 (tuples are expression-level first-class values), ADR-0009 (Decimal does not
  include scale in identity), ADR-0085 (a collection keeps the contract it owes Java)
