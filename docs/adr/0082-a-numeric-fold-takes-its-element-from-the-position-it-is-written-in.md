# ADR-0082: A numeric fold takes its element from the position it is written in

Status: Accepted (decided 2026-08-01).

## Context

`souther.list` declared the two numeric folds over `Int` alone:

```souther
let sum (xs: List<Int>) = List.fold((acc, x) -> acc + x, 0, xs)
let product (xs: List<Int>) = List.fold((acc, x) -> acc * x, 1, xs)
```

A domain whose quantity has a fraction therefore wrote the fold out. `example.attendance` keeps working hours as `Decimal`, because half an hour is an hour anybody works, and each of its four monthly totals is `Hours(List.fold((acc, d) -> acc + f(d).value, 0.0m, days))` with three lines of comment explaining why it is not `List.sum`. `Decimal` is what a rate, a ratio, and anything sold by weight is, by the same argument that makes yen an `Int`.

The neighbouring combinators are already stated over any element their operation makes sense for. `sort` declares `List<'a>` and the compiler admits an ordered element; `max` / `min` / `sortBy` carry the same check. Souther has no type classes, so a constraint of this kind lives in the compiler by construction and not in the signature.

The fold could not be generalised where it was written. `member` generalises because its seed is `false`, which does not depend on the element; `sum`'s seed is `0` or `0.0m`, one of the two numeric types and never both. `souther.decimal` states that there is no implicit widening — `Decimal.fromInt(n) * rate`, F#'s position — so nothing lets a written `0` follow the element. A fold written in the language has to write its seed, and that is what fixed it at `Int`.

## Decision

**`List.sum` and `List.product` are primitives over a numeric element, and the empty list takes its element from the position the call is written in.**

The element MUST be `Int` or `Decimal`, and the answer has the element's type. These are the two types `+` and `*` are defined for; the constraint is checked in the compiler, as `sort`'s ordered-element constraint is.

Over the empty-list literal there is no element to read. The answer is the seed — `sum([]) == 0`, `product([]) == 1`, Elm's rule — and which of the two comes from the position the call is written in: the field it fills, the annotated binding it feeds, the declared output it returns. Written where nothing states that, it is a compile error asking for the annotation.

Choosing `Int` there would be a numeric default rule. Souther has none, and adding one for one library function costs more than the annotation does: `let total: Decimal = List.sum([])` says what the domain meant, and a rule that quietly answers `0` when it meant `0.0m` does not.

**A newtype over `Int` or `Decimal` is not a numeric element.** `data Hours = Decimal` declares no addition and no zero of its own. A list of them is summed by mapping to the wrapped value first:

```souther
List.sum(List.map(h -> h.value, hours))   // typechecks
List.sum(hours)                           // does not
```

This is not the ordered-element rule's shape, and the difference is real. An ordering is a total function of the wrapped value, so a newtype carries it (ADR-0047). An addition is not: the seed is a construction, and a type with an invariant may refuse it. Giving `Hours` a sum means giving the language a way to declare an addition, an identity, and what invariant preservation means for them — a separate type mechanism, not a widening of this constraint.

## Alternatives considered

**`Decimal.sum` / `Decimal.product` beside the `Int` ones.** Two lines in `souther.decimal`, and the abstraction in the wrong module. `sum` is an operation on a list, not on a `Decimal`, and its first argument is not a receiver the qualifier stands for. Every numeric type added later brings another one, and the family drifts from `List.map` / `List.filter` / `List.max`, which are classified by the container they walk.

**`List.sumDecimal`.** The same objection with the overload hand-encoded in the name.

**Defaulting the empty list to `Int`.** Rejected above. It is a language-wide inference rule bought for one call shape.

## Consequences

- The signature is `List.sum : List<'a> -> 'a` with `'a` admitting `Int` and `Decimal`. The call site reads as the operation, with no qualifier stating a type.
- A non-numeric element is now reported against `sum`'s own parameter. It used to surface from inside the expansion — `argument 2: expected Decimal, but got Int`, where argument 2 is the seed of a `List.fold` the source never wrote — with the caret on `List.sum` and a number belonging to a call the reader cannot see.
- The empty list has one new refusal: `let total = List.sum([])` with nothing stating a type. `sum([])` in a field, in an annotated binding, or in a declared output is unchanged.
- `sum` / `product` leave the set of prelude functions derived from `List.fold`. They join `sort`, `reverse` and `range` as primitives, and the reason is the same shape: what they need is not something a fold written in the language can state.

## References
- Specification: `[#stdlib-list]`
- ADR-0047 (a newtype is ordered by the value it wraps — the rule this one deliberately does not follow)
- ADR-0051 (`fold` is not privileged; the derived combinators are ordinary helpers)
- ADR-0053 (where a standard-library function is implemented)
- Issue #241, and finding F32 of souther-lang/souther-examples
