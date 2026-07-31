# ADR-0011: Option, Never, and Unit are not surface-writable types

Status: Accepted for `Never` and `Unit`. Amended (2026-07-28) — where an optional is made is now stated
rather than left implicit, which is what issue #167 found: the compiler had implemented neither half of
it. **Revised for `Option` by ADR-0078 (2026-07-30):** `Option<T>` is writable where a model reads an
optional; what is refused is making one and answering one out of a behavior. The title's claim about
`Option` is what ADR-0078 revises — read that one for the rule in force.

## Context

`Never`, `Unit`, and `Option<T>` are useful as reading concepts, but letting them be written as ordinary types in the surface language raises questions the model does not want to answer — chiefly, how `>->` routing should treat an `Option` in a behavior's output.

## Decision

`Never` and `Unit` are reading concepts, not writable type names. `Option<T>` cannot be written as a type either; it appears only where a `T?` field desugars, as stdlib return types (`List.get` / `Map.get` / `List.find`), and as the argument/result of the `Option` module's functions (`Option.map` / `Option.withDefault`), which consume an inferred `Option` without the caller ever naming the type or building a `Some`. None of the three may appear in a behavior output.

A model makes an optional in one place: a data construction giving a `?` field its value. A plain value written there is wrapped and `None` is the empty one, so the type is made without being named. Everywhere else a model reads an optional and passes it on.

## Consequences

`Never` denotes an impossible case (an empty sum); a single-case output (`-> A`) reads as "the failure row is empty." `Unit` corresponds to the DSL's Unit but is always expressed as a field-less `data`, never as a written type. `Option` cannot appear in a behavior output because "might not be found" as a business result is a domain sum — `-> Member | NoSuchMember` — which reads closer to the DSL than `Option<Member>`. Allowing `Option` in output would also force `>->` routing to decide whether it consumes `Some` / `None` or treats `Option<Member>` as one case; saying it in business vocabulary removes the question.

Making an optional at a construction is a rule about building a data, not a coercion applied wherever two shapes nearly line up, and the two differ in what they permit elsewhere. An expected optional reaches an expression only from a field's own type, since nowhere else in a model can `T?` be written, so no other position can produce one — a lambda handed to a stdlib combinator is typed with no expected type at all. A step for `List.filterMap` therefore still has to answer an optional it read, and absence that is a case of the model's own sum stays a case of that sum, projected to a list of nought or one for `List.concatMap` (issue #166). A coercion would accept a step answering a plain value, and `filterMap` would no longer be the combinator that drops anything. The lift does reach the branches of the value being given to the field, so a field can be given one thing or nothing by a rule; that is the same construction, written conditionally.

`Some(T)` is the one exception to the rule that a sum case carries no payload (see ADR-0013). Because `Option` is built in, users cannot imitate the form. Building a `?` field needs no `constructs`: `Option` is an auxiliary type with no invariant, so closed construction (ADR-0002) has nothing to protect there — and there is no way to write `constructs Some` anyway, since `Option` is not a writable type. The wrapped value is taken out with `match`, positionally: `| Some v` binds `v` to the contained value, as F#'s `Some x` and Elm's `Just x` do (see ADR-0035). `as`, which binds the whole matched value everywhere else, is not used on `Some`.

## References

- Specification: `[#algebraic-types]`, `[#optional]`
- ADR-0002 (closed construction paths), ADR-0013 (sum cases are named-data references)
