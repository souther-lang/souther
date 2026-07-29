# ADR-0011: Option, Never, and Unit are not surface-writable types

Status: Accepted. Amended twice. (2026-07-28) Where an optional is made is now stated rather than left
implicit, which is what issue #167 found: the compiler had implemented neither half of it. (2026-07-30)
`Option<T>` is writable where an optional is read; what is refused is making one and answering one —
see *What "not a surface type" turned out to mean* below (issue #202).

## Context

`Never`, `Unit`, and `Option<T>` are useful as reading concepts, but letting them be written as ordinary types in the surface language raises questions the model does not want to answer — chiefly, how `>->` routing should treat an `Option` in a behavior's output.

## Decision

`Never` and `Unit` are reading concepts, not writable type names. `Option<T>` cannot be written as a type either; it appears only where a `T?` field desugars, as stdlib return types (`List.get` / `Map.get` / `List.find`), and as the argument/result of the `Option` module's functions (`Option.map` / `Option.withDefault`), which consume an inferred `Option` without the caller ever naming the type or building a `Some`. None of the three may appear in a behavior output.

A model makes an optional in one place: a data construction giving a `?` field its value. A plain value written there is wrapped and `None` is the empty one, so the type is made without being named. Everywhere else a model reads an optional and passes it on.

## Consequences

`Never` denotes an impossible case (an empty sum); a single-case output (`-> A`) reads as "the failure row is empty." `Unit` corresponds to the DSL's 単位型 but is always expressed as a field-less `data`, never as a written type. `Option` cannot appear in a behavior output because "might not be found" as a business result is a domain sum — `-> 会員 | 会員なし` — which reads closer to the DSL than `Option<会員>`. Allowing `Option` in output would also force `>->` routing to decide whether it consumes `Some` / `None` or treats `Option<会員>` as one case; saying it in business vocabulary removes the question.

Making an optional at a construction is a rule about building a data, not a coercion applied wherever two shapes nearly line up, and the two differ in what they permit elsewhere. An expected optional reaches an expression only from a field's own type, since nowhere else in a model can `T?` be written, so no other position can produce one — a lambda handed to a stdlib combinator is typed with no expected type at all. A step for `List.filterMap` therefore still has to answer an optional it read, and absence that is a case of the model's own sum stays a case of that sum, projected to a list of nought or one for `List.concatMap` (issue #166). A coercion would accept a step answering a plain value, and `filterMap` would no longer be the combinator that drops anything. The lift does reach the branches of the value being given to the field, so a field can be given one thing or nothing by a rule; that is the same construction, written conditionally.

`Some(T)` is the one exception to the rule that a sum case carries no payload (see ADR-0013). Because `Option` is built in, users cannot imitate the form. Building a `?` field needs no `constructs`: `Option` is an auxiliary type with no invariant, so closed construction (ADR-0002) has nothing to protect there — and there is no way to write `constructs Some` anyway, since `Option` is not a writable type. The wrapped value is taken out with `match`, positionally: `| Some v` binds `v` to the contained value, as F#'s `Some x` and Elm's `Just x` do (see ADR-0035). `as`, which binds the whole matched value everywhere else, is not used on `Some`.

## References

- Specification: `[#algebraic-types]`, `[#optional]`
- ADR-0002 (closed construction paths), ADR-0013 (sum cases are named-data references)

## What "not a surface type" turned out to mean (2026-07-30)

The rule was enforced on two spellings — `T?` and `Some(...)` — and not on the type. `Option` sits in
`TypeOps.denoted` beside `List`, `Set` and `Map`, so a model reached the same type by naming it, and
issue #202 asked what that had cost.

Measured on `develop`, naming it reached six positions. Five of them are the reading this ADR already
permits, written instead of inferred: a data field (where `T?` means the same type), a behavior's
input, a helper's parameter, a helper's declared return, and a function type's result. Two of those
*cannot* be written any other way, because the annotation is mandatory there: a recursive helper's
return type, and a function-typed parameter (spec 13.1) — so a `List.filterMap`-shaped combinator a
user writes has no way to say what its step answers. Refusing the name would remove those programs
rather than a second spelling of an existing one.

The sixth was the leak: `let p: Option<Int> = None` made an optional outside a construction, because
`None` was accepted wherever the expected type was an optional — a test this ADR's own reasoning
licensed ("an expected optional reaches an expression only from a field's own type, since nowhere else
in a model can `T?` be written"). Naming the type is another way to expect one, so the test stopped
meaning what it was written to mean. A helper's declared optional return leaked the same way in one
position and not another: `| None -> None` inside such a helper was accepted, while the same helper
inlined as a `List.filterMap` step was refused, so one helper had two answers depending on where it
was used.

**So `Option<T>` may be written wherever a model reads an optional, and the two rules that matter are
enforced on the type instead of on a spelling.**

*Making one is the `?` field being given its value, and nothing else.* The permission travels with the
check rather than with the expected type: a field's value carries it, and its branches do, so a field
may still be given one thing or nothing by a rule. Nothing else has it — an annotation that says
`Option<T>`, a helper that declares it as a return type, a step handed to a combinator. A helper
answers the optional it read, which is what this ADR says a model does everywhere but the one place:

```souther
partial let firstOver (n: Int, xs: List<Int>) : Option<Int> = {
    let head = List.get(0, xs)
    match head with
        | Some v -> if v > n then head else firstOver(n, List.drop(1, xs))
        | None -> head
}
```

That keeps the property issue #166 rests on — a step for `List.filterMap` has to answer an optional it
read, so absence the model owns stays a case of the model's own sum — and now keeps it in every
position rather than in the position the call site happened to check.

*A behavior does not answer one.* This ADR's reason was that `>->` would otherwise have to decide
whether it consumes `Some`/`None` or treats `Option<会員>` as one case. Measured, the implementation
has been answering that all along: an optional output composes when the next stage's input is the same
optional, and it travels as one case. The prohibition stands on the other two grounds, which the
measurement does not touch — the business vocabulary a reader of the answer matches on, and the
runtime's `Option` appearing in the Java-facing signature an exposed behavior generates (ADR-0008).
It is now read off the resolved output type, so `-> Option<Int>` and `-> Int?` are refused as the same
thing, and the report names the rule instead of blaming the pair that could not compose (E1701).

`T?` stays the field mark. Each spelling has a job: `?` marks where an optional is made, the name says
what the type is.

Migration cost across souther-examples (24 modules, 7007 lines): none. The one `Option<...>` written
there reads an optional and passes it on, and every `None` is a `?` field's value or an example
fixture.