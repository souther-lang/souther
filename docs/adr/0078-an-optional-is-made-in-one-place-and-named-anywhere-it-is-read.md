# ADR-0078: An optional is made in one place and named anywhere it is read

Status: Accepted. Revises ADR-0011 for `Option` (its `Never` and `Unit` decisions stand).

## Context

ADR-0011 decided that `Option<T>` cannot be written as a type. The compiler enforced that on two
spellings — `T?`, guarded in the builder, and `Some(...)`, refused in the elaborator — and not on the
type: `Option` sits in `TypeOps.denoted` beside `List`, `Set` and `Map`, so a model reached the same
type by naming it. Issue #202 asked what that had cost, which is a different question from how to close
it, and the measurement moved the answer.

Naming it reached six positions. Five are the reading ADR-0011 already permits, written instead of
inferred: a data field (where `T?` means the same type), a behavior's input, a helper's parameter, a
helper's declared return, and a function type's result. Two of those cannot be written any other way,
because the annotation is mandatory there — a recursive helper's return type, and a function-typed
parameter (spec 13.1):

```souther
partial let firstOver (xs: List<Int>) : Option<Int> = ...
let firstKept (step: (Int) -> Option<Int>, xs: List<Int>) : Int = ...
```

The second is how a user writes a `List.filterMap`-shaped combinator of their own. Refusing the name
leaves no way to say what its step answers, so it removes programs rather than a second spelling of an
existing one. The corpus has no helper of that shape, which is why the migration measurement in the
issue — one line — did not show it.

The sixth position was a leak, and its root was this ADR's own reasoning. `None` was accepted wherever
the expected type was an optional, on the grounds that "an expected optional reaches an expression only
from a field's own type, since nowhere else in a model can `T?` be written". Naming the type is another
way to expect one, so the premise stopped holding and `let p: Option<Int> = None` made an absence
outside a construction. A declared optional return leaked the same way in one position and not another:
`| None -> None` inside such a helper was accepted, while the same helper inlined as a `List.filterMap`
step was refused, so one helper had two answers depending on where it was used.

## Decision

**`Option<T>` may be written wherever a model reads an optional.** A data field, a behavior's input, a
helper's parameter or declared return, a function type's result, a local binding's annotation. There is
no name guard, and none of these is a new capability: each is a position that already held an optional
and could not say so.

**`T?` stays the field mark.** Each spelling has a job: `?` marks where an optional is made, and the
name says what the type is. Outside a field, `?` is written only in the shipped core, as a type
variable is (ADR-0028).

**Making one is the `?` field being given its value, and nothing else.** The permission travels with the
check rather than with the expected type, because writing the type is now another way to expect one. A
field's value carries it, and so do the branches of that value — a field may be given one thing or
nothing by a rule, which is the same construction written conditionally. Nothing else has it: an
annotation that says `Option<T>`, a helper that declares it as a return type, an argument, a lambda
handed to a combinator. A helper answers the optional it read, which is what ADR-0011 says a model does
everywhere but the one place:

```souther
partial let firstOver (n: Int, xs: List<Int>) : Option<Int> = {
    let head = List.get(0, xs)
    match head with
        | Some v -> if v > n then head else firstOver(n, List.drop(1, xs))
        | None -> head
}
```

Two things stop the permission at a call and at a function: an argument and a lambda body are typed
with no expected type at all, and the permission is dropped at both boundaries. The second is
redundant with the first today and is stated anyway, so the rule holds where it is written rather than
resting on how an argument happens to be typed elsewhere. That keeps the property issue #166 rests on —
a step for `List.filterMap` has to answer an optional it read, so absence the model owns stays a case
of the model's own sum — and keeps it in every position rather than in the one the call site happened
to check.

**A behavior does not answer an optional.** ADR-0011's reason was that `>->` would otherwise have to
decide whether it consumes `Some`/`None` or treats `Option<Member>` as one case. Measured, the
implementation has been answering that all along: an optional output composes when the next stage takes
the same optional, and it travels as one case. So the prohibition stands on the two grounds the
measurement does not touch — the business vocabulary a reader of the answer matches on
(`-> Member | NoSuchMember`), and keeping the runtime's `Option` out of the Java-facing signature an exposed
behavior generates (ADR-0008; an optional's JVM type is `souther.runtime.Option`). It is read off the
resolved output type, so `-> Option<Int>` and `-> Int?` are refused as the same thing, and the report
names the rule instead of blaming the pair that could not compose (E1701).

## Consequences

Issue #202 closes. The two rules that matter are enforced on the type, so neither is a rule a second
spelling walks past — the shape ADR-0076 removed for function types.

A model may now write the type of a position that reads an optional, which is mostly a documentation
gain: a helper says what it answers instead of leaving it to be inferred. It is not a new capability,
and nothing that could not be expressed before becomes expressible, except the two annotations that
were mandatory and unwritable.

`E1303` now says something true again. Its message — "nothing here is asking for one" — was inaccurate
wherever an annotation had asked; the question is no longer what asked but where the value is going.

Migration cost across souther-examples (24 modules, 7007 lines): none. The one `Option<...>` written
there reads an optional and passes it on, and every `None` is a `?` field's value or an example
fixture.

## References

- Specification: `[#algebraic-types]`, `[#optional]`, `[#e1303]`, `[#e1701]`
- ADR-0011 (the decision this revises), ADR-0008 (asymmetric Java interop), ADR-0028 (the reserved
  core), ADR-0066 (a helper is typed by its body)
