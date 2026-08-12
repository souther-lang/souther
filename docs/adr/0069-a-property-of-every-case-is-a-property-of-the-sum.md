# ADR-0069: What holds of every case is a property of the sum

Status: Accepted.

## Context

A sum is opaque to things the compiler already knows about all of its cases, and the model pays for
it in repetition.

`example.pipeline` has ten states, every one of which spreads `OpportunityCommon`. Reading `id` off
the sum is an error — a sum has no fields of its own — so `idOf`, `amountOf` and `closeDateOf` are
ten `match` arms each, and `example.forecasting` writes four more such helpers over the same sum.
That is the single largest source of repetition in the CRM example (issue #160).

The same sum's ten stage names are also written twice, once as cases and once as the `StageName`
strings a total `match` produces, because `Map<Stage, Amount>` cannot cross the boundary and nothing
carries the order the stages are declared in (issue #161). A report keyed by stage therefore reports
"Closed Lost" first.

Both are the same gap: the cases carry a property in common, and the sum does not have it.

## Decision

**What holds of every case is a property of the sum.** Three properties follow from it.

"Property" is not "any fact that happens to be true of every case". It is a capability that the sum's
complete case set *determines*, and that answers the same way for every value of the sum. Adding or
removing a case may therefore add, remove or change what is derived — a case that stops spreading the
common data takes the field read away, and one field-bearing case makes the sum an object again. That
is the rule working, not a hole in it: the derivation reads the case set the sum has, and the case set
is what the author writes. What the rule does not say is that a sum inherits an annotation, an
interface, or an operation because every case happens to have one.

**A field every case spreads is read on the sum.** When every case (folded to leaves) spreads the
same data, the sum exposes that data's fields, and `d.id` reads one without opening the value. The
sharing is nominal: two cases that happen to declare a field of the same name have not shared it,
and reading it stays the error it is. That structural reading is the one ADR-0012 declined, and it
is what TypeScript's discriminated unions do; the nominal languages that have the feature at all
(Scala, Kotlin, Java) make the author declare the member on the parent instead. Souther derives it
because the author has already written `...Common` in each case, and because the spec DSL has no
"sum with a common part" form to derive a declaration syntax from (ADR-0001).

The generated sealed interface declares the accessor, which each case record's accessor of the same
name implements — so Java reads it off the sum the same way, with no `switch`.

**A sum every one of whose cases is a unit data is an enumeration, and travels as its case's name.**
A bare string, not an object holding a discriminator alone. This is what serde gives an enum with no
fields, what `FSharp.SystemTextJson` gives fieldless tags, what Jackson gives an enum, and what an
OpenAPI `enum` of `string` is; the object form Souther wrote is the odd one out. It is also what
lets such a sum key a `Map` at the boundary, which is what issue #161 asked for: a JSON object's key
cannot be an object, and ADR-0040 refused an `Int`-backed newtype key precisely because its external
form would then depend on where it appeared. Making the enumeration a bare string everywhere meets
that rule rather than carving an exception into it.

**An enumeration is ordered by the order its cases are declared in.** `Prospecting < Won`, and
`sort` / `sortBy` / `max` / `min` accept it. This is F#'s discriminated-union comparison, Haskell's
derived `Ord`, Rust's derived `Ord` over variants, and Java's enum ordinal; Elm alone withholds it,
and withholding it is why a report has to project the cases onto `Int` by hand. A `Map`'s iteration
order is untouched — it stays the deterministic, implementation-defined hash order the spec states,
and a report that wants stage order writes `Map.toList |> List.sortBy`.

The order lives on the sum and not on the case values: one unit data may be a case of two sums,
which place it differently, so a `Comparable` on the case record would have to answer for both. The
generated sealed interface carries the order, and the runtime's sort family takes it as a
comparator.

## Consequences

The ten-arm helpers become one field read, and `Map<Stage, Amount>` crosses the boundary with the
stages in the order a deal moves through them.

The boundary form of an existing unit-only sum changes: `{"stage": {"type": "Won"}}` becomes
`{"stage": "Won"}`. Consumers written against the old form must be updated. The change is toward the
form every other serializer already produces, so what they are updated to is not a Souther-specific
convention. A sum with even one field-bearing case is untouched, and a unit data nested inside such
a sum keeps its object form, so the two representations do not interfere.

Ordering is refused, not guessed, where it is undecided: a bare case value that two enumerations
both list has no order of its own, and comparing it takes the order from the sum on the other side.
Reordering an enumeration's cases changes its order, which is the cost F#, Haskell, Rust and Java
all accept for the same feature.

None of the three changes what a sum is. It is still not assignment-compatible with the data its
cases spread, and still exhaustively checked per layer. Deciding which case a value is stays `match`.

The construction side followed under issue #237: the shared part is spread from the sum as well as
read off it, so `Filed { ...d, filedOn = on }` writes at once what an arm per case would write alike.
The shared part is derived the same way and a named sum stays the only source, so that is this rule
reaching the other side of the boundary rather than a decision of its own.

## References

- ADR-0012 (nominal spread, no structural intersection — why the shared field set is derived from
  spreads and not from field names)
- ADR-0040 (typed map keys — the rule the enumeration key satisfies rather than excepts)
- ADR-0047 (a newtype is ordered by the value it wraps — the ordered-value set this extends)
- ADR-0001 (one-to-one with the spec DSL — why the shared field set is derived, not declared)
- Specification: `[#sum-data]`, `[#sum-discrimination]`, `[#collections]`, `[#primitives]`
- Prior art: TypeScript discriminated unions and Scala/Kotlin/Java sealed hierarchies (shared
  fields); serde, `FSharp.SystemTextJson`, Jackson, OpenAPI (fieldless enum as a string); F#,
  Haskell, Rust, Java (enumeration order)
