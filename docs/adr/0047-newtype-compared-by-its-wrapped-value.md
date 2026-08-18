# ADR-0047: A single-value newtype is compared by the value it wraps

Status: Accepted. Amended three times — arithmetic, deferred at the time of this decision, was added
later (see the "Arithmetic" paragraph below and spec §newtype-arithmetic / §invariant-discharge), the
sort family was brought onto the same reading (see "Sorting"), and the ordered set the rule composes
with grew an enumeration (see "What the wrapped type may be"). The ordered primitives are
eight since ADR-0103, not the five this reasons about.

## Context

`data Amount = Int` is a newtype: a domain name and an invariant over a single underlying value. The
value is reached as `Amount.value`. But `value` is not a name the author writes — the `data X = Y`
syntax generates it. So requiring `.value` to compare amounts (`m.amount.value <= 100`) leaks an implicit
detail into every comparison, and reads as ceremony.

Two things were already inconsistent. Equality (`==` / `/=`) works on any data structurally, so
`Amount == Amount` compares the wrapped values without `.value`; but ordering (`<` `<=` `>` `>=`) was
defined only for the five primitive types, so `Amount <= Amount` was a type error and you dropped to
`.value`. And a bare literal never met a newtype: `Amount == 100` did not type-check either.

Souther has already extended ordering beyond Elm. Elm orders only `Int`/`Float`/`Char`/`String`;
Souther adds `Decimal`/`Date`/`DateTime` because the JVM carries them as `Comparable`. A single-value
newtype over an ordered type is "morally" that type with a name and an invariant, so ordering it by
the wrapped value is the same kind of extension — and it removes the `.value` noise the author never
asked to write.

The pull against it is nominal safety: the whole point of `Amount` and `quantity` being distinct newtypes is
that they must not be confused. Any relaxation has to keep `Amount <= quantity` an error.

## Decision

A single-value newtype (`data X = Y`) is compared by the value it wraps, for both equality and
ordering, so `.value` is not written. The nominal boundary is kept by four rules:

- Two of the same newtype compare their wrapped values: `Amount <= Amount`, `Amount == Amount`.
- A bare literal of the wrapped type takes the newtype from the other operand: `Amount <= 100`,
  `Amount == 0`. Only a source literal is taken this way — this mirrors how `[]` takes its element type
  from context (ADR-0028).
- Two different newtypes over the same base do not compare: `Amount <= quantity` is a type error, even
  though both wrap `Int`.
- A non-literal value of the wrapped type is not taken implicitly: `Amount <= n` (with `n: Int`) is a
  type error — write `Amount <= Amount(n)`.

Ordering additionally requires the wrapped type to be ordered (Int/String/Decimal and the temporals — Date/DateTime when this was written, and Time/Instant since ADR-0103);
equality works over any wrapped type. The unwrap recurses, so a newtype over a newtype
(`Manager = Level = Int`) reaches its base. In the backend, a newtype operand of a comparison is opened
to its wrapped value (its `value` accessor) before the primitive comparison, so `Amount <= Amount` emits
the same integer comparison `Amount.value <= Amount.value` would.

Arithmetic on a newtype (`Amount + Amount`) was out of scope in the original decision — only comparison
was adopted — because it raised questions this decision did not settle: whether the result re-wraps
(and re-checks the invariant, so `Amount - Amount` could abort on a negative), and which operators make
domain sense. **Arithmetic was added subsequently**, resolving those questions:

- Closed `+`/`-` stay in the newtype (`Amount - Amount : Amount`): the operator opens each operand to its
  base, computes, and re-wraps, re-checking the invariant. A `Amount - Amount` that goes negative aborts
  inside the domain, or is *discharged* at compile time when a `guard` guard establishes it (the
  invariant-discharge check, spec §invariant-discharge).
- Scalar `*`/`/` by a plain number of the base also stay in the newtype (`Amount * 2`) — the dimension
  is unchanged. A product of *two* newtypes (`unitPrice * quantity`, a dimension change / units) is not modeled
  and stays rejected.

See spec §newtype-arithmetic. The re-wrap/invariant question is answered by the invariant-discharge
check, and the operator question by "dimension-preserving only".

## What the wrapped type may be

The decision says the wrapped type must be ordered and lists which types those are, and the list is
of primitives because those were the ordered types when this was written. ADR-0069 then made an
enumeration ordered, by the order its cases are declared in. Nothing was decided about the two
together, and the compiler answered both ways: `data StageN = Stage` was measured on `Stage`'s
declaration order and generated as `Comparable<StageN>`, while `StageN < StageN` did not typecheck
and `sort` would not take a list of them (issue #856).

**The rule is `Ordered(Newtype<T>) = Ordered(T)`, and `T` is whatever is ordered at the time.** The
list in the decision above is the ordered set as it stood, not a second condition on top of being
ordered — so a newtype over an enumeration is ordered, and nothing had to be decided to get that
answer. Excepting the enumeration would have been the new decision, and there is no reason for one:
the wrapped value has an order and the name over it does not take that away.

Two things follow that the primitive cases did not raise. The order of an enumeration lives on the
sum rather than on the case value, because one unit data may be a case of two sums (ADR-0069), so a
newtype over a bare *case* has no order to carry either and is refused; a newtype over the *sum*
names one enumeration and is ordered by it. And the generated `Comparable` cannot delegate to the
wrapped value's own `compareTo`, there being none — it reads the sum's declaration order, which is
the wrapper being the place a Java reader gets an ordering the case values do not have.

## Sorting

`List.sort` / `max` / `min` / `sortBy` kept the older reading — only the five primitives are ordered —
so `Amount > threshold` was accepted while `sortBy((r) -> r.Amount, Bill)` was rejected as a key with no
ordering. The same value is orderable in a comparison and not orderable as a sort key, which is not a
distinction anyone can act on. **The sort family now reads ordering the same way the operators do**:
the element (or the key) is ordered when its base is.

The runtime compares by natural order, so the wrapper has to carry the ordering rather than have it
opened at each call site: a single-value newtype over an ordered type is generated as
`Comparable<itself>`, comparing the value it wraps. The alternative — rewriting each call to pass an
unwrapping function — needs a key-taking variant of `max` / `min` that does not exist, and leaves the
type unordered for a Java caller that wants a `TreeMap` key.

## Consequences

- `m.amount.value <= 100` becomes `m.amount <= 100`, and `m.amount <= m.budget` (two amounts) now type-checks. The
  implicit `value` name stays implicit; the author writes the domain name.
- Equality and ordering are now consistent for newtypes (both read the wrapped value), and a bare
  literal compares against a newtype in both.
- `Amount` and `quantity` remain uncomparable to each other and to a raw `Int` variable, so the nominal
  distinction that motivates newtypes is intact.
- Sorting reads the same definition of ordered, so `sortBy((r) -> r.Amount, Bill)` orders by a typed key
  without projecting to `.value` — which for a `List<Amount>` also meant re-wrapping afterwards, running
  the invariant on every element again.
- Arithmetic was subsequently added on the same wrapped-value footing — closed `+`/`-` and scalar
  `*`/`/`, re-wrapping and re-checking the invariant. The re-wrap/invariant question this decision
  deferred is resolved by the invariant-discharge check (spec §invariant-discharge); a product of two
  newtypes (units) remains out (no dimensions, ADR-0010).
