# ADR-0116: Division answers an exact Rational quotient

Status: Proposed. Amends ADR-0033 and ADR-0047. ADR-0003's zero-divisor distinction and
ADR-0095's naming rule stand.

## Context

ADR-0033 made arithmetic operators available on both numeric primitives:

```text
Int / Int         -> Int
Decimal / Decimal -> Decimal
```

and deliberately distinguished the terse operator form, which aborts on a zero divisor, from
named division functions that may return `DivisionByZero` as a case.

The zero-divisor part of that decision is independent of another property the two `/` operators
acquired: both discard information.

`Int / Int` truncates toward zero. `Decimal / Decimal` rounds to a fixed significant-digit
precision. Neither `Int` nor finite `Decimal` is closed under mathematical division, so keeping
the quotient in the operand type requires an unstated loss policy.

That conflicts with the rule used elsewhere in the numeric library. `Decimal.toInt`,
`Decimal.round`, and `Decimal.divide` require the model to state how information is discarded.
Whether a fraction is rounded, truncated, or otherwise quantised is a domain decision rather than
an incidental consequence of the representation.

The difference is visible in an ordinary expression:

```souther
guard y < -1 / 2 * x + 30
```

For `x: Int` and `y: Int`, the coefficient written is exactly negative one half. With truncating
integer division, `-1 / 2` instead becomes zero.

Making `Int / Int` exact means its result can no longer be `Int`. It also means the remainder of
the expression contains operations such as:

```text
Rational * Int
Rational + Int
Int < Rational
```

A general implicit `Int -> Rational` conversion would make those expressions convenient, but
would also let an `Int` silently satisfy a Rational binding, parameter, field, or return
position. Souther deliberately does not use such numeric coercion: the existing `Int`/`Decimal`
boundary is explicit, and `[#stdlib-decimal]` states that the two meet only where the conversion
is written.

Contextual literals are not required either. Today:

```text
1    : Int
1m   : Decimal
0.5  : compile error
0.5m : Decimal
```

and exact division does not require that rule to change.

Nor should arithmetic depend on whether an expression is a literal, a compile-time constant,
inside a `guard`, or still written inline. These two expressions must have the same arithmetic:

```souther
-1 / 2 * x
```

and:

```souther
let slope = -1 / 2
slope * x
```

The distinction needed is therefore between **implicit conversion** and an **operator directly
defined for different operand types**.

## Decision

### `/` returns the exact quotient

The numeric `/` operator does not truncate or round a non-zero quotient.

Its primitive signatures are:

```text
Int      / Int      -> Rational
Decimal  / Decimal  -> Rational
Rational / Rational -> Rational
```

Unary minus answers the type it is given, Rational included:

```text
-Rational -> Rational
```

A model that can write `0 - r` for a Rational `r` and not `-r` would have the negation of a number
depend on which spelling reaches an operator table. What the standard library offers over a
Rational beyond the operators is settled with the library.

The static result type does not depend on the value of the quotient:

```souther
1 / 2   // Rational, exactly 1/2
4 / 2   // Rational, exactly 2
```

Therefore:

```souther
let r = 4 / 2          // Rational
let i: Int = 4 / 2     // type error
```

Compile-time evaluation may discover that `4 / 2` has the value two. It does not change its type.

### Numeric literal typing is unchanged

ADR-0033's literal rule stands.

```text
1       : Int
1m      : Decimal
0.5     : compile error
0.5m    : Decimal
```

There is no contextual `fromInteger` or `fromRational` rule.

In particular:

```souther
let d: Decimal = 1
```

remains a type error.

### Rational is an exact computational numeric type

`Rational` represents an exact rational value.

Every `Int` and every `Decimal` has one exact mathematical value in Rational arithmetic:

```text
Int     n -> n / 1
Decimal d -> the exact finite-decimal value of d
```

This fact does **not** define an implicit conversion relation.

These remain errors:

```souther
let n: Int = 3

let r: Rational = n
takesRational(n)
```

When a non-operator position requires a Rational, the conversion is explicit:

```souther
Rational.fromInt(n)
Rational.fromDecimal(d)
```

### A Rational operand admits heterogeneous exact arithmetic

When one operand already has static type `Rational`, arithmetic with `Int` or `Decimal` is
defined directly.

For `N` equal to `Int` or `Decimal`:

```text
Rational + N        -> Rational
N        + Rational -> Rational

Rational - N        -> Rational
N        - Rational -> Rational

Rational * N        -> Rational
N        * Rational -> Rational

Rational / N        -> Rational
N        / Rational -> Rational
```

The non-Rational operand is interpreted at its exact mathematical value as part of that
operator's semantics.

It is not first converted to a Rational value by a language-wide coercion.

The distinction is observable:

```souther
let n: Int = 3
let r: Rational = 1 / 2

r + n                    // Rational
n * r                    // Rational

let x: Rational = n      // error
takesRational(n)         // error
```

### Int and Decimal still have no direct mixed arithmetic

There is no common-numeric-type search and no direct Int/Decimal promotion.

These remain errors:

```souther
1 + 1m
1 < 1m
1 / 2m
```

A Rational value does, however, provide an explicit path into exact arithmetic:

```souther
1 / 1 + 1m
```

is valid because:

```text
1 / 1              : Rational
Rational + Decimal : Rational
```

This is intentional.

The Int/Decimal boundary has not disappeared: `1 + 1m` still has no meaning. The second
expression crosses that boundary only after the source has visibly produced an exact Rational
value.

The same applies to an explicitly constructed Rational:

```souther
Rational.fromInt(1) + 1m
```

Therefore the rule is not that Int and Decimal promote to a common type. It is:

> Once an operand is already Rational, that operation is exact Rational arithmetic.

Exact division is one visible way to enter that arithmetic.

### A heterogeneous operator admits two operands; it determines neither

ADR-0066 types a helper's parameter from its body, and says that what an operator asks of an
operand is answered where that operator's rule is stated. This is that rule for these operators.

The heterogeneous signatures above admit a pair whose types are already settled. They determine
nothing about an operand whose type is still open.

Left to the implementation, the resolution of an overloaded operator would decide a typing policy
by accident: with both `Int * Int -> Int` and `Rational * Int -> Rational` available, the
parameter of `let double (x) = x * 2` has two candidates that differ only in which arm the
implementation reached first.

So an open operand is determined by the homogeneous signature alone:

```souther
let double (x) = x * 2         // Int * Int    determines x : Int
let scale (x) = 1 / 2 * x      // Rational * Rational determines x : Rational
```

The second is not a Rational because the operator preferred one. Its left operand has type
Rational already, and the homogeneous rule reads the other side as the same type. A helper that
wants the heterogeneous operation writes the type it wants:

```souther
let scale (x: Int) = 1 / 2 * x     // Rational * Int -> Rational
```

This keeps the claim that heterogeneous arithmetic is not conversion. A conversion relation would
have let the open parameter be anything embeddable; an operator admitting a pair says nothing
about a type nothing has settled.

### What Rational answers when a position asks

A type is asked what it answers, and `TypeOps.Requires` is where the two yes/no questions are
asked: `EQUALITY`, which `==` requires and which a `Set` requires of its element and a `Map` of
its key; and `EXTERNAL_FORM`, which a data's field, a newtype's base, and a behavior's input and
output require. Ordering is not one of those — it is a witness, and `Ordering` holds it.

Rational answers:

```text
EQUALITY       yes
ordering       yes, by exact mathematical value
EXTERNAL_FORM  no
```

`EXTERNAL_FORM no` is what the previous section states, made a property of the type instead of a
list of places. Every primitive Souther has today answers yes to both, and `TypeOps.answers`
writes one arm for `Type.Prim`, so adding `RATIONAL` to `Type.Prim` and nothing else would give
Rational an external form. The arm splits.

What follows is not a list: a data's field, a newtype's base, and a behavior's input and output
refuse Rational, and refuse a `List<Rational>` or a `Map<String, Rational>` at those positions
too, because those arms already ask the question of what they hold.

What equality and ordering buy is that Rational is an ordinary value in computation:

```text
List<Rational>   Set<Rational>   Map<Rational, V>   Option<Rational>   (Int, Rational)
```

are usable inside a computation, and `List.sort`, `min` and `max` work over Rational.

The heterogeneous rule does not reach the library. `Set.contains(v, s)` takes its element at the
one type the signature names, and an `Int` is not a member of a `Set<Rational>`. Exact
heterogeneous comparison is a rule about those operators, not about every position that compares.

### Equality and ordering follow the same rule

Rational comparison with Int or Decimal is by exact mathematical value.

For `N` equal to `Int` or `Decimal`:

```text
Rational == N        -> Bool
N        == Rational -> Bool
Rational /= N        -> Bool
N        /= Rational -> Bool

Rational <  N        -> Bool
N        <  Rational -> Bool
Rational <= N        -> Bool
N        <= Rational -> Bool
Rational >  N        -> Bool
N        >  Rational -> Bool
Rational >= N        -> Bool
N        >= Rational -> Bool
```

For example:

```souther
1 == 2 / 2       // true
1m == 2 / 2      // true
0.5m == 1 / 2    // true
1 < 3 / 2        // true
```

Decimal scale remains irrelevant to equality as ADR-0009 requires.

Direct Int/Decimal comparison remains invalid:

```souther
1 == 1m          // error
1 < 1m           // error
```

### The motivating expression follows ordinary operator typing

For `x: Int` and `y: Int`:

```souther
guard y < -1 / 2 * x + 30
```

is typed as:

```text
-1 / 2            : Rational
Rational * Int    : Rational
Rational + Int    : Rational
Int < Rational    : Bool
```

No rule asks whether any operand is a literal or compile-time constant, whether the expression
occurs in a `guard`, or what type a surrounding expression expects.

Therefore extracting intermediate bindings preserves both typability and meaning:

```souther
let slope = -1 / 2
let intercept = 30
let line = slope * x + intercept

guard y < line
```

where:

```text
slope     : Rational
intercept : Int
line      : Rational
```

Refactoring an arithmetic expression into named intermediate values must not change which numeric
operations it denotes.

### Changing a value is what needs a policy; failing to represent one is a case

The rule is about the mathematical value and not about the width of the representation.

A narrowing that changes the value states how. A narrowing that does not change it has no policy
to state, and `4 / 2` into `Int`, or `1 / 2` into `Decimal`, changes nothing:

```text
4 / 2 = exactly 2
1 / 2 = exactly 0.5m
```

Requiring a rounding mode there would name a decision nobody made.

So two kinds of narrowing are available to the library, and this decision admits both:

```text
exact, answering a case where the carrier has no such value
    Rational -> Int     | <the quotient is not whole>
    Rational -> Decimal | <the quotient has no finite decimal>

lossy, answering a value and stating what it discarded
    Rational -> Int      with a rounding mode
    Rational -> Decimal  with a scale and a rounding mode
```

Widening is exact and states nothing:

```text
Rational.fromInt(Int)         -> Rational
Rational.fromDecimal(Decimal) -> Rational
```

The standard-library surface is specified with the library. What this decision fixes is that no
operation changes a value silently, and that an exact conversion is not made to name a rounding
policy it does not use.

A result outside the range its carrier holds aborts where the corresponding arithmetic aborts;
that is a model error rather than a rounding decision.

`Decimal.divide(dividend, divisor, scale, mode)` remains the operation for a model that wants a
Decimal quotient and chooses its scale and rounding rule at that point.

### Truncating integer division is named

The existing:

```text
Int.divide(dividend, divisor): Int | DivisionByZero
```

computes a quotient truncated toward zero.

That policy must be visible in its name. It becomes:

```text
Int.truncatingDivide(dividend, divisor): Int | DivisionByZero
```

following ADR-0095's rule that arithmetic conventions on which languages differ are named.

`Int.truncatingRemainder` already follows that vocabulary.

Additional integer quotient policies are added only when the model needs them. They need not be
introduced as a complete family merely because `/` changes.

### Zero division is unchanged

This decision concerns information preservation, not the classification of a zero divisor.

ADR-0033's operator/function distinction stands:

* `/` aborts on a zero divisor;
* a named operation may represent `DivisionByZero` as a case.

Thus exact `/` still aborts where its divisor is zero.

### Newtype arithmetic requires closure

ADR-0047's "dimension-preserving" condition on newtype arithmetic is necessary but not
sufficient.

A numeric newtype inherits an arithmetic operation only when:

1. the operation preserves the newtype's dimension; and
2. the corresponding base operation is **type-closed** over the wrapped type — its static result
   type is that type.

Type-closed, not total. `Int + Int -> Int` is type-closed and still aborts on overflow, and a
newtype's own invariant may refuse the value it re-wraps. Neither of those is what this condition
is about: it asks whether there is an `Int` to wrap at all.

For:

```souther
data Yen = Int
```

operations such as:

```text
Yen + Yen -> Yen
Yen - Yen -> Yen
Yen * Int -> Yen
```

may remain closed over `Yen`.

But:

```text
Yen / Int
```

is not inherited because:

```text
Int / Int -> Rational
```

does not produce an `Int` to wrap again as `Yen`.

The same applies to a newtype directly over Decimal.

The heterogeneous Rational rules also do not unwrap a nominal type:

```souther
yen * (1 / 2)     // error
yen < 1 / 2       // error
```

Quantisation of a domain value remains a domain operation rather than an accidental consequence
of primitive arithmetic.

### Rational is computational, not a boundary type

This decision introduces Rational as a value produced and consumed by computation.

It does not introduce Rational as an external representation.

Rational may appear in local computation and helper signatures, but is not admitted by this
decision as:

* a behavior input or output boundary value;
* a stored data field;
* a newtype carrier;
* a JSON scalar;
* a boundary Map key.

Therefore this ADR selects no JSON representation for Rational and introduces no Rational
input-space or ON-point semantics.

Making Rational a boundary type is a separate decision.

### The JVM representation must preserve compact Decimal values

The exact JVM representation of Rational is an implementation choice with one architectural
constraint:

> Embedding a Decimal into Rational must not eagerly materialise `10^scale` merely to represent
> the same exact value.

A Decimal that is compact in its own representation must not become work or storage proportional
to its scale solely because it entered exact arithmetic.

The canonical representation used to satisfy that rule belongs to the implementation, not to this
ADR.

### The name `Rational` belongs to the language

The compiler already has `souther.compiler.numeric.Rational`, whose contract says it is not a
number a model writes. That concept keeps its meaning and gives up the name; ADR-0117 decides
what it is called instead and why the two are not one implementation.

## What was weighed and rejected

### Keep `/` and add exact division under another name

`//`, or `Rational.divide`, would leave every existing model compiling.

It also leaves the defect. The problem is not that exact division is unavailable — it is that the
unmarked operator discards information without saying so. Adding a second operator makes the
exact one the marked case and leaves the truncating one as what an author writes by default.
Souther pushes a loss policy onto a named operation, so it is lossy division that takes a name,
and `/` is the operation that states none because it discards nothing.

### Diagnose the suspicious case and keep the rest

Refusing `1 / 2` while admitting `x / 2` leaves the same loss wherever the dividend is not a
literal, and makes the type of an expression depend on how it was written. A warning is not a
numeric semantics.

### Refuse `/` entirely and keep only named division

This removes accidental truncation and also removes the ordinary exact expression that motivated
the change. The language can represent the quotient; refusing to write it down is a worse answer
than typing it.

### A numeric tower with implicit promotion

`Int` and `Decimal` would promote to `Rational` on meeting, and `1 + 1m` would compile because
both are rationals. That erases the explicit `Int`/`Decimal` boundary `[#stdlib-decimal]` states,
and makes Rational a numeric supertype. Heterogeneous operators give the arithmetic without the
conversion relation.

### Contextual numeric literals

Letting the expected type decide what `1` means would replace ADR-0033's literal rule as a side
effect of fixing division, and would make an expression's meaning depend on where it sits. It
raises defaulting and generalisation questions exact division does not.

### Require `fromInt` / `fromDecimal` at every mixed operand

Explicit, consistent, and it makes the motivating guard read as conversion plumbing:

```souther
guard Rational.fromInt(y) < (-1 / 2) * Rational.fromInt(x) + Rational.fromInt(30)
```

The conversion carries no information at an operator position — the operator already says which
arithmetic is being done. It is worth writing where a value is stored, passed, or returned, which
is exactly where this decision keeps it.

### Answer Decimal where the quotient terminates and Rational where it does not

The result type would depend on the value, so `a / b` has no static type, and `1m / 4m` and
`1m / 3m` would differ in type. Both answer Rational instead.

### Keep the Decimal operator rounding as it does

A finite Decimal is not closed under division, so any fixed precision discards information for
`1m / 3m` and says nothing about it. A Decimal quotient remains available from `Decimal.divide`,
where the scale and mode are the model's.

### Rewrite the expression where an analysis can recognise it

Clearing denominators in a guard would type the motivating expression without a Rational type at
all. It special-cases what one analysis happens to recognise, stops working once the value is
named or leaves that fragment, and makes admitted arithmetic depend on the consumer. ADR-0117
takes the same alternative up on the compiler side.

## Consequences

The `/` operator has one numeric meaning: exact division.

Rounding and truncation move to operations whose names or arguments state the policy.

The expression:

```souther
guard y < -1 / 2 * x + 30
```

has its mathematical meaning without implicit numeric conversion, contextual literals,
constant-expression privileges, or a guard-specific rewrite.

`Int` and `Decimal` remain distinct types with no direct mixed arithmetic. A model may cross
between them through Rational arithmetic, but only after an expression has visibly acquired type
Rational.

A quotient that happens to be integral remains Rational, so typing never depends on constant
evaluation.

Exact arithmetic begins at the subexpression that produced a Rational and does not reach back up
the expression. For `a: Int`:

```souther
a * 2 / 2      // a * 2 is Int, and overflows as Int arithmetic does
a / 2 * 2      // a / 2 is Rational, and everything after it is exact
```

The two are different expressions and this decision does not make them one. Nothing promotes an
operation because a later operation is exact, and nothing reassociates an expression to reach an
exact reading — which is the same statement as "a Rational operand admits the operation", read
from the other end.

A numeric newtype no longer inherits scalar division when its carrier's quotient leaves that
carrier.

Rational initially creates no JSON, Java-boundary, input-generation, or ON-point contract.

`Rational` becomes a reserved type name. A primitive's spelling is reserved (E1502), so a model
declaring `data Rational` stops compiling and is renamed. Nothing in this repository or the
example corpus declares one.

The published-declaration boundary version moves. A helper signature may write `Rational`, and a
published declaration crosses a jar as source, so an older compiler would read a signature naming
a type it has no primitive for — the same reason ADR-0076 moved it when a function type became
writable there.

The reading rules stated over `/` change with the operator. `[#invariant-discharge-terms]` says
that `/` and `Int.divide` are two spellings of one truncating quotient and that where both answer
they answer the same number — which after this decision is a statement about
`Int.truncatingDivide` alone, the operator no longer computing a truncating quotient at all. The
`Int` pair for which the truncating quotient has no value keeps its account there; exact `/` has
no such pair, its quotient for that pair being a whole number Rational holds.

ADR-0033 is amended where it says `/` yields the operand type and where Decimal `/` chooses an
implicit precision. Its literal and zero-divisor decisions stand.

ADR-0047 is amended so that dimension preservation alone is not enough for inherited newtype
arithmetic; closure over the wrapped type is also required.

## References

* Specification: `[#primitives]`, `[#stdlib-int]`, `[#stdlib-decimal]`, `[#newtype-arithmetic]`,
  `[#invariant-discharge-terms]`
* ADR-0003: invariant violations abort; possible business outcomes are cases
* ADR-0009: Decimal scale is not part of value identity
* ADR-0033: numeric literals and arithmetic operators
* ADR-0047: comparison and arithmetic of single-value newtypes
* ADR-0066: a helper's parameter types come from its body — and what an operator asks of an
  operand is stated with that operator
* ADR-0095: standard-library naming grammar
* ADR-0112: a backend does not change a value to fit a host API
* ADR-0117: affine interpretation keeps coefficients exact
* Kotlin numeric conversions and mixed numeric operations
* Rust heterogeneous operator and comparison traits
* Scheme/Racket exact rational arithmetic
