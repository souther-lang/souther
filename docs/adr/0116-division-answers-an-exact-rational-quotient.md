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

### Information loss is named

Moving an exact Rational result into a narrower numeric representation requires an operation that
states the loss policy.

The standard library provides explicit exact widening:

```text
Rational.fromInt(Int)         -> Rational
Rational.fromDecimal(Decimal) -> Rational
```

and policy-bearing narrowing, including operations equivalent to:

```text
Rational.toInt(RoundingMode, Rational) -> Int
Rational.toDecimal(Int, RoundingMode, Rational) -> Decimal
```

The precise standard-library surface is specified with the library, but no narrowing operation
silently chooses a rounding policy.

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
2. the corresponding base operation is closed over the wrapped type.

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

### Source-level Rational and compiler analysis ratios are different concepts

The compiler already has `souther.compiler.numeric.Rational`. Its current contract explicitly
describes an exact value used by constraint algebra and says that it is not a number a model
writes.

That concept remains useful and must not silently acquire the opposite meaning when `Rational`
becomes a source type.

The implementation therefore gives the compiler-internal concept a distinct name, such as:

```text
ExactRatio
```

and reserves `Rational` for the Souther language type.

Its JVM carrier likewise need not have the Java simple name `Rational`; a name such as
`RationalValue` keeps the runtime value distinct from compiler analysis machinery.

The exact class names are implementation details, but two values with different contracts must
not continue under the same conceptual name.

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

A numeric newtype no longer inherits scalar division when its carrier's quotient leaves that
carrier.

Rational initially creates no JSON, Java-boundary, input-generation, or ON-point contract.

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
* ADR-0095: standard-library naming grammar
* ADR-0112: a backend does not change a value to fit a host API
* ADR-0117: affine interpretation keeps coefficients exact
* Kotlin numeric conversions and mixed numeric operations
* Rust heterogeneous operator and comparison traits
* Scheme/Racket exact rational arithmetic
