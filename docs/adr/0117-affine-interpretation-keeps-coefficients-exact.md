# ADR-0117: Affine interpretation keeps coefficients exact

Status: Proposed. Specialises ADR-0111.

## Context

ADR-0111 made `AffineForms` the one owner of interpreting an expression as:

```text
constant + Σ coefficient · atom
```

so different consumers no longer keep competing accounts of the arithmetic an expression denotes.

`LinearForm` currently represents that result as:

```java
BigDecimal constant
Map<A, BigDecimal> coefs
```

while `NumericDomain` already uses exact rational arithmetic when solving the resulting
constraints.

The split matters because affine reasoning is not closed over finite decimals. A rule such as:

```text
3 * x <= 1
```

places a derived boundary at one third. Rounding that value before the constraint algebra sees it
changes the relation being reasoned about.

ADR-0116 makes the same issue visible directly in source arithmetic:

```souther
guard y < -1 / 2 * x + 30
```

The affine form of this expression contains an exact coefficient of `-1/2`. Reading it first as a
finite `BigDecimal` would discard information before it reached the exact algebra.

The reason to fix this is nevertheless independent of source-level Rational. An affine
interpretation that claims to say what arithmetic an expression came to should not approximate
that arithmetic merely because a later consumer already has a more exact representation.

## Decision

**Affine interpretation carries exact coefficients.**

`LinearForm<A>` represents its constant and coefficients with the compiler's exact ratio type
rather than `BigDecimal`.

Conceptually:

```text
LinearForm<A> =
    exact constant
    + Σ exact coefficient · atom
```

Int and Decimal constants are embedded exactly when the affine reader encounters them.

A Rational expression admitted by ADR-0116 is read as the same exact mathematical value.

No rounding occurs while an expression is being interpreted as an affine form.

### The exact ratio is compiler arithmetic, not a model value

The existing `souther.compiler.numeric.Rational` already represents the mathematical object
needed by this decision.

Once ADR-0116 introduces a source type named `Rational`, keeping both concepts under that name
would give the compiler class a contract opposite to the language type: its current documentation
deliberately says that it is not a number a model writes.

The compiler-internal type is therefore renamed to a name such as:

```text
ExactRatio
```

Its role remains:

> the exact scalar representation used by compiler numeric reasoning.

It is used by both `LinearForm` and `NumericDomain`.

It is not the runtime carrier of the Souther `Rational` primitive.

This preserves the distinction the existing implementation was trying to express between exact
reasoning and a value that stands at a model position.

### Exact coefficients do not change a position's carrier

An exact coefficient says how a numeric expression relates its atoms. It does not say what values
those atoms themselves may take.

Thus an Int input remains on the Int lattice and a Decimal input remains on the Decimal carrier.

For:

```souther
guard y < -1 / 2 * x + 30
```

with `x: Int` and `y: Int`, the affine reader carries the coefficient `-1/2` exactly, while `x`
and `y` remain integer positions.

Exact Rational coefficients therefore introduce neither Rational input positions nor Rational ON
points.

The distinction between an exact ratio used in reasoning and a `Place` on a carrier remains.

### Conversion to a carrier happens only at the carrier edge

When an exact derived result must become a value on a Decimal or Int carrier, that conversion is
performed where the carrier is known.

That edge is responsible for whether an exact ratio:

* is itself representable on the carrier;
* must be widened outward for a bound;
* determines that no carrier value exists at that exact point.

`LinearForm` does not make that decision.

This keeps exact arithmetic and carrier granularity as separate concerns.

### Exact Decimal embedding must remain compact

Embedding a Decimal into compiler exact arithmetic must not eagerly materialise `10^scale` merely
because a mathematical fraction can be written with that denominator.

A Decimal compact in the source representation must not cause work proportional to its scale
solely by becoming an affine coefficient.

The concrete canonical representation used to satisfy that requirement belongs to the
implementation.

## Consequences

`LinearForm` no longer uses `BigDecimal` as its arithmetic domain.

The current exact-ratio implementation becomes the common scalar representation used by affine
interpretation and `NumericDomain`, rather than exactness appearing only after the affine
boundary.

The rename from compiler `Rational` to `ExactRatio` also removes the false implication that the
compiler analysis object is the runtime representation of ADR-0116's source-level `Rational`.

Existing `Place` and carrier abstractions remain distinct. A fraction such as one third can
participate in exact reasoning without thereby becoming a value a Decimal or Int input can take.

Readers of affine forms do not acquire new rounding rules. Any approximation or outward rounding
remains owned by the edge that turns an exact result into a carrier-specific bound.

This decision is useful independently of ADR-0116, although exact source division makes the
existing loss at the `LinearForm` boundary directly observable.

## References

* ADR-0111: an environment answers with the value a name denotes, never with the form a reader
  makes of it
* ADR-0116: division answers an exact Rational quotient
* Specification: `[#invariant-discharge-arithmetic]`, `[#example-partition]`,
  `[#example-adequacy]`
* `souther.compiler.check.AffineForms`
* `souther.compiler.numeric.LinearForm`
* the compiler exact-ratio type currently named `souther.compiler.numeric.Rational`
