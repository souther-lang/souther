# ADR-0117: Affine interpretation keeps coefficients exact

Status: Proposed. Specialises ADR-0111. Follows ADR-0116.

## Context

ADR-0111 made `AffineForms` the one owner of interpreting an expression as:

```text
constant + Σ coefficient · atom
```

so different consumers no longer keep competing accounts of the arithmetic an expression denotes.

`LinearForm` represents that result as:

```java
BigDecimal constant
Map<A, BigDecimal> coefs
```

and nothing is lost there today. `BigDecimal` holds a finite decimal exactly, the affine grammar
composes only addition, subtraction, negation and a scalar multiply — `AffineForms.composed`
refuses `DIV` outright, its comment saying that a divide truncates for `Int` — and finite decimals
are closed under what is composed. `NumericDomain` then lifts the whole form into exact ratios
before it reasons:

```java
f.coefs().forEach((atom, coef) -> coefs.put(atom, Rational.of(coef)));
...
Rational.of(f.constant())
```

`Rational.of` on a finite decimal is exact, so the third that `3 * x <= 1` puts on `x` is derived
in exact arithmetic and was never a `BigDecimal`. The rounding that would make this decision
urgent is not happening.

What changes it is ADR-0116. `-1 / 2` becomes an expression whose value is a coefficient, and:

```souther
guard y < -1 / 2 * x + 30
```

has an affine meaning whose coefficient is not a finite decimal. Two things are missing at once:
the grammar does not admit `/` at all, so the guard is read as no form rather than as a form with
a fractional coefficient; and the representation could not hold the coefficient if it did.

So the affine reading has to decide what division means to it, and once it admits one, its
arithmetic domain is no longer closed over finite decimals.

The semantic need to change `LinearForm` follows ADR-0116. A resource question stands apart from
it and is already present: `Rational.of(BigDecimal)` builds `BigInteger.TEN.pow(scale)` to embed a
decimal, so a compact Decimal of a large scale already costs what its scale says at the boundary
this decision moves. The representation rule below removes that as well, and would be worth
having if the affine reading never changed at all.

## Decision

### The affine reading admits division by a constant

A quotient is affine where its divisor is a constant. What counts as constant is read, not
spelled: a divisor is constant where reading it as an affine form yields a form with no
coefficients.

```text
form / divisor, divisor read as a form with no coefficients and a non-zero constant
    = form scaled by the reciprocal of that constant

form / divisor, divisor read as a form with any coefficient
    = not affine

form / divisor, divisor read as the constant nought
    = not affine
```

So these read alike:

```souther
x / 2
x / (1 + 1)

let two = 2
x / two
```

and these are not affine:

```souther
x / y
1 / x
```

A zero divisor makes no form. The operation aborts where it is reached, so there is no value for a
form to be about, and building one would state an arithmetic meaning for an expression that
answers nothing.

Reading the divisor as a form rather than as a literal is what keeps ADR-0111's rule: a name given
a constant is read through to the constant, so extracting `let two = 2` changes what an author
wrote and not what the reading makes of it.

### Affine interpretation carries exact coefficients

`LinearForm<A>` represents its constant and coefficients with the compiler's exact ratio type
rather than `BigDecimal`.

Conceptually:

```text
LinearForm<A> =
    exact constant
    + Σ exact coefficient · atom
```

Int and Decimal constants are embedded exactly when the affine reader encounters them, and a
Rational expression admitted by ADR-0116 is read as the same exact mathematical value.

`NumericDomain` then receives the form in the domain it already reasons in, and the lift through
`Rational.of` at its boundary goes away rather than becoming a rounding step.

### Exact coefficients do not change a position's carrier

An exact coefficient says how a numeric expression relates its atoms. It does not say what values
those atoms themselves may take.

An Int input remains on the Int lattice and a Decimal input remains on the Decimal carrier. For:

```souther
guard y < -1 / 2 * x + 30
```

with `x: Int` and `y: Int`, the affine reader carries the coefficient `-1/2` exactly, while `x`
and `y` remain integer positions.

Exact coefficients therefore introduce neither Rational input positions nor Rational ON points,
and the distinction between an exact ratio used in reasoning and a `Place` on a carrier remains.

### Conversion to a carrier happens only at the carrier edge

When an exact derived result must become a value on a Decimal or Int carrier, that conversion is
performed where the carrier is known.

That edge is responsible for whether an exact ratio:

* is itself representable on the carrier;
* must be widened outward for a bound;
* determines that no carrier value exists at that exact point.

`LinearForm` does not make that decision. This keeps exact arithmetic and carrier granularity as
separate concerns.

### Exact Decimal embedding must remain compact

Embedding a Decimal into compiler exact arithmetic must not eagerly materialise `10^scale` merely
because a mathematical fraction can be written with that denominator.

A Decimal compact in the source representation must not cause work proportional to its scale
solely by becoming an affine coefficient. This is where the eager `BigInteger.TEN.pow(scale)` the
current embedding performs goes. The canonical representation that satisfies the rule belongs to
the implementation.

### The compiler's ratio and the language's Rational are two types

ADR-0116 gives the name `Rational` to the language type. The compiler's
`souther.compiler.numeric.Rational` takes another — `ExactRatio` — and keeps its contract: the
exact scalar that compiler numeric reasoning is done in, used by `LinearForm` and `NumericDomain`,
and not the runtime carrier of a model's value.

They hold the same mathematical domain, so sharing one implementation is the obvious question.
The reason not to is the boundary the compiler already draws.
`TheRuntimePackageIsTheBackendsToNameTest` refuses any mention of `souther.runtime` from the
areas that reason about what a declaration is — `types`, `check`, `stdlib`, `semantics`,
`partition`, `inputs`, `core`, `flow` — because what a declaration *is* and what one backend calls
it are two things. The runtime carrier of `Rational` is the JVM backend's physical representation
and would be another backend's to choose differently; an analysis reasoning in it would be one
whose soundness depended on which backend was linked.

The alternative is a third target-neutral module holding an exact ratio both could use. That buys
one shared implementation for the cost of a new architecture boundary maintained for a single
type, and this decision does not take it.

`numeric` is in neither set that test names, so the rule it holds does not currently reach the
package this exact ratio lives in. It is added to the target-neutral set, which is what makes this
paragraph a rule rather than an intention.

## Alternatives

### Keep `BigDecimal` and clear denominators where a form becomes a constraint

```text
y < -1/2 x + 30
```

normalises to:

```text
2y < -x + 60
```

whose coefficients are whole numbers, so `LinearForm` could stay on `BigDecimal` and the exactness
would be recovered at the constraint edge.

It answers a different question from the one `LinearForm` answers. A form is what an expression
*comes to*, not a comparison against nought: clearing denominators preserves the relation and not
the value, and `-1 / 2 * x + 30` has a value at every `x` whether or not anything compares it.
Every reader that asks what an expression came to — the adequacy measure reads a rule for the line
it draws, not only the check that discharges it — would get a form scaled by a factor that came
from a comparison it is not making.

It also puts two accounts of one expression's arithmetic back where ADR-0111 left one: the reading
would hold approximate coefficients and the constraint step would hold exact ones, and a named
intermediate value read at the first would not agree with the same expression read at the second.

## Consequences

The affine grammar admits `/` by a constant, so a model writing an exact coefficient has its rule
read rather than silently unread. A divisor with an atom in it is still not affine, and an author
whose rule goes unread for that reason is in the case the grammar already had.

`LinearForm` no longer uses `BigDecimal` as its arithmetic domain, and `NumericDomain` no longer
lifts a form into ratios at its own boundary — one exact scalar reaches both.

The rename off `Rational` removes the implication that the compiler's analysis object is the
runtime representation of ADR-0116's language type, and `numeric` joins the packages that may not
name the runtime package.

`Place` and the carriers remain distinct. A third can take part in exact reasoning without becoming
a value a Decimal or Int input can take.

Readers of affine forms acquire no rounding rules. Any approximation or outward rounding stays with
the edge that turns an exact result into a carrier-specific bound.

## References

* ADR-0111: an environment answers with the value a name denotes, never with the form a reader
  makes of it
* ADR-0116: division answers an exact Rational quotient
* Specification: `[#invariant-discharge-arithmetic]`, `[#example-partition]`,
  `[#example-adequacy]`
* `souther.compiler.check.AffineForms`
* `souther.compiler.numeric.LinearForm`, `souther.compiler.numeric.NumericDomain`
* `souther.compiler.types.TheRuntimePackageIsTheBackendsToNameTest`
