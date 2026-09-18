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

### An exact scalar stays exact through the partition geometry

Reading an expression is not where exactness is needed last. What a border is drawn at travels from
the reading to the values `souther examples --generate` writes, and every type on that way holds a
`BigDecimal` today:

```text
AffineReading   form, cut
QuantityKey     direction, per
Cutting         per
LevelSpace      its generator and step
Level           what a quantity counts to
Seam.Scale      per
CutPosition     written, per
LevelRealizer   the coefficients it solves with
BorderQuantity  what it shows of a form
```

Changing `LinearForm` alone would cut the chain one step in.

The geometry gets by today because everything written in a model is a finite decimal. A border at a
third is reachable — `guard 3 * d <= 1` draws one — and it survives as the ratio `CutPosition` keeps:
a `written` level over a `per`. The exactness is in the pair, and the pair is built from two numbers
the source wrote.

ADR-0116 lets the third be written directly. In:

```souther
guard d <= 1 / 3
```

the `written` value is itself a third, and there is no second number for it to be a ratio against.
The same happens to the coefficients:

```souther
guard y < -1 / 3 * x + 30
```

leaves `QuantityKey` a direction it cannot hold and `LevelRealizer` a form it cannot solve in the
domain it solves in.

**An exact affine scalar stays exact through the partition geometry, and becomes an Int or a Decimal
only where a candidate is placed on a carrier.**

`Level` and `LevelSpace` are part of that geometry, and the layer where it is easiest to leave a
`BigDecimal` in the middle of an otherwise exact chain. `BorderQuantity.levels()` builds a
`LevelSpace` — `steppingBy` and `overFiniteDecimals` both take a `BigDecimal` generator — and a
counted level is `Level.ACount(Count at)` over `Count(BigDecimal at)`.

A counted affine level is not a carrier count. `Level.ACount`'s own account already says so: a
number the quantity itself counts to, on no coordinate's carrier. `Count` is the other thing — the
number a value counts to *on* a carrier's order — and the two shared a representation only while
every level a form could take was a finite decimal. For `x: Int`:

```souther
guard 1 / 3 * x < 2
```

the quantity takes the values a third apart, so the lattice itself is over a ratio no decimal
writes. This is a different case from a fractional cut over a whole-numbered lattice, and the two
have to be distinguishable for either to be right.

So `LevelSpace`, its intervals, its generators and its comparisons carry the exact scalar as well,
and a counted level does too. Whether that is `ACount` holding the exact ratio or a level that
separates the carrier case from the exact one is the implementation's to choose; what is decided
here is that it is not a `Count` of a `BigDecimal`.

The mathematics is already there: `AdditiveImage` takes `Map<A, Rational>`, computes its generator
with `Rational.gcd`, and answers `OverWholeNumbers` or `OverFiniteDecimals` over exact ratios. What
is left is the representation the geometry hands it.

The conversion to a carrier stays at the edge the next section describes. `CutPosition`'s pair keeps its meaning — a level and what it is over — with both exact,
and the technique it encodes is no longer the only place exactness can live.

What reaches a fixture is unchanged. Rational answers no external form, so no generated row writes
one: a behavior input is placed on the carrier it declares, and `FixtureTemplate.integer` and
`FixtureTemplate.decimal` are what a row is written with. A border at a third on a Decimal position
has no value on that carrier, and the generator says so the way it does for `3 * d <= 1` — it does
not write `0.333…m` and call it a point on the line.

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

### Clear denominators at the border instead

A comparison is a relation, and multiplying both sides by a positive factor names the same line. So
the geometry could stay on `BigDecimal` by canonicalising each comparison as it enters the
partition:

```text
x < 1/3            becomes   3x < 1
y < -1/3 x + 30    becomes   x + 3y < 90
```

This is a different proposal from the one refused above. That one rewrote `LinearForm`, which holds
what an expression comes to and may not be scaled by a factor a comparison supplied. This one
rewrites only the relation, where the factor is sound.

It is refused for what it costs rather than for what it means. Clearing a denominator multiplies
through by it, and a coefficient that came from a Decimal of a large scale has a denominator the
size of that scale — which is the `10^scale` expansion this decision removes, arriving by another
route and landing on every coefficient of the relation rather than on one embedding. The exactness
would also stop at a boundary again: what the geometry held would be a scaled relation while the
reading held the form, and reconciling them is the two-accounts problem ADR-0111 removed.

## What generation has to keep answering

The rule above is about the values a reader is handed, so `souther examples --generate` is where it
is observable. Four models say whether the chain holds:

```souther
guard x < 1 / 3                     -- Int carrier, no Int value on the line
guard d < 1 / 3                     -- Decimal carrier, a third is no Decimal
guard 1 / 3 * x < 2                 -- the quantity's own lattice is over a third
guard y < -1 / 3 * x + 30           -- an exact coefficient
let slope = -1 / 3
guard y < slope * x + 30            -- the same, through a name
```

The third is the one that says whether `LevelSpace` held. The first two put a fractional cut on a
whole-numbered lattice; that one makes the lattice itself fractional, and a geometry that only
carried its cut exactly would pass the first two and fail it.

The first two are the ones that say whether the carrier edge held. A generated row carries a value
of the position's own type and never a Rational, and a Decimal position whose border falls at a
third gets what `3 * d <= 1` already gets rather than a fabricated `0.333…m`.

The last two are ADR-0111's rule read through this one: a coefficient reached through a name is the
coefficient, so both draw one line.

And these two draw the same border:

```souther
guard x < 1 / 3
guard 3 * x < 1
```

which is what says exact arithmetic left `QuantityKey`'s direction-not-size reading intact.

## Consequences

The affine grammar admits `/` by a constant, so a model writing an exact coefficient has its rule
read rather than silently unread. A divisor with an atom in it is still not affine, and an author
whose rule goes unread for that reason is in the case the grammar already had.

`LinearForm` no longer uses `BigDecimal` as its arithmetic domain, and `NumericDomain` no longer
lifts a form into ratios at its own boundary — one exact scalar reaches both.

The partition geometry carries that scalar too, so a border written at a third reaches the carrier
edge as a third rather than as the nearest decimal to one. `CutPosition`'s level-over-per pair is
no longer the only place an exact position can live, and the models where the written number is
itself a fraction have somewhere to be held.

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
