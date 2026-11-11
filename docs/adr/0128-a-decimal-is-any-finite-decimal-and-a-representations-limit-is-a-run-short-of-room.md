# ADR-0128: A Decimal is any finite decimal, and a representation's limit is a run short of room

Status: Accepted. Amends ADR-0112: what a `BigDecimal` cannot hold is reported as `OutOfRoom` and
not as `ConstraintViolation`; that a backend does not change a value to fit a host API stands.
Keeps ADR-0009 and ADR-0116.

## Context

ADR-0009 makes a `Decimal`'s identity independent of its scale: `1m` and `1.0m` are equal. ADR-0112
made a Decimal operation abort where the answer's scale left the 32 bits a `BigDecimal` keeps a scale
in, and wrote that range into the specification as part of what the operations mean. Together the two
meant that equal values did not behave alike. A JSON boundary admits `0E-2147483647`; multiplied by
`0m` it answered nought, and multiplied by `0.0m`, which is equal to `0m`, it aborted.

Finite decimals are closed under addition, subtraction and multiplication, so the partiality came
from the representation and not from the values. It was nonetheless a partiality of the language, and
the analysis had to prove where it did not happen. That proof grew: scale laws and scale bounds per
operation, the shape of every operand, walks bounded by the shape of their parts, totals held to the
budget a row is built at, and library bodies read for the room each of their operations asks. Each
issue about a Decimal comparison reached that machinery, and several were defects of it.

`Rational` had the same shape at a different width. Its exponents are 64 bits, and the specification
called that width a bound on what a value is, so `+`, `-` and `*` over rationals were partial too, and
so was every narrowing of a rational to a decimal.

The specification already had a word for the other kind of failure. `OutOfRoom` is what a run reports
when it cannot obtain what computing a defined answer takes, and its definition already counted how
large a whole number the platform's arithmetic builds among the things a run can be short of. A
`BigDecimal`'s scale is the same kind of thing: a limit of the platform's arithmetic and not of the
numbers.

## Decision

A `Decimal` is any finite decimal number and a `Rational` any rational number. No scale, no count of
digits and no width of an exponent bounds which values there are.

So a sum, a difference, a product and a negation of decimals always have an answer, a rounding
answers at every scale, `Decimal.divide` answers at every scale wherever the divisor is not nought,
and a narrowing of a rational to a decimal always has one. Over rationals the same holds of `+`, `-`,
`*`, and of `/` wherever the divisor is not nought. Where the representation has no place to write an
answer, the run fails as `OutOfRoom`: the platform failing, which says nothing about the model or a
value. A `ConstraintViolation` is left for what the language itself refuses — a zero divisor of `/`, a
value no `Int` holds, a text no `String` holds.

The representation is unchanged: a `Decimal` is a `java.math.BigDecimal` on the JVM, and generated
classes expose it as one.

The analysis follows. A Decimal or Rational operation ends no run (`AbortSites`, `KernelContracts`),
it answers everywhere (`WhereAnOperatorAnswers`), and `List.sum` and `List.product` are read at the
number they answer: over decimals and rationals they end no run, over `Int` they end one where an
`Int` total has no place. Everything that existed to show where a decimal operation had room is
removed: the scale laws and bounds, the shapes of operands, the decimal operations a row was asked to
get past, and the scale range the check held a division's scale to. The budget rows are built at stays,
since it is what generation tries and not what exists, and it moves to `DecimalPoints`, which owns how
a decimal of a row is written.

## Alternatives

**An unbounded exponent.** A `Decimal` held as a coefficient and an exponent of any width, and a
`Rational` with exponents of any width, would make running short of room a matter of memory alone.
It changes the type generated classes expose to Java, and with it every caller and the encoders.
The semantics decided here is the same either way, so this is an implementation the decision leaves
open rather than a different decision.

**A bounded domain made consistent.** The range could have been held on the scale a value has with
its trailing zeros removed, so that equal values completed alike. A bounded domain is not closed under
`+` and `*`, so every operation would still need a proof of room, and the machinery this removes would
have stayed.

**A wider fixed exponent.** A 64-bit scale moves the end but does not remove it: squaring a value with
one digit doubles its scale, so a few multiplications reach any fixed width, and the analysis would
still have to prove where they do not.

## Consequences

- Equal decimals give equal answers, and the language never refuses one for its scale. Whether a run
  has room for an operation still depends on how the operands are written — `0.0m * x` wants a scale
  one past `0m * x` — and a model sees that only as the platform failing.
- `OutOfRoom` is reachable from inputs a few bytes long, such as a decimal written at the end of the
  scales a `BigDecimal` keeps. It was an abort before as well; what changed is what it says. A boundary
  handles it as the platform failing.
- A narrowing to an `Int` — `Decimal.toInt`, `Rational.toInt`, `Rational.toWholeNumber` — asks the
  bound of an `Int` of the value's order, in one place, before it builds the whole number, so a value
  no `Int` holds is the language's refusal even where building it would have been a shortage.
- Reading the definitions of a record showed a defect the decimal partiality had been hiding. A place a
  rule defines as a number made of others was certified exact as a box; its values are the image of the
  number, and a product of a quantity of one or two and a price up to ten is never eleven. Only a
  definition whose operators were not shown to answer kept the place from being certified, which every
  decimal definition was and no whole-number one. A place any proven rule relates to a number worked
  out of others now carries that cause itself, a definition among them, and the places the number is
  made of stand where their own rules leave them, as before.
- A rounding, a `Decimal.toInt` and a `Decimal.divide` whose answer has room may still pass through an
  intermediate a `BigDecimal` has none for, such as the power of ten between two far scales. Those
  are worked out on the exact rational and narrowed once, so a run is short of room only where the
  answer is.
- The cost of ordinary decimals is unchanged. They are the same `BigDecimal`s through the same
  operations, and the narrowings through the exact rational run only where a `BigDecimal` has no room.
  Profiled with JFR over the conformance corpus and the analysis tests this change touches, against
  the commit it starts from, the samples differed by less than the runs of either commit differ
  among themselves, and no sample landed in the code added.
- An example row whose evaluation is short of room is undecided and not failed, and the check says
  so (E1941): the expected answer is a decimal the language defines, and nothing about the model was
  found out.
- The analysis that reads a library body used to stop at a declared case such as `HALF_UP`, a
  guard the abort sets had made sure was never needed. With the decimal operations ending no run it
  is needed, and a case of a declared unit type is read as that value.
- A corpus model that weighed each deal by a decimal product, and so asked a reach witness of a
  comparison the product kept unshown, now rounds each deal to whole yen, which an `Int` may not hold:
  the same question, asked for a reason the language states.

## References

- Issue #3131
- Specification: `[#a-decimal-is-any-finite-decimal]`, `[#a-scale-is-used-as-the-number-written]`,
  `[#stdlib-decimal]`, `[#stdlib-rational]`, `[#an-operation-refuses-only-what-its-own-answer-has-no-place-for]`,
  `[#invariant-discharge-arithmetic]`, `[#jvm-abort]`, `[#primitives]`
- ADR-0009 (Decimal does not include scale in identity)
- ADR-0112 (a backend does not change a value to fit a host API)
- ADR-0116 (division answers an exact Rational quotient)
