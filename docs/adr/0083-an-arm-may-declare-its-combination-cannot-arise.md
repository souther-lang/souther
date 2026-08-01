# ADR-0083: An arm may declare the combination it covers cannot arise

Status: Accepted.

## Context

A statutory table indexed by two banded sums is written as a nested `match`, which is what makes
adding a band a compile error in every place that has to answer for it. Some such tables have blank
cells, because the two axes are not independent.

`example.employmentinsurance` in souther-examples writes the basic-allowance matrix of 雇用保険法第23条:
five age bands by five insured-period bands, of which two cells are blank in the published table.
Twenty insured years cannot have accrued before the age of thirty, and an ordinary recipient with
under a year is not entitled at all — `judgeBenefitEntitlement` has already turned them away.
Exhaustiveness asks for an arm for each, and there was nothing to write there. Both answered with the
neighbouring cell, which is a number a report will print, and a reader has no way to tell it from the
twenty-three that are real.

Neither blank is derivable where it is needed. The two bands are computed by separate rules from
separate inputs, so nothing in the types `specifiedBenefitDays` sees relates an age to a period; and
what rules out the other cell is the order the caller applies its rules in. A callee sees the same
thing in both: a premise that holds, and that neither its parameters nor any invariant states.

That is why making the compiler prove the arm away does not answer this. Proving needs the relation to
be written down somewhere it can be read, and here it is not written anywhere — the information is
absent, not merely unproven. Reshaping the data so the pair cannot be built does not answer it either:
it would replace one table that is the shape of the published one with a sum per age band, and the
matrix structure the model is checked against — the same period axis across every row — would no
longer be in the code.

## Decision

**An arm may answer `unreachable "reason"`.** The reason is a string literal and is required.

* Its type is `Never`, which fits every expected type. Joined with a type it yields that type, so a
  `match` is typed by the arms that answer a value.
* Exhaustiveness counts the arm like any other. No arm may be omitted, and there is still no `_`.
* Reaching it aborts, throwing `UnreachableReached`. Souther cannot catch it, and a boundary maps it
  to a 500, apart from a business failure's 400.
* An `example` row that reaches it is a compile error, E1911, carrying the reason and the place it
  was written.
* It may not be written in an `invariant`, and an `example` expectation is a value, so not there
  either. Everywhere else an expression may stand, it may — provided the position states what it
  holds, or a branch beside it does. Written where nothing does, it is E1307.

**It is a statement, not a proof.** The compiler does not decide that the point cannot be reached.
What the form does is put the premise where it is relied on and make its failure an abort. The
specification says this in those words, because a name borrowed from Rust invites the other reading.

## Consequences

The distinction the model could not previously make, it now makes: "the prescribed days for this pair
are 90" and "this pair has no prescribed days" are different program texts, and only one of them
produces a number. Nothing reaches an encoder from a blank cell, because no value is built there.

`UnreachableReached` is separate from `ConstraintViolation` although both abort and both become a 500.
What failed is different — a value against its type's condition, against a premise the model wrote
down — and the two are worth telling apart where an abort is inspected. There are only these two abort
types today; a common supertype for them is a separate question, and not one this decision needs.

The reason being a literal is what makes it more than a way past exhaustiveness. A reason that could
be computed would exist only when the model runs; written as a literal it is available to the reader,
to E1911, and to anything that reads the source. An `unreachable` with no reason is not accepted.

`Never` fitting every position is not the same as every position accepting it. The abort answers no
value, but the code that would have read one is still emitted, and it reads a shape — a long for an
`Int`, a reference for a data. Where the position states a type, that is the shape; where nothing
states one and no sibling branch supplies it at the join, there is none to take, and E1307 says so.
This is the rule `[]` already follows: an expression with no type of its own, written where the
position states none, is reported rather than defaulted.

The misuse this admits cannot be checked. `| InsufficientFunds -> unreachable "the caller checked"` is
the same shape as the blank cell whose reason is the caller's order of checks, and the compiler has no
way to tell one from the other — which is the same reason it cannot prove either. The specification
states the rule and leaves it to the author: where the combination is one the model admits, the arm
answers a value, or the input types change.

## References

- Specification: `[#unreachable]`, `[#algebraic-types]`, `[#invariant-expressions]`, `[#e1911]`
- Issue: souther#239 (finding F30 of souther-examples)
- ADR-0003 (invariant violations abort in the domain), ADR-0029 (platform failures are exceptions,
  not cases)
