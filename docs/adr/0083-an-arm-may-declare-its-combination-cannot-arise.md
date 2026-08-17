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
* An `example` row that reaches it is a compile error, E1911, carrying the reason and the line and
  column it was written at. Not a file name: this compiler is not given one — a generated class's
  `SourceFile` is derived from its module name — and deriving one would name a file that need not
  exist, and the reading module's when the `unreachable` arrived with another module's inlined
  helper.
* It may not be written in an `invariant`, and an `example` expectation is a value, so not there
  either. Everywhere else an expression may stand, it may — provided the position states what it
  holds, or a branch beside it does. Written where nothing does, it is E1307.

**It is a statement, not a proof.** The compiler does not decide that the point cannot be reached.
What the form does is put the premise where it is relied on and make its failure an abort. The
specification says this in those words, because a name borrowed from Rust invites the other reading.

**The statement is checked where the model's own rules can answer it.** Not proven — held against
what the declarations already say. An arm of the first `match` a body reaches, on one of the
behavior's own input positions, is the end where they can answer: nothing stands between that fork
and the caller, so what may arrive there is what the rules reaching the position leave. A case they
leave standing is one a caller can supply, and the arm is refused where it is written (E1326). A
case behind a second `match`, behind a `guard`, or at a position whose rules this compiler could not
read is one nothing settles; the arm stands, and what could not be settled is said. Every arm of a
`match` on an input position is read this way, wherever in the body it is written — what is left
unread is a `match` on something that is not an input position, which is a claim about a value no
rule of the model speaks about.

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

The misuse this admits is checked at one end and left to the author at the other, and the two ends
are different shapes rather than the same one. `| InsufficientFunds -> unreachable "the caller
checked"` matches a case of the type a parameter is declared as, at the first fork: the declarations
leave the case standing, so the arm is refused. The blank cell is not that shape — it is behind a
second `match`, where what the outer arm fixed is exactly what no declaration states — so nothing
about it can be decided, and both cells of the matrix above stay as they are.

That the claim was *acted on* is what made not checking it cost something. `souther examples` took
the arm at its word and removed the case from what the rows were held to, so the one row that would
have shown the model wrong — the row at that case, which reaching the `unreachable` makes E1911 —
was the row nothing asked for (souther#778). What a row is owed at is read from the declarations
now, and the claim is held against that reading rather than read into it: a case the rules refuse is
already out, a case they admit is E1326, and a case nothing settles keeps what it was owed while the
report says the claim was not proven.

## References

- Specification: `[#unreachable]`, `[#algebraic-types]`, `[#invariant-expressions]`, `[#e1911]`,
  `[#e1326]`
- Issues: souther#239 (finding F30 of souther-examples), souther#426 (an arm answering
  `unreachable` is reported as an arm no row reaches), souther#778 (a case declared unreachable is
  taken out of the measure without the claim being checked)
- ADR-0003 (invariant violations abort in the domain), ADR-0029 (platform failures are exceptions,
  not cases)
