# ADR-0088: An injected behavior's example is recorded until it can be run

Status: Accepted. Narrows E1902, which until now refused a row on any behavior with no `let`.

## Context

`example` rows on an injected behavior were a compile error. The reason given was that an injected
behavior is implemented in Java, so Souther has nothing to run and nothing to compare — you fake one,
you do not example it.

That reasoning holds for what an example *evaluates*. It does not hold for what an example *states*.
A row is two things at once: an assertion the compiler checks, and a written record of what a
behavior owes. Refusing the row throws away the second to protect the first.

Where this costs the most is migration. A model that a system is being migrated onto starts injected
everywhere: the shape is written first, the bodies arrive one at a time as each rule is read out of
the system being replaced. The inputs and expected outputs harvested from that system — from logs,
from batch expectations, from the regression suite — are exactly the record of what each behavior
will owe. Under the old rule that record has to live outside the model, in a spreadsheet or a JSON
file, which is where it stops being checked and starts drifting from the declarations it is about.

There is a second cost. Those harvested values are the first real data the model meets. Whether they
even satisfy the model's own invariants is the question a migration wants answered on day one, and
the derived Decoder answers it — but only for values the compiler is allowed to see.

## Decision

A row naming a behavior with no `let` is **recorded rather than evaluated**.

Everything the row can be held to without a body, it is held to: its arity, each input built against
its parameter type through that type's derived Decoder (so an invariant violation is E1903), the
expected arm against the output's cases (E1904), and the expected value built (E1903). Evaluation —
resolving fakes, applying the behavior, comparing — is what is skipped, because there is nothing to
apply.

The row is unchanged when the `let` arrives. From that compile on it is applied and compared like any
other row.

Waiting is a normal state, not a defect, so it is **not a compile warning**. A model under
construction would carry one per row, and a warning that is always present says nothing. How many
rows are waiting is reported by `souther examples`.

E1902 keeps one reason: the target is not a behavior at all — a helper `let` of that name.

A `fake` and an `example` of the same injected behavior say different things and both belong. A fake
stands in for a dependency while some *other* behavior's row runs; an example says what this behavior
itself will have to answer. Neither reads the other.

## Consequences

A program that was refused now compiles. This is a change to what the language accepts, not to what
it means; nothing that compiled before compiles differently.

The row's evidence has to be graded rather than counted. A pending row states that a case is expected;
it does not state that the behavior produces it. Whatever reads these rows has to keep the two apart,
which is why an observation carries how far its row got and not only whether it passed.

Three existing tests asserted the refusal and now assert the recording. The test that E1902 still
exists moved to a helper `let` target.

The alternative — a marker on the row, so that waiting is written rather than inferred — was not
taken. It would add a word to the language for something the declarations already say, and every row
would have to be edited on the day its `let` arrived, which is the day the author is least interested
in editing rows.

## References

- spec `example-pending`, `example-evaluable`, E1902
- ADR-0068 (a behavior is called when it requires nothing), for what an injected behavior is
