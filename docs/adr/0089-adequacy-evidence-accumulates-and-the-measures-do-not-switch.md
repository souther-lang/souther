# ADR-0089: Adequacy evidence accumulates, and the measures do not switch

Status: Accepted. Establishes the shape every adequacy measure is reported in.

## Context

A behavior is written before it is implemented. Under ADR-0088 its rows are recorded while it has no
`let` and evaluated once it has one, and a migration spends most of its life with some behaviors on
each side of that line.

That makes "how well do the rows cover this?" two questions that look like one. Before there is a
body, a row can state which case the model owes and which values it will be given; it cannot state
what the model answers. After there is a body it can state both, and there is a new thing to ask —
which arms of that body the rows run through — that did not exist before.

The obvious shape is a mode: measure an injected behavior one way, an implemented one another way,
and switch when the `let` arrives. It reads well in a table and is wrong in a way that is hard to see
until a migration is underway. The point of the exercise is that writing the body does not throw away
what the rows already established, and a report that changes what it measures when the body arrives
cannot say that. Worse, it makes the day the body lands look like progress on a scale nobody moved:
the numbers change because the question changed.

A second temptation is a score. One number per behavior, one per model, rising as the model is filled
in. It is what a dashboard wants. But the number is not monotone and cannot be made monotone: adding a
case to a signature lowers the witness ratio; writing a body creates a branch denominator out of
nothing; a boundary a new `guard` draws is a new obligation nobody has met. Every one of those is the
model getting *better specified*, and every one of them moves the score down.

## Decision

The measures do not switch. A behavior is measured at the same axes throughout, and implementing it
**adds** axes rather than replacing them:

| axis | injected | implemented |
| --- | --- | --- |
| cases of the signature | measured | measured |
| classes the types and invariants state | measured | measured |
| boundaries | those an invariant drew | those, and those a `guard` drew |
| class coverage, and pairs of classes | measured | measured |
| what running the row produced | recorded | held or failed |
| arms of the body | nothing to measure | measured |

No column empties when a body arrives. What was measured stays measured and keeps its meaning.

Evidence is graded rather than counted, and the grades are kept apart rather than reduced to one
set. For an output case: *specified* — a row expects it; *observed* — the behavior was seen to answer
with it; *verified* — a row expected it and the behavior produced it. For an input case *executed*
replaces *observed*, because applying a behavior to a value claims nothing about what came back.

A measure that could not be made says so, as a third value beside met and unmet. A row whose value
could not be read leaves that position undecided, not uncovered.

An unavailable measurement must expose why no value exists. The reason is stored when it would
otherwise be lost, and derived when it is already encoded by the evidence — what the contract
requires is the meaning, not a field. Consumers may interpret evidence but must not reconstruct
measurement meaning from declarations or unrelated report state. Structural non-applicability is
currently represented as `UNAVAILABLE` with a reason of `NO_BODY`, to keep `MeasurementStatus`
stable; that encoding must remain encapsulated by the evidence model, and callers ask
`applicable()` rather than reading the constant.

Nothing is reduced to a single score, at any level.

## Consequences

What is monotone is the structure and not the numbers: the axes a behavior is measured at only ever
grow. That is the property a migration can be run against — no column disappears, so no progress is
lost — and it is stated plainly rather than implied by a rising figure.

A row that failed is still evidence. It did apply the behavior and did see an answer, so it feeds
*observed* even though it feeds neither *specified* nor *verified*. A measure that dropped failing
rows would report the case they produced as one nothing produces.

Three sets per position rather than one is more to carry and more to render, and every reader of the
report has to decide which of the three it means. That is the cost, and it is paid because the three
ask different things of an author: nobody has written down that the model owes this; somebody has and
nothing confirms it; the model gives it.

Undecided as a third value means every consumer handles three states. A report that collapsed it into
unmet would send authors after rows they may already have written.

The reason costs a field on most measures and a check wherever one is built. It is paid because
without it the layer that has to choose a sentence works the reason out from whatever else is to
hand — the row count, whether the behavior is injected, whether the declaration has a body. Each of
those correlates with the reason and is not it, so each such rule is right about the cases it was
written against and wrong about one nobody had in mind: a `>->` composition is implemented, carries
rows, and has no arms all the same. Keeping the reason where the measurement is made is also what
lets `NOT_APPLICABLE` be added to `MeasurementStatus` later without touching a consumer.

Comparing two runs is left out. Quantifying "how much did implementing this behavior reveal?" needs
the two reports matched arm by arm, and an arm has no identity that survives an edit
(<<example-branch-coverage>> numbers them per run). Nothing here pretends otherwise.

Spec: `[#example-adequacy]`, `[#example-pending]`, `[#example-branch-coverage]`
