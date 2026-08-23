# ADR-0113: Axis count is not a resource budget

Status: Accepted. Supersedes ADR-0090 in one respect only — that ADR treats the axis limit as a
budget doing what it is for, and this retracts that. Its decisions about what a partition is, what a
threshold draws, and what a position admits stand unchanged.

## Context

`Partitions.MAX_AXES` was 12. A behavior taking more positions than that had the rest dropped, and
the report said so — `omitted: calc/c.f12 (axis limit)`, with `measurement: partial` at the top.
Nothing a caller wrote could raise it. Issue #969 asked what the number was protecting: the size of
the report, or the cost of the measurement.

It was measured. Neither.

**The report did not shrink.** A dropped axis printed a line of its own, one for one with the line a
measured axis prints. A behavior with 62 positions wrote 62 lines under a limit of 12.

**The cost was bounded where it is incurred, and already was.** `Coverages.PAIR_LIMIT` bounds the
pair space at 20,000 and reports exhaustion as `Measurement.Partial` with
`Weakening.PairSpaceTruncated`. `Generator.MAX_ROWS` bounds the rows one call writes at 200 and
records what the limit stopped it before (#967). The measure itself is close to linear in the axis
count. Measured on a behavior of N fields, at the limit and with it removed:

| model | limit 12 | no limit |
|---|---|---|
| 64 fields × 2 cases | 114ms, 12 axes, 12 rows | 312ms, 64 axes, 64 rows |
| 100 fields × 2 cases | 151ms, 12 axes, 12 rows | 828ms, 100 axes, 100 rows |
| 40 fields × 20 cases | 1499ms, 12 axes, 200 rows | 1241ms, 40 axes, 200 rows |
| 64 fields × 20 cases | 2488ms, 12 axes, 200 rows | 2164ms, 64 axes, 200 rows |

The last two are *faster* without the limit: the row budget binds first there, so dropping to 12
axes leaves the same work to do and adds the dropping. Across the bench corpus and the conformance
models no record reaches four fields, so nothing written here was measured differently either way.

**A count of axes is not a cost.** What the pair space costs grows with the positions *and* their
cardinalities together — 40 positions of 20 cases is a larger space than 100 of two — and what the
row search costs is decided by its own budget. A count of positions is an input to both and a proxy
for neither, which is why the table above has rows going each way.

**And the number did not bound what it named.** The budget was spent in `Partitions.of`, which runs
before the body is read, and only on an axis that was `measurable()` by then. A plain `Int` has no
classes and no cuts until a comparison draws one, so it passed free and became a boundary axis in
`withThresholds` afterwards. Twelve `Flag` fields beside five plain `Int`s the body compares
reported **17 axes** under a limit of 12.

That is the shape of the fault rather than a detail of it. The drop happened at the one point in the
pipeline where the least is known about what is being dropped: an axis dropped in `of` never reaches
`withThresholds`, so what a `guard` would have drawn on it was not merely lost but never knowable.
The order was

    model structure → axis truncation → body semantics

where what the work needs is

    model structure → body semantics → the obligations in full → bounded expensive operations

**And what the author was told was untrue.** `About.APositionPastTheAxisLimit` reached
`GenerationOutcome.NotApplicable.Reason.A_FACT_ABOUT_THE_MODEL` — *this is what the model says
rather than what its rows do not cover, and no row changes it*. The model said nothing of the kind.

## Decision

**Axis count is not a resource budget. Budgets are imposed where combinatorial or generative work is
actually performed.**

Four rules, which the adequacy subsystem is held to. They are about where a limit may be put at all,
rather than about the one constant this removes.

**1. Semantic evidence is never pre-selected by a resource budget.** Every semantic subject the
reading reaches is offered to the readers that measure it. A reading may still fail to derive or
understand one; what it may not do is select the subject away to save work.

The distinction is the whole of the rule and is easy to lose. Souther already has readings that stop
— a walk that goes two levels into a value and no further, a clause whose alternatives
`ReadingPolicy` will not hold apart, a rule this compiler cannot turn into a line. None of those is
a budget choosing which evidence to keep: every position is still there, and what the reading could
not do with it is reported at that position (`notRead`, `rulesNotReached`,
`PositionValuesNotSeparated`). The axis limit was different in kind. It took a position out of the
measure entirely, and a position nobody measured leaves the same absence as one the rows cover.

**2. Budgets guard expensive operations, not semantic inputs.** A limit belongs at the operation
whose cost it bounds, and after the semantic inputs to that operation are known. Pair enumeration,
row generation and cell expansion are such operations. The number of positions a behavior takes is
not one — it is an input to those operations, and per rule 1 not a place to spend a budget.

**3. Every budget exhaustion is observable.** A compiler-imposed loss of evidence is represented in
the semantic result at the point where the loss occurs, and reaches every projection of that result
unchanged — the human report, the JSON document, an API. A limit that fires and hands back a value
saying nothing is worse than the loss it caused: a measure that was weakened then reads exactly like
one that found nothing to say.

**4. Resource policy belongs to the compilation.** A limit is an input the query graph hands to the
analysis, the way `ReadingPolicy` (`Front.Reading`) and `EvaluationPolicy` (`Front.Policy`) already
are, rather than a private constant or a system property read wherever the work happens.

`MAX_AXES` failed 1, 2 and 4. It satisfied 3, and the machinery that satisfied it — `OmittedAxis`
recording what a dropped axis was carrying, `ClosureGap.AxisOmitted` filing it under the measure it
cost, `About.APositionPastTheAxisLimit`, `Adequacy.Kind.PARTITION_OMITTED`,
`WeakeningWord.AXIS_OMITTED`, the report's line and the JSON's array — goes with it. It was a
faithful account of a loss that need not have happened, and a correct taxonomy for an event that no
longer occurs is a ghost.

**What is not yet conforming.** `PAIR_LIMIT`, `MAX_ROWS` and `MOST_CELLS` are private constants no
caller can reach, which is rule 4 unmet, and `MOST_CELLS` drops a group past it with a bare
`continue` and records nothing, which is rule 3 unmet. Tracked in #1005, and deliberately not done
here: moving a limit that weakens a result in silence into a policy a caller can set would make a
silent loss into an officially configurable one, so the accounting comes before the policy.

## Consequences

The JSON schema is version 6. Removing the `omitted` property, which was required, and the
`axis_omitted` and `partition_omitted` words from two enumerations are removals, and the schema's own
rule raises the version for a removal. `adequacy-schema-5.json` stays in the repository as the
contract documents of that version were written against; the serializer emits the version 6 shape
only. A deprecated empty `omitted` array was considered and rejected — it would keep a concept alive
in the output after the domain model stopped having it, which is the arrangement being removed.

The specification loses two passages, both current contract rather than prose trailing the code: one
made the `carriedAnObligation` distinction a normative rule about what dropping an axis costs each
measure, and one listed the axis limit among the things that leave a measure short of what it read.

`GenerationOutcome.NotSupported.Reason.NO_AXIS_AT_THIS_POSITION` stays and is reachable from no
source measured here. Its guard in `atCase` is a disjunction — no partition evidence, a parameter
index out of range, or no axis carrying the case — and the axis limit was only the last of those.
Showing the other two unreachable is separate work, so the answer stays and the test that reached it
through the limit is gone.

Three regression tests hold rules 1 and 2 apart, and one test cannot say which of them broke.
Fifteen divided positions, all measured, holds that a count of positions is not a budget — written
at fifteen rather than at thirteen, since a test at the old ceiling plus one passes again the moment
somebody sets a new ceiling one higher. Twelve declared positions beside five the body divides, all
seventeen measured, holds that no budget runs before the body has been read; it is the case a
count-based budget cannot be made correct for, the five not having been measurable when it would
have run. One declared position beside one the body divides holds the dependency itself — structural
reading, then the body's threshold, then the boundary — so that a reading which stopped producing
boundaries fails there rather than passing for want of positions to lose them at.

Spec: `[#example-partition]`, `[#example-adequacy]`
