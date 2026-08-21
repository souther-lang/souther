# ADR-0109: Relational knowledge about an input is asked through one boundary

Status: Accepted. Fixes where a question about several input positions at once is answered.

## Context

Everything the reading of an input hands over is per position. `Position.numericDomain()` is that
position's range, the admissible values are that position's, the unread reasons are about that
position. A rule that relates two positions divides neither of them, so nothing under
`souther/compiler/inputs/` had a unit for it.

ADR-0107 gives the interval algebra the relation and PR #906 makes each position's range take it in.
Neither reaches across the boundary, because the boundary has no form to say anything about. What a
caller with a form in hand could do was compose the per-position answers, and a product of
per-position answers cannot carry a relation.

Two fields each running from none to five, held together at five by their record, compose to a sum
running to ten. A guard cutting that sum at eight then drew a border on a quantity the model never
arrives at, the rows for it were rows nobody can write, and the report said of each that every value
tried had been refused.

The same loss appeared once more, and not as the same symptom. A search for a row at a point of a
form was handed the ends of each position and walked the box between them. Where the record holds
two fields three apart, each position's own range is already narrowed by the relation and their sum
already runs exactly as far as the form does — and the box still has a corner the rules refuse. The
search offered an assignment in the corner, the row was refused at construction, and one refused
candidate was reported as every value having been tried, of a point another pair stands at.

Conditioning the rules on an assignment was not missing. `FieldDomains` has taken a settled map since
#479, and two searches in `partition` already used it: a record composed field by field, and a
parameter chosen a position at a time. Both reached past the reading of the input into the reading of
the declarations, both spelled a position the way the declaration does and translated it themselves,
and one of them walked the positions again although the walk is what the reading of an input exists
to own. The third search never found the capability and took the box.

So the capability existed and had no boundary. A search written without one either re-derives it or
goes without, and the count so far is two and one.

## Decision

The declarations reaching a behavior's input are asked through one boundary, in the vocabulary of
that input's paths and forms.

`Quantities` answers where a form over several positions runs, where one position runs, what is left
once positions are fixed, and why nothing is left. Conditioning is a refinement of what is asked
rather than a second reading: fixings accumulate and the declaration is read once from the top, so
fixing nothing changes nothing, fixing twice is fixing both, and the two orders agree — of what is
left and of what is proved empty alike. Which route proved an emptiness is not observable, or a cache
and an arithmetic would decide what the model says.

What it answers is the declarations reaching the input, intersected with what each of its numeric
terms guarantees of itself, intersected with what is fixed. An answer is therefore at least as tight
as the box of the positions it is over: a border can go away for being asked about properly and can
never appear. A count is never negative and no clause writes that down, which is why the intersection
with the term's own guarantee is part of the meaning rather than an optimisation — a value fixed
below none is proved impossible where no reading of the clauses refuses it.

A term is queryable where its path is one of this input's. Which numbers a path is measured at is not
settled by the reading of the declarations alone: a bare list nothing bounds becomes an axis about
its length where a body measures it. A term at a path the input does not have is the caller's
mistake and is refused as one — answered as an emptiness it would be a bug wearing the words of a
contradiction in the model, and answered as unbounded it would be one wearing the words of a model
that says nothing.

Rules reach an input from the declarations of its parameters and from nowhere else, so two parameters
are related by nothing. A form spanning both is answered by solving each parameter's part of it
against that parameter's rules and adding the results: the parts stay forms and only the answers are
added. That composition depends on nothing relating two parameters, and a behavior whose own clauses
relate them is the day it changes.

**A capability, not an answer.** Asking the declarations a further question takes a way of reading
them, and what a question is answered with is compared as a value by whatever decides that a compile
changed nothing. So `Quantities` is built where it is used and never kept in `InputDomain`, which
holds what the behavior takes and nothing that reads it. It is built once per walk and handed down:
one per comparison would read every parameter of a behavior once per comparison written about it.

**Knowledge, not search.** What is answered is what the rules leave. Where a row goes, how long to
look for one, and what follows from having given up stay in `LevelRealizer`. A search reads the rules
again as it fixes positions and skips what they leave nothing beside; past a budget it carries on
against what they left before anything was fixed, which is wider and refuses nothing it would have
kept. Exhausting a superset with no solution is still a proof, so what the search may conclude does
not depend on how much of the budget it spent.

`LevelRealizer` walks what `Quantities` soundly leaves, which the actual set is a subset of.
`Impossible` is sound because of the direction of that inclusion and not because the two are the
same: nothing here claims the reading is exact.

**Two callers have not moved.** `Partitions.composed` and `Generator.conditioned` still read the
declarations again themselves. Both want a second answer of the same reading — how much a position
must hold, beside where its values run — which this boundary does not carry. A test over the compiled
classes names them, and names them as what has not been moved rather than as exceptions: a third way
round the boundary fails it.

## Consequences

`Cutting` no longer composes a reach out of per-position ranges, and `Partitioning` carries the
reading rather than a map from term to bounds. `Position.numericDomain()` and
`Quantities.runsBetween(term)` were measured against each other over every position the conformance
corpus reaches before the second was allowed to answer for the first; they agreed everywhere, on a
corpus that reaches twenty-four positions of which eight say anything, so what carries the claim is
the checked-in answers and the suite rather than that measurement.
