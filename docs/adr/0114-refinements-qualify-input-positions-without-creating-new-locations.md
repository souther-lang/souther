# ADR-0114: Refinements qualify input positions without creating new locations

Status: Accepted.

## Context

The reading of a behavior's input stopped at a sum. `StructuralInspection` answered that a sum is
not made of positions — which is true — and the walk descended only into records and sequences, so
nothing a case of a sum declares was a position of the input. Every field of every case was out of
reach of the partition, of the boundary and of generation, and a behavior taking a sum was measured
on the one axis the sum itself states.

`InputDomain` stated that answer deliberately: under a sum the declaration puts nothing, and a
construction recipe naming one of its cases puts the fields of that case there, which are the
generator's paths and not the reading's. The premise is what turned out to be wrong. What a case of
a sum holds is declared, not chosen by a recipe: a `GlobalQuery` has a `tag` whether or not anything
constructs one.

`realworld` in `souther-examples` declares `data ArticleQuery = GlobalQuery | FeedQuery`, and
`readArticles` takes it. The optionals of `GlobalQuery` are what decide how the `WHERE` clause is
assembled, and `souther examples --generate` proposed a row for none of the combinations, because
the axes were not there to combine. The ten rows that hold the implementation to them were written by
hand.

The same reading is why a name a `match` arm binds named no position: there was no position under a
case for it to name, so a `guard` written inside an arm drew its line on nothing.

## Decision

**A behavior input position may exist only under a refinement of another position. A refinement
narrows which values may stand at a position; it does not move to another position.**

Refinements are therefore part of the typed path of a position. `query@GlobalQuery.tag` denotes
`tag` at the same `query` value under the refinement that `query` is a `GlobalQuery`. Refinement
steps do not consume structural depth.

Every conditional position derives its requirements from that path. A class may add a requirement by
selecting a refinement at its own position. Requirements are compatible exactly when they can be
merged without selecting different refinements of the same position. Coverage and generation use this
same merge; neither maintains a separate account of conditionality.

Structural descent and obligation are distinct. A type says which refined continuations structurally
exist; the obligation policy says which of them a behavior still owes. Input positions are descended
only where both permit it. Conditional descendants are created for the branches the obligation policy
retains, which is not a claim that they are semantically reachable.

A branch exists whether or not anything stands under it. A case that is the whole of a value — a unit
case, and eventually the absence of an optional — is a branch of its position and puts no position
anywhere.

Refinement does not introduce a wrapper position. In particular, a value carried by a newtype-like sum
case, and eventually the value of `Some`, stands at the refined position itself: `d@Approved` and
`x@Some`, not at synthetic `.value` children.

Names introduced under a refinement may denote the refined position.

## Consequences

- Paths can contain refinement steps, and a path is where the requirement of a conditional position
  is read from.
- Incompatible class combinations are outside the coverage denominator, and a row is never offered
  for one.
- A row that does not satisfy a refinement has no occurrence at the positions beneath it. That is a
  row that was read and stands nowhere, and not a row nothing could read.
- Construction follows the same requirements as coverage, so what a report counts and what a row is
  written for cannot come apart.
- The rules read at a position under a refinement are the refined declaration's own, since no clause
  is written across a refinement.
- The optional remains unrefined for now. Nothing about this decision is particular to sums, so
  taking it is supplying a branch rather than a position semantics of its own.
