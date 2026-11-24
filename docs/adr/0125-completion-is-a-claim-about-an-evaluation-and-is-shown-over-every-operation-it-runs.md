# ADR-0125: Completion is a claim about an evaluation and is shown over every operation it runs

Status: Accepted. States the contract for evidence that working an expression out completes at a row,
including expressions that apply a function value (`List.map`, `List.fold`, `List.sum` over a mapped
list). It names no structure; how existing mechanisms meet it is decided against it.

## Context

Which number an expression comes to says nothing of whether working it out completed. With `MAX` the
greatest `Int`:

- `List.sum([MAX, 1, -1])` completes. The total is worked out wide and only the final total is checked
  against `Int`, and it is `MAX`.
- `List.fold((acc, x) -> acc + x, 0, [MAX, 1, -1])` stops. The second step computes `MAX + 1`.
- `List.sum(List.map(x -> 2 * x, [MAX, -MAX]))` stops. The final total is `0`, but `2 * MAX` is worked
  out for the first element.

Agreeing on a number, or normalising to the same form, does not carry completion from one computation
to another: the first two come to `MAX` and one completes where the other stops. Whatever carries the
claim "this row is computed" cannot be keyed on the value, and cannot be shared between computations
that only agree on one.

Evidence about the operation itself (what a sum checks, what an addition checks) and evidence about
what is handed to it (the function applied to each element) are separate facts, known in different
places. A claim about the whole needs both, and today nothing says when the two together are enough.

## Decision

### Three claims, not two

For an expression `e` and a row `r` there are three separate claims: `e` completes at `r`, `e` does not
complete at `r`, and neither is shown. Let `C` be the rows where completion is shown, `S` the rows where
non-completion is shown, and `D` the rows where `e` really completes. Soundness is `C ⊆ D` and
`S ∩ D = ∅`, so `C ∩ S = ∅`. The rest is unresolved, and it may hold completing rows, stopping rows, both, or none. Unresolved is never
read as "stops"; it is also never read as "completes". A reading that cannot tell stays at "some
operations told" (`Told.SOME`), which no consumer takes as computed.

### Evidence belongs to an evaluation

Completion is a property of the evaluation of an expression at a row, not of its value, its normal form
or the set of operations it contains. Evidence is therefore about one evaluation: the operation, the
environment it is applied in, and the condition under which it is reached. Two expressions that
normalise to the same value do not share evidence, and evidence for the evaluation of a source
expression is not evidence for an expression a rewrite produced from it.

### Showing completion

Completion at `r` is shown when the evaluation is shown to be finite and every operation it runs at `r`
is shown to complete there, in the order it runs and under the conditions it is reached. Operations that
each complete do not make a run that never ends complete, so finiteness is a premise of its own. It
comes from a termination guarantee that already holds: structural descent, the walk of a finite
container, a helper checked total (ADR-0052). A callee declared `partial` whose termination is not
shown leaves the claim unresolved however safe each of its operations is. Exceeding the evaluation
budget (`E1910`) shows no non-termination and is no evidence of a stop.

- Sequence. `a; b` completes when `a` completes and `b` completes in the environment `a` produced.
  Non-completion is shown when `a` is shown not to complete, or when `a` completes and `b` is shown not
  to in that environment. An operation that would fail is no evidence of stopping unless it is certain
  to be reached.
- Branch. Only the arm taken is run. Evidence is required of the condition and of the arm the condition
  selects at `r`; none is required of an arm it does not select, and a failing operation in such an arm
  is no stop.
- Element-wise application. `List.map(f, xs)` completes when the expression that makes the function
  value and the one that makes `xs` complete, `f` completes at every element, and building the result
  completes. An empty list owes nothing for the applications of `f`, and nothing about `f` is learned
  from it; the expressions that make `f` and `xs` are owed all the same.
- Accumulating application. `List.fold(f, z, xs)` completes when the expressions that make `f`, `z`
  and `xs` complete, `f` completes at every step, and the fold's own work completes. The accumulator of
  a step is the result of the steps before it, so a bound on the elements alone is no evidence about
  the steps. `List.fold((acc, x) -> acc, z, [])` owes `z` although `f` is never applied. A fold with
  `acc + x` runs that `Int` addition at every step, and a sum checks only its total; these are
  different operations and are not given each other's evidence.
- Callee. A callee whose endings are not known contributes none, and the claim stays unresolved.

### The number of applications

A closure may be applied once per element of a container whose length is not known. Evidence about
those applications is either each application shown, or one statement proved for an arbitrary
application and quantified over all of them: over the elements, or for a fold over the steps by
induction. The induction needs an invariant `I(i, a)` of the accumulator and three things shown, not
assumed: `I(0, z)`; that where `I(i, a)` holds the step completes; and that its result satisfies
`I(i + 1, ·)`. An invariant that is only stated promotes nothing. An enumeration that gave up before covering every application is not a
proof of the quantified statement. It is also no proof against it: that applications could not be
listed does not mean they cannot be shown to complete, and `x + 1` over elements all at most `MAX - 1`
completes however many there are. Until one of the two forms of evidence is shown, the claim stays
unresolved.

### Direction

A claim that a row is computed needs every operation it runs covered, so incomplete coverage always
leaves it unclaimed. A claim that a row does not compute needs one operation shown to stop at that
row and certain to be reached there; the rest of the evaluation does not have to be covered. For a
region the stopping operation may differ from row to row: `if flag then x + 1 else y - 1` stops over
`x = MAX, y = MIN` for either value of `flag`, though neither operation is reached in every row. What
is required is that every row of the region has such an operation, not that one operation serves all.

### Moving evidence across a rewrite

Evidence moves from an evaluation to a rewritten one only along an implication that states the
direction. To use completion shown for the rewrite as completion of the original, the rewrite's
completing rows must be within the original's. To use a stop shown for the rewrite as a stop of the
original, the original's completing rows must be within the rewrite's. A relation that is correct as arithmetic does not
give either: `a / b >= 100` and `a - 100 * b >= 0` agree where both are worked out, and `100 * b` can
stop where the division does not. Operations run before an expansion into arms are evidence in every
arm; operations run only inside one arm are evidence in that arm only. Having made no reading of the
program is not the same state as having read it and found operations it could not account for, and the
second is `SOME`.

### Decided rows

The three computations above are decided at rows taken from the ends of the type: at `[MAX, 1, -1]` the sum completes, the fold stops, and at `[MAX, -MAX]` the mapped sum stops. In
each, the evidence is the evaluation's own, so none of the three supplies evidence to another.

For a closure applied under a branch only the rows that reach the branch carry its evidence. For an
application count that is not known, the claim is a quantified statement or it is unresolved. For a
callee whose endings are not known, the claim is unresolved.

## Consequences

Showing more can only shrink the unresolved rows: a row shown to complete, or shown to stop, at one
level of what the compiler can prove keeps that answer at every later level. A change that moves a row
from one shown answer to the other is a defect in one of the two proofs, not a refinement, and it is
what a test of the contract asks.

The contract does not decide whether the evidence is held per application, per operation, or as one
quantified statement, and does not decide where a consumer asks for it. It requires only that whatever
holds it is keyed on the evaluation and its conditions, can say "every application" without listing
them, and gives a consumer the answer unresolved wherever it was not shown.

Completion of a general program is undecidable, so the contract aims at no completeness: it asks that
what is shown is sound and that nothing is shown on evidence not shown.
