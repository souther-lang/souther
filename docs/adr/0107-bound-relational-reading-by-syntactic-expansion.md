# ADR-0107: Bound relational reading by syntactic expansion

Status: Accepted

## Context

`AdmissibleValues` stores a `ValueSet` per position, so it can represent only a Cartesian product of
per-position values. It is what answers `[#what-a-position-admits]` — the rule that a field's
position admits what the record's clauses leave it, which the spec states with `startsAt < endsAt`,
a clause relating two fields.

Approximating a choice by its product hull is a safe upper approximation. However, once correlations
between positions are lost, a later `meet` can make the per-position projections wider than the true
projections. Projection distributes over union, `π(R ∪ S) = π(R) ∪ π(S)`, but only one way over
intersection, `π(R ∩ S) ⊆ π(R) ∩ π(S)`. So a choice reaching across positions leaves every
projection correct, and the next conjunction is where the width arrives. Issue #877 is the defect
that exposed this: every rule read, and `a` reported as `{"5", "6"}` where only `"5"` can stand.

The goal is not to preserve every reading as an arbitrary relation. Instead, Souther preserves
correlations as a finite union of Cartesian products when the expansion is small enough, and falls
back to the existing product-hull domain otherwise.

Three decisions are important here:

1. resource admission is based on syntactic expansion cost;
2. the reading domain is chosen before evaluation, rather than by dynamic widening during the fold;
3. exactness flags represent proof guarantees, not semantic truth.

## Decision

### Use syntactic expansion cost for resource admission

Before reading starts, compute an upper bound on DNF expansion using the same `(Core, polarity)`
recursion followed by `ClauseReading.read`.

The cost is defined as:

- positive `AND`: multiply child costs
- positive `OR`: add child costs
- negated `AND`: add child costs
- negated `OR`: multiply child costs
- any other expression: `1`

Addition and multiplication saturate at `dnfExpansionLimit + 1`.

The cost of one declaration is the product of the costs of its clauses, because clauses are combined
by conjunction.

This bounds the whole computation and not only its result. Every partial product of the clause costs
is at most the declaration's cost, and inside a clause the cost of a subexpression is at most the
cost of the clause containing it. So a declaration admitted under the limit cannot exceed it at any
point of the fold, and no second, dynamic control is needed to hold the intermediate combinations
down.

What the limit governs is the reading of a declaration's `invariant` clauses. That is the whole of
what this domain is built from: the reading is constructed in one place, from clauses each carrying
the invariant it came from. A `guard` reaches the check by another path and is not bounded here.

The limit is intentionally based on syntactic expansion, not on the number of semantically distinct
alternatives after normalization.

Determining the normalized number of alternatives requires performing expansion, normalization, or
both. Those are precisely the operations whose resource cost the admission check is intended to
avoid.

Therefore duplicate alternatives do not refund budget. For example:

```text
A || A || B
```

has cost `3`, even if normalization could later remove the duplicate `A`.

### Choose the reading domain before the fold

The reading domain is selected once, before evaluation begins.

If the syntactic expansion cost is within `dnfExpansionLimit`, the reading is represented as a finite
union of Cartesian-product boxes.

If the limit is exceeded, the reading uses ProductHull mode, which corresponds to the existing
`AdmissibleValues` domain.

So the reading of a declaration is two passes and not one. The first saturates the product of its
clause costs and settles the domain; the second reads every clause in that domain. Deciding per
clause inside the existing loop would be deciding after the fold has begun.

The implementation does not switch from the relational domain to ProductHull while folding `join` or
`meet`.

This eliminates dynamic widening decisions whose result could depend on fold structure or evaluation
order.

The cost model itself is invariant under reassociation and operand reordering of the same `AND` and
`OR` structure because it interprets `OR` as addition and `AND` as multiplication over natural
numbers.

It is intentionally not invariant under Boolean identities such as idempotence, absorption, or
semantic equivalence in general.

### Treat exactness as a proof state

Exactness does not state semantic truth directly. It states what equality the implementation can
guarantee, and it is held where the proposition is quantified:

```text
relationExact()       := tangled.isEmpty()
projectionExactAt(p)  := !widened.contains(p)
```

`tangled` is the positions whose correlations the reading is no longer guaranteed to represent, and
`widened` the positions whose `at(p)` it cannot guarantee is the true projection.

`relationExact()` means:

> The implementation guarantees that the represented relation is equal to the true tuple relation
> admitted by the rules that were read.

`projectionExactAt(p)` means:

> The implementation guarantees that `at(p)` is equal to the true projection of that relation at
> position `p`.

Therefore:

```text
relationExact()       => the represented relation is actually exact
!relationExact()      => exactness is unknown

projectionExactAt(p)  => the projection at p is actually exact
!projectionExactAt(p) => exactness at p is unknown
```

The converses do not hold.

Relational precision is one proposition about a reading and projection precision is one per position,
so only the first is a single answer. Read as a single answer, the second can say no more than that
some position is not shown exact — and a caller asking about one of them is handed that sentence
about each, which is the other quantifier and is false wherever a clause of its own answers for a
position.

For example, an inexact ProductHull relation can later be intersected with another relation so that
the resulting relation happens to become exact again. A conservative transition rule may still leave
`relationExact()` false.

This is intentional. Future analyses may prove additional cases exact by changing `false` to `true`
without changing the type or its contract.

`Completeness` follows the same proof semantics:

- `Complete` means equality with the true projection is guaranteed.
- `Wider` means equality cannot be guaranteed.

`Wider` therefore does not imply that the result is strictly wider in reality.

## Consequences

### Relation and projection precision have different lifecycles

Loss of relational correlation does not immediately imply loss of projection precision.

A ProductHull join across multiple positions can produce:

```text
relationExact()      = false
projectionExactAt(p) = true, at every p
```

A later `meet` can make that lost correlation relevant to a projection, at which point projection
exactness can no longer be guaranteed.

These states must therefore remain separate.

They must not be collapsed into a single set of widening reasons. Doing so would cause a reading to
report `Wider` as soon as relational correlation is lost, even when all current projections are still
guaranteed exact.

Internally they are two sets of positions rather than two flags. A flag for the projections cannot
express the answer at all — its negation is about the reading and the question is about a position —
and carrying `relationExact` beside them rather than deriving it from `tangled` would let the two
come apart. Only one representation-level source of lost relational precision exists today, so
neither set needs to say which it was.

The outward diagnostic remains:

```text
Completeness =
    Complete
  | Wider(NonEmptySet<Widening>)

Widening =
    RuleUnread(UnreadReason)
  | AlternativesNotSeparated
```

`AlternativesNotSeparated` is emitted only when projection exactness can no longer be guaranteed.

### ProductHull remains the compatibility domain

ProductHull mode is intended to preserve the observable behavior of the previous `AdmissibleValues`
implementation, except for the corrected `Completeness` result required by issue #877.

This equivalence is verified for observable operations such as:

- `at(p)`
- `guaranteedAt(p)`
- `speaksFor`
- `standing`
- `dropped`
- bottom / `Nothing` behavior

### `Nothing` remains distinct from an empty union

A reading is modeled as:

```text
Reading =
    Nothing(...)
  | Alternatives(non-empty boxes, ...)
```

`Nothing` is not represented as an empty union of boxes.

Treating it as an empty relation would allow the implementation to infer stronger cross-position
impossibility than the current model permits.

Its behavior under `join`, `meet`, `at`, `guaranteedAt`, `standing`, and `dropped` is therefore
specified separately.

`Nothing` carries a **bottom residue**: the per-position record the arithmetic was holding when it
learned that nothing satisfies the rules. The residue is not the relation's projections, which are
all empty once the relation is. It holds positions left no value beside positions a rule narrowed
and left values at, and both are answered with, so that a reader asking which position was left
nothing gets the answer the reading had.

Narrowing it to the positions every dead alternative agrees are empty does not reproduce the
previous behavior. Measured:

```text
(a == "1" && a == "2") && b == "3"

    at(b)   {"3"} before, ANY once the residue keeps only what is commonly empty
```

Nothing about the residue says whether a reading is bottom — that is the case's to say. A reading
shown to admit nothing from outside carries no position at all, so a residue read for an empty set
answers it backwards. Telling a worked-out product from the absence of one is asked in exactly one
place.

A conjunction and a choice differ in what a side that admits nothing leaves behind, and both are
right. A rule stated beside an impossible one was still stated, so the conjunction answers with the
values it worked out; an alternative nobody can take puts nothing under obligation, so the choice
keeps only what every alternative agrees is empty.

### Exactness is about a reading that holds alternatives

`relationExact` and `projectionExactAt` are asked of a reading that holds alternatives. Where it
admits nothing, `at` answers from the residue rather than from a relation, so there is no projection
for an answer to be exact about, and a caller asking is asking about a position no value ever stands
at. Consumers do not ask it there: a declaration the rules leave no value is owed that it has no
values, which is said elsewhere.

### The policy is owned by the compilation

`ReadingPolicy` is an input to the query graph. Query keys read it at the boundary where they hand
work to analysis and pass its value down; nothing that reads a declaration constructs one.

This is not tidiness. The same declaration is read by the coverage path, by the cardinality
fixpoint, and by the walk that bounds a reduction step. A policy constructed where it is needed can
differ between two of them — each sound, each answering a position differently — and the difference
would not appear in any diff. The policy is therefore a required argument on every path that reads a
declaration, so a path that omits it does not compile.

## Rejected alternatives

### Budget by normalized semantic alternatives

Rejected.

A deterministic normalized alternative count can be defined, but obtaining it requires expansion or
normalization before the resource-admission decision can be made.

That defeats the purpose of the admission check.

### Dynamic widening during `join` or `meet`

Rejected.

Switching domains only after an intermediate number of alternatives exceeds a limit makes precision
depend on how the fold is structured and evaluated.

The domain is therefore selected before reading starts.

### A single widening-reason set for relation and projection precision

Rejected.

Relational correlation can be lost while every per-position projection remains provably exact.

The two states have different lifecycles and must remain distinct.

## Policy

`dnfExpansionLimit` is 64, and the domain decision applies to the whole declaration: every clause of
one declaration is read in the same domain.

The limit is a guardrail against pathological expansion and not a precision setting. Measured over
the compiler's own suite — 68,725 readings, 42,377 clauses — the largest cost any clause reaches is
5, and 98.97% of clauses cost 1. Over the bench corpus, which is whole applications, every one of
3,740 clauses costs 1. Nothing in this repository is read in ProductHull mode at any limit of 8 or
more.

So 64 is not an optimum derived from those numbers. It is a conservative value with a wide margin
over anything observed, and what the design needs is that a finite limit exists, not that it is this
one. The number is policy and may move; the representation and the exactness contracts above do not
move with it.

Deciding per clause rather than per declaration was weighed and dropped. Its precision advantage
over the whole corpus is zero, because no reading exceeds any usable limit, while it would let an
unrelated clause added to a declaration change how an existing clause is read. Stability is the
reason, and simplicity of the contract follows from it.

Because the default is never reached by real input, the conformance suite cannot detect a regression
in ProductHull mode. The fallback is held instead by tests that set the limit themselves, at a limit
no choice fits under:

- the witness of issue #877 is answered exactly at the limit a compilation sets, and reports
  `partition_values_not_separated` at a limit that merges — end to end, in a document;
- a declaration the rules leave no value is told nothing about how its values were held, either way;
- a clause written at one position has nothing to say under either reading;
- what a test reads under is what a compilation reads under, checked against the compilation's own
  input.

The cost model is held separately, on the fold that computes it: a denial counts what the clause
under it counts denied, brackets and operand order do not change the count, a count that runs past
the limit saturates without overflowing, and a declaration costs the product of its clauses.

And the two are tied at run time. After a declaration is read, the number of alternatives it came to
is asserted to be at most what was counted for it. An assertion rather than a check: it is about this
compiler and not about the model, and a throw would be swallowed by the fail-open around the reading
and leave the reading silently dropped. Measured with the count under-reporting a choice:

```text
java.lang.AssertionError: a reading of R expanded to 2 alternatives past a counted 1
```

That is what makes "counting before reading is enough" executable rather than a claim in this
document. It is a second line: the first is that the count and the reading are the same
`ClauseReading` fold over the same clauses, so there is one place where a connective is interpreted
and no second walk to drift from it.
