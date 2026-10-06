# ADR-0121: A row is evidence for an arm where a rewrite of it fails the row

Status: Accepted. Extends ADR-0089 with one measure; the measures it lists keep their meaning.

## Context

Branch coverage asks whether some row goes through each arm. A row that does has shown the arm ran,
and nothing about whether the arm decided anything the row looks at. Issue #2156 is the shape this
takes in a model somebody writes:

```souther
let refund (item) = match item.payer with
    | OutOfPocket -> item.amount
    | Advance     -> Amount(0)
    | CompanyCard -> Amount(0)
```

with every row holding `Amount(0)`. Every arm is reached, every class is covered, the report says
satisfied, and the arm answering `item.amount` could be written as `Amount(0)` without any row
failing. The same issue has a sum whose rows hold nothing to sum: a body answering `Sum(0)` whatever
it is given passes them all.

What is missing is a notion of adequacy the measures do not have: that the rows *discriminate* the
body from a body written otherwise. Mutation testing is the technique that asks it, and its usual
form — many operators, each a new program — is a cost and a vocabulary a model's author did not sign
up for.

## Decision

Discrimination is added evidence for an implemented behavior, beside the arms and the rules, as
ADR-0089 requires of every measure: it does not replace branch or class coverage, and a behavior with
no body is not measured by it.

There are two rewrites and no others. An arm a row stating its answer goes through is rewritten as
each sibling of its fork, run in the same environment. A body with no such arm is rewritten as one
value the rows were seen to answer. Only there: a body whose rows go through a fork is asked about
the fork, and a body whose other arms its declarations prove nothing reaches is the constant it
answers, which no input would ever tell apart from itself. Both are edits of the source an author could make, so a finding reads
against what was written; neither moves an input. A sibling that does the same thing as the arm is
no rewrite of it, two siblings that do the same thing are one rewrite, and a sibling reading the name
its own arm gives a value is no program the body could be written as. The arms are the ones the
branch measure counts, so a helper is rewritten wherever it is declared, as it is measured wherever
it is declared. An arm no row reaches is already owed under its own code and is not rewritten.

A rewrite is a gap only where some input is shown to be answered differently by it and by the body,
and no row's statement fails of it. Rows that fail of it notice it. A rewrite nobody showed to differ
is left undecided, never concluded equivalent: a search that ran out establishes nothing about the
inputs it did not try. Undecided weakens the measure and leaves the verdict undetermined, and
`--strict` refuses only what is shown.

Inputs are varied only to look for such a witness: a row composed and run under both the body and
the rewrite, compared on the same input. The search has a run budget of its own and its own purpose,
`ForAReplacement`, so what it composes is never a row offered for a class or an arm.

The rewrites are carried in the one set of instrumented classes, behind a switch at each arm read
from a per-thread selector, so no class is generated per rewrite. A run under a rewrite records no
probe, and so moves no other measure.

The finding is one warning, E1939, and the document is schema 24 extended without a bump: a
`replacement` measure, a `rewrite_unnoticed` finding joining to it by an obligation id, and a
`rewrite_undecided` weakening.

## Alternatives

Composing the witness inside the per-position choice of values was the first way to get it, and was
refused. Choosing what fills a position knows what that position may hold, not whether a whole row
answers differently under a rewrite; putting the rewrite there would make every filler choice depend
on the program being run, and a value the walk passes over would become a value it refuses. What was
taken instead is the walk over a row's positions telling apart a value it took, a value it passed
over and one it stopped on, so that a search may go past a value its caller does not want without
that reading as every candidate having been rejected.

Per-rewrite classes, the usual shape of a mutant, were refused for cost: a class per rewrite per
fork is a compile per mutant, where a switch in the classes already made costs one run per rewrite.

## Consequences

Models whose rows all hold the constant a sibling answers, or all answer one value, are refused under
`--strict` where they were satisfied. A model with a single row of a behavior with a body is the
plainest case: the body answering that row's value always is a rewrite the row cannot tell apart.

Each row reaching an arm is run once more for each rewrite of that arm, and a rewrite the rows leave
open is searched for. Both are made only at the level that asks for every measure.

What this does not cover is the rest of mutation testing: an operator swapped, a constant nudged, a
condition negated. Those are different rewrites, and adding one is a decision of its own.
