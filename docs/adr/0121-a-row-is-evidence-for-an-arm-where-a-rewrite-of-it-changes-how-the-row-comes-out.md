# ADR-0121: A row is evidence for an arm where a rewrite of it changes how the row comes out

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
each sibling of its fork, run in the same environment. A body with no such arm is rewritten as each
value the rows were seen to answer, one rewrite per value: answering one value and answering
another are two programs, and a row telling one of them apart says nothing of the other. Only there:
a body whose rows go through a fork is asked about the fork arm by arm. Both rewrites are edits of
the source an author could make, so a finding reads against what was written; neither moves an
input. A sibling reading the name its own arm gives a value is no program the body could be written
as, and two siblings that do the same thing are one rewrite. The arms are the ones the branch
measure counts, so a helper is rewritten wherever it is declared, as it is measured wherever it is
declared. An arm no row reaches is already owed under its own code and is not rewritten.

A row tells a rewrite apart where it comes out the other way under it: it holds of one of the two
bodies and fails of the other. A row that fails of both tells neither apart, which is what keeps a
row written wrong from counting for the rewrite that happens to be wrong the same way.

Whether a rewrite is a gap is asked three ways, and two of them are kept apart on purpose:

- **Shown to differ.** Some input is answered differently by the rewrite and by the body, and no row
  tells it apart. That is a gap, E1939.
- **Proven the same.** The source and the model's own rules show the rewrite is the body under
  another spelling. An arm is read down to every answer it can come to, through the forks inside it,
  and the rewrite is the same program where every answer that is not the sibling's lies down a way
  the rules prove no run arrives at — two guards no input passes both of leave the way past them
  answering only the second guard's answer, and rewriting that way as that answer is no rewrite. A
  body is answering one value already where every answer it can come to reads nothing and all of
  them are one expression; what arrives from outside does so by a name, a dependency's answer
  included, so an answer that reads nothing is the same on every run. A rewrite proven the same is no
  obligation and is not asked about.
- **Neither.** A search for an input the two part at found none. That establishes nothing about the
  inputs it did not try, so the rewrite is left undecided, never concluded the same. Undecided
  weakens the measure and leaves the verdict undetermined, and `--strict` refuses only what is shown.

The proof is a narrow one by design: it reads only what is certain without running anything, and
everything it does not prove is left to the search and to undecided. A wider proof can be added
without changing what any of the three means.

Inputs are varied only to look for such a witness: a row composed and run under both the body and
the rewrite, compared on the same input, with its own purpose, `ForAReplacement`, so what it
composes is never a row offered for a class or an arm. How many runs one rewrite may take is a figure
of the measure's policy and not of the generation's: running out of it leaves the measure partial,
so it is a figure of what the rows establish. For the same reason the search the measure makes is
not stopped by how many rows a block may hold; a search for a row to hand a person is, as every row
of a block is. Each way a search stops is said as itself — the runs, a figure of the composing, a
run that came back without an answer — since which one a wider run would have to raise is what a
reader of an undecided rewrite acts on.

The rewrites are carried in the one set of instrumented classes, behind a switch at each arm read
from a per-thread selector, so no class is generated per rewrite. A run under a rewrite records no
probe, and so moves no other measure. Where a method the JVM holds as written would not hold with
its arms' siblings in it, it is written again without them, and the rewrites there are left as ones
the classes could not carry; what the classes carry is what the measure reads, so a measured build
of a model that compiles always compiles.

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

Treating a search that found no differing input as proof the two are the same was refused. It is the
cheaper reading and it is wrong in the direction that matters: a search looks where it looks, so it
would call a rewrite the same exactly where the rows are least looked at. Treating every rewrite no
search separated as undetermined, with no proof at all, was refused the other way: a body answering
a constant, and a guard nothing gets past, would leave models undetermined that every input agrees
about, and the author could write no row to settle it.

Deciding that the body reads nothing by asking only whether it reads its parameters was refused: a
dependency's answer arrives as something read too, and a body answering what a dependency answers
changes with what each row stands it in with.

## Consequences

Models whose rows all hold the constant a sibling answers, or all answer one value, are refused under
`--strict` where they were satisfied. A model with a single row of a behavior with a body is the
plainest case: the body answering that row's value always is a rewrite the row cannot tell apart.

Each row reaching an arm is run once more for each rewrite of that arm, and a rewrite the rows leave
open is searched for. Both are made only at the level that asks for every measure.

What this does not cover is the rest of mutation testing: an operator swapped, a constant nudged, a
condition negated. Those are different rewrites, and adding one is a decision of its own.
