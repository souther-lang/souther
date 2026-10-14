# ADR-0123: A generated row is chosen among the rows that meet its requirement for the rewrites it tells apart

Status: Accepted. Extends ADR-0121.

## Context

A row composed for a requirement — a point of a line, a rule of the decision, a class of a position,
an arm no row reaches — is built from the values the requirement fixes, the values the way to it asks
for, and, at every position nothing asks anything of, the first value that builds. That last value
decides nothing about the requirement, and it can decide everything about whether a row tells an arm
from its sibling (ADR-0121). A body answering `amount` between two dates and `Megabytes(0)` on either
side of them was handed rows that all held `amount = Megabytes(0)`, and a body answering what it
earned for one case of a sum and `Points(0)` for the other was handed a row for each case holding
`Points(0)`. Every one of those rows answered nothing, so none could tell the arm answering what the
row holds from the arms answering nothing. The replacement measure is read off rows that state an
answer, so on the first round it had nothing to say, and the rows that would settle it were composed
only on a second round, after the first rows had been answered and the strict build had refused.

Every search that hands a person a row takes the first row that meets what it was asked, so the
question is one of all of them, and not of the search for points the question was first seen at.
Which positions a requirement leaves free is not something a search can read off it: a line and an
arm are not one to one, and a value a reading of the body leaves unconstrained can still change which
arms a run goes through.

## Decision

Where a way to run rows is at hand, the row a search hands out is chosen among the rows that meet its
requirement. For a point and for a rule, every whole row the walk composes is offered, and the walk
goes on while the preference passes rows over. For a class and for an arm, the search settles its row
first, under what it holds a row to and what it may spend; then the values of the candidate it settled
on are walked again, and the rows that still meet the requirement are offered. Either way, a row is
run, and run again once for each rewrite the replacement measure would ask of a row through the arms
it went through — a sibling that is another program, standing at every site of the arm, and carried at
every one of them. Which rewrites those are has one answer, read by the measure and by the composer
alike, so a row is never chosen for a question its answer will not be read for. The first row whose
every such rewrite answers it differently is taken. Where the preference is not satisfied within a
fixed number of rows of its own, the row that told the most rewrites apart is taken, the earliest of
those.

Only rows that go the way the first row went are compared: the same arms, and every condition coming
out the same. What the other measures read off a row is which arms it reached and how its conditions
came out, so the row taken covers what the first row would have covered, and the only thing the
preference changes is which rewrites the row tells apart. The same way is also the same combination
filled and the same guard passed, so a row for an arm or for getting past a guard stays one. What a
way does not settle is held as well: a row for a class still stands in every class it was pinned to.
A row whose run answered nothing is never taken over the first.

The preference is never a condition. The first row that meets the requirement is kept whatever the
runs said: a requirement whose arms no row tells apart is still one a row is handed out for, and
reaching the preference's figure leaves nothing owed. Nothing the preference finds is evidence. A
composed row answering differently under a rewrite is a question put to a person, and the measure
reads only the rows whose answers are written. Finding no row that tells a rewrite apart proves
nothing about the rewrite.

A row is run once however many searches compose it. The preference runs rows the searches did not, and
a search may then compose one of them; what each row came to is kept where the way rows are run is
held, and a search counting what it may spend counts only the rows nothing ran before.

## Alternatives

ADR-0121 refused composing the witness inside the per-position choice of values, because a filler
choice would come to depend on the program run and a value passed over would read as one refused.
This is not that. The choice is among whole rows that all meet the requirement, after every position
has a value, and a row passed over is never read as refused: the walk's own account of what it took,
passed over and stopped on is what lets the preference pass rows without the requirement turning into
one nothing was composed for. The filler choice does depend on the run now, and that is the decision:
the runs only rank rows the search has already accepted.

Holding a class's or an arm's rows to the preference inside the search was refused. What those
searches hold a row to may spend runs of their own budget, and asking it again of every row the
preference looks at would spend that budget on a choice the search has already made, and change what
the search says it spent.

Changing the first value of an unconstrained number from zero was refused. It suits this model and
would lose the rows where zero is the value that matters.

Composing a separate row for each rewrite on the first round was refused. Those rows are what the
search for an undecided rewrite composes once rows exist; composed on the first round, they would
double the rows a person answers where one row for each requirement can carry both questions.

Applying the preference only to the rows a block hands a person was refused. The search for a row
answers both the measure, which asks whether a row stands there, and the block, which offers the row.
Composing the offered row again at the block would be a second search of the same requirement, and
which of the two a measure, a settlement or an offering reads would become a question of its own.

## Consequences

The search for a row costs more wherever rows can be run, in the measure as well as in `--generate`:
each requirement runs its first row and every rewrite of the arms that row went through, and up to the
preference's figure of further rows where the first did not tell them all apart. A later row is not
asked a rewrite once the rewrites left could not bring it past the row kept. Running each row once
takes back what searches spent running the same rows again. The figure is not a budget of the
composing: reaching it stops the preference and not the search, and the requirement is answered
either way.

Which value a free position is written with now depends on the arms of the body and on what the other
positions are, so a row composed for a requirement can change when a rule elsewhere in the body
changes. A test that selects rows by the value of a position a row's requirement does not read selects
rows that were not composed for it. A test that counts on a search meeting values nothing has run has
to leave it more values than the searches before it ran.

A body with no fork whose rows all answer one value is told apart from the body answering that value by
a second row answering another, which is how many rows there are and not which values one of them
holds. This does not reach it.
