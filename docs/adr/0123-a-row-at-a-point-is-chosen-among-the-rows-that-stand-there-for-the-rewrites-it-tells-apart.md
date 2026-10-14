# ADR-0123: A row at a point is chosen among the rows that stand there for the rewrites it tells apart

Status: Accepted. Extends ADR-0121.

## Context

A row composed for a point of a line is built from the values the point fixes, the values the way to
the point asks for, and, at every position nothing asks anything of, the first value that builds. That
last value decides nothing about the point, and it can decide everything about whether a row tells an
arm from its sibling (ADR-0121). A body answering `amount` between two dates and `Megabytes(0)` on
either side of them was handed rows that all held `amount = Megabytes(0)`. Every one of them answered
`Megabytes(0)`, so none could tell the arm answering `amount` from the arms answering nothing. The
replacement measure is read off rows that state an answer, so on the first round it had nothing to say,
and the rows that would settle it were composed only on a second round, after the first rows had been
answered and the strict build had refused.

Which positions a rule leaves free is not something the composer can read off the point: a line and
an arm are not one to one, and a value a reading of the body leaves unconstrained can still change
which arms a run goes through.

## Decision

Where a way to run rows is at hand, the composer offers each whole row it composes for a point to a
preference, and the walk goes on to the next row while the preference passes rows over. A row is run,
and run again once for each rewrite the replacement measure would ask of a row through the arms it
went through — a sibling that is another program, standing at every site of the arm, and carried at
every one of them. Which rewrites those are has one answer, read by the measure and by the
composer alike, so a row is never chosen for a question its answer will not be read for. The first row
whose every such rewrite answers it differently is taken. Where the preference is not satisfied within
a fixed number of rows of its own, the row that told the most rewrites apart is taken, the earliest of
those.

Only rows that go the way the first row went are compared: the same arms, and every condition coming
out the same. What the other measures read off a row is which arms it reached and how its conditions
came out, so the row taken covers what the first row would have covered, and the only thing the
preference changes is which rewrites the row tells apart.

The preference is never a condition. Every row offered stands at the point, and one of them is taken
whatever the runs said: a point whose arms no row tells apart is still a point a row is composed for,
and reaching the preference's figure leaves nothing owed. Nothing the preference finds is evidence. A
composed row answering differently under a rewrite is a question put to a person, and the measure
reads only the rows whose answers are written. Finding no row that tells a rewrite apart proves
nothing about the rewrite.

## Alternatives

ADR-0121 refused composing the witness inside the per-position choice of values, because a filler
choice would come to depend on the program run and a value passed over would read as one refused.
This is not that. The choice is among whole rows that all stand at the point, after every position
has a value, and a row passed over is never read as refused: the walk's own account of what it took,
passed over and stopped on is what lets the preference pass rows without the point turning into one
nothing was composed for. The filler choice does depend on the run now, and that is the decision: the
runs only rank rows the composer has already accepted.

Changing the first value of an unconstrained number from zero was refused. It suits this model and
would lose the rows where zero is the value that matters.

Composing a separate row for each rewrite on the first round was refused. Those rows are what the
search for an undecided rewrite composes once rows exist; composed on the first round, they would
double the rows a person answers where one row at each point can carry both questions.

Applying the preference only to the rows a block hands a person was refused. The search for a point's
row answers both the measure, which asks whether a row stands there, and the block, which offers the
row. Composing the offered row again at the block would be a second search of the same point, and
which of the two a measure, a settlement or an offering reads would become a question of its own.

## Consequences

The search for a row at a point now costs more wherever rows can be run, in the measure as well as in
`--generate`: each point runs its first row and every rewrite of the arms that row went through, and up
to the preference's figure of further rows where the first did not tell them all apart. A later row is
not asked a rewrite once the rewrites left could not bring it past the row kept. The figure is not a
budget of the composing: reaching it stops the preference and not the search, and the point is
answered either way.

Which value a free position is written with now depends on the arms of the body and on what the other
positions are, so a row composed for a point can change when a rule elsewhere in the body changes. A
test that selects rows by the value of a position a row's point does not read selects rows that were
not composed for it.
