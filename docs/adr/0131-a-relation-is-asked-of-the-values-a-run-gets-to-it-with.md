# ADR-0131: A relation is asked of the values a run gets to it with

Status: Accepted. Extends ADR-0130: a class is owed a row only where some row can be in it.

## Context

A guard on the way to a relation keeps some values of a place from it. `guard String.length(a) >= 3
else 0` sends every shorter `a` to 0 before the relation is asked, and `guard
B(String.trim(a)) as t else 0` does the same for the strings of whitespace alone. A run that gets
to the relation holds none of them.

The classes of a place were drawn over the values the run gets to the relation with, and the others
were reported as left open: no class held them, and the measure of the place stayed incomplete for
as long as they were there. They were left open in two forms, the lengths no run gets to the
relation at and the numbers of code points of a class it does not, and the report said which.

Nothing could close that. A row that puts one of those values to the relation does not exist, so no
row can meet a class they alone would fill, and the only way to a complete measure was to remove the
guard. The report also said it unevenly. Where the other side of the relation was any string, the
guarded side was read and nothing was left open; where it was a declared type, the same guard left
the same values open. The two readings differed in whether a side happened to be found undivided
first.

A run may also stop on the way: an addition that passes the greatest `Int` ends it before the
relation, and so no run gets there with the strings that need it. That stop is a fact of its own and
is said where the operation is, as every stop at an `Int`'s end is.

## Decision

A relation is asked of the values a run gets to it with. A value no run gets there with, whether a
guard sends it elsewhere or an operation ends the run first, is none of the relation's: it is in no
class of it and it is not left open by it.

The rule that keeps those values away is where they are accounted for. A guard is a decision, and a
row is owed for each way it can be taken. A stop is said where the operation says it. The relation
does not say the same fact again for every place it reads.

What stays open is what the relation is asked of and shows nothing of: the strings whose image under
an operation of the library is not shown. That is a statement about the relation, and a row that
runs the relation can meet it.

A statement still holds every string of its place on one side or another: the true, the false, the
open, and those no run gets to it with, which are there so that a reader of the statement can ask
which of the four a string is in. The reader that makes classes takes the first two as its classes,
the third as what it reports open, and the fourth as no part of the relation.

## Alternatives

**The values left open, as they were.** Said of every guard and every stop, and reported as an
incomplete measure no model can complete. Refused: it asks for a row that cannot exist, which is
the defect ADR-0130 refused for the longest string.

**The values given a class of their own.** A class of the values the guard sends away, owed a row.
Refused: that row is the guard's row, owed already as the way the guard is not passed, and a class
of the relation holding it would say the same obligation a second time under a rule that cannot
tell the row apart.

## Consequences

- A guard that keeps values from a relation changes what the relation tells apart: where every value
  that gets to it can be on the true side, the relation divides nothing at that place, as it does
  where nothing is guarded. The place is reported as divided by no rule rather than as read over a
  region.
- The report of a relation no longer carries which numbers of code points of a class are open, and
  the schema loses that field. What is left open is the images that are not shown.
- A reader of what a statement says makes classes of the first two sides, reports the third and
  leaves the fourth, as ADR-0130 holds the readers of a statement to.

## References

- ADR-0130
