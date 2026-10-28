# ADR-0124: A derived value cut at several places owes a weight per position and divides none

Status: Accepted. Refines ADR-0090 for a value a computation derives from several positions and cuts
at several places; a value cut at one place divides its positions as before.

## Context

A rule that looks a derived value up in a table compares one computed value against every row's
threshold. In `hr`, `decideRegularly` averages the total remuneration of the payable months and looks
the average up in the standard grade table. The total is a sum of fields, each declared at nought or
above, and each field of each month was divided into classes at the table's lower bounds, together
with their multiples for an average over two or three months.

Those classes do not state an outcome. A value of one field that settles the comparison at one
threshold leaves the next threshold either way, so the grade is not the same through the class and a
row in it stands for nothing beyond itself. The borders of the value already carry the thresholds;
what the classes added was a count of rows owed that grew with the number of positions times the
number of thresholds.

What the classes did not ask for is what a test of a lookup needs besides the thresholds: that each
position is weighed into the value. A wrong constant is shown by a row at a border and a row beside
it (ADR-0090). A wrong coefficient, which includes a position left out, is not: the border can turn
about a point and still pass through it, and a row that writes the left-out position as nought
passes. A domain strategy places points on a border apart from each other for that reason (White and
Cohen, IEEE TSE SE-6(3), 1980).

## Decision

### What is cut: a computation

The weights of the positions are weights of the expression that computes the value, and an
expression is what is written at a call. The comparison is read at each call of the helper that holds
it, and what each call is cut at — which weighings of the positions, at which values — is what the
rows on its borders can say of it. A computation (`DerivedValue`) is the author's comparison and the
calls cut at the same places: it is how the obligation is named and counted, and one position owes
one weight however many calls name it.

That the borders agree is no proof that the calls take their value from one place. A value computed
once and handed to two calls, two calls written alike, and two calls on exclusive branches all look
the same to the borders. So naming them together is not evidence about them together: a weight is
fixed for a computation only where it is fixed for every call of it, each by the rows on that call's
own borders. A value handed to two calls puts the same rows on both, and both are fixed at once. Two
calls on exclusive branches are put to different rows, and the one no row reaches leaves the weight
unfixed. One comparison inside a helper read at two calls with two values — `gradeOf(a + b)` and
`gradeOf(a + 3 * b)` — is cut at different places and is two computations outright.

A derived value is a form over at least two positions: a total, a difference, any weighing of them.

Only a comparison a body wrote draws a computation. What says which one it is, is the copy of the
comparison a call made, and a comparison a clause of a declaration states has no call. Its lines are
never held apart and its positions keep their classes.

### What is decided once

A computation cut at more than one place — more than one weighing at more than one value — does not
divide the positions it is made of. The values of one position that settle the comparison at one
threshold are held as borders of the computation and not as lines on the position. A computation cut
at one place keeps its classes: the values that settle the one comparison are the same outcome
throughout.

Which computations those are is decided in one place, over every line every reader drew
(`DerivedValues.decide`), and the result travels with the partitioning. The classes dropped and the
weights owed are that one decision. A reader that counted thresholds again from the borders would
count over a different set of lines — a comparison that draws no border, two readings folded into one
— and could drop a position's classes with no weight owed in their place.

### What is owed instead

Each position of such a computation owes its weight, once for the computation however many
thresholds the table has and however many positions a window of the table reads. A weight is fixed
where a computation weighing the position otherwise would fail a row. The faults are the ones E1938
holds a border against, one position weighed one more or one less than the model weighs it in the
quantity's own weights, and nothing else. For each such computation the border's own rule is read
against the threshold the model wrote and the value the changed computation works out at a row nearest
the border, and the computation fails the row where that puts it on the other side of the rule than the
model has it. A weight is fixed where both the computation weighing it one more and the one weighing it
one less fail some row, on any border of the call.

This is asked of the rule and not of how the rows are spread. The alternative considered was that the
vectors of weighted values the rows give span the space of the positions, on each side of the border
apart. That is a statement about the rows' independence, and a wrong weight is caught by a row only
where it moves the row across the border. With a position negative on the side where the rule does not hold,
rows on both sides of two borders can be of full rank and still be passed by a computation weighing a
position twice: it moves each of them away from the border on the side the model has it on. Which value
is where the rule holds is the comparison's too, since a strict comparison holds one value further up
than a non-strict one.

What this establishes is no fault of one step in one weight with the threshold the model wrote: a
fault domain stated and not the weights pinned down. A rule weighing a position by two and a half lies
between the weights this tries. E1938 states a wider domain for a border cut at one place, where the
threshold of the line beside it may move as well; the two are separate fault models and neither
contains the other.

Only the readings of a row that stand at a border's point are evidence of it. A row inside a
container has a reading for each element, and one of them standing at the point is no reason to take
the numbers of another: whether a reading stands and what it reads as are asked of one walk, so that
the reading that was found to stand is the reading whose numbers are taken. A row whose answer is
not the model's is evidence of nothing, and a point that could not be worked out may have rows nobody
can name, so a weight is not said to be unfixed past it. A side the border has no value on, because
the type ends there, has no rows and none are asked for; the weight is caught from the side that has
them.

How a row is shaped decides nothing. A row that moves one position alone is one way to fail a changed
computation and not the only one: three rows that each move two of three positions fail every one of
them, and a position weighed by minus one has no row that moves it alone and can still be fixed.

Where nothing was read against the computation, where a border of it was not read and the rest leave
a weight unfixed, or where the exact arithmetic gave out on a row, no claim is made about the weight
and the document says `undecided`. It is not a finding. A row the arithmetic gave out on is left out
alone: what the other rows fix stays fixed.

The obligation is keyed on the computation and the position, never on a threshold: where a row stands
moves with every row written, and an obligation whose identity moved with them would be a new
obligation every run. It is a warning, E1940, and it appears in the document under `partition.weights`
beside the borders, each entry with the word `shown`, `not_shown` or `undecided`.

It is owed only for a value cut at several places. A value cut at one place is no computation shared by
thresholds and owes no weight here; its border is held against the lines one step from it (E1938), which
is where a fault of one step in one weight of that border is asked.

For a value cut at several places E1938 is not asked of the thresholds. The weight is a fault of the
computation, which every threshold reads, so it is owed once, here. A line beside a threshold that
weighs a position otherwise and moves the constant with it is two faults at once: the weight is owed
here, and the constant at the ON and OFF points of each threshold. A fault made of both together is
not among the faults either measure states. A threshold is recognised by the partition having placed
it (`Border.threshold`), and the answer is `OwedByTheComputation` whatever the weights came to: an
unfixed weight is said under E1940 and does not bring the lines beside the threshold back.

What the weights are short of is the weights' to say, since no border carries it any longer. A weight
the rows neither fix nor show unfixed is `undecided` in the document and is a weakening of the
behavior's border measure (`a_weight_not_decided`), so a verdict does not rest on a weight nobody
established.

### What each threshold is owed

A shifted threshold is the fault a border exists to show, and it needs an ON and an OFF point at each
threshold of the table and not at one of them. The points against the line of a computation cut at
several places are owed once for each threshold; the points in the runs beside it are owed once for
the comparison, as before.

A threshold is a threshold of one computation, and two computations never share one. A computation is
the calls of a helper cut at the same places; calls cut at different places are two, and a row on a
border of one is on no border of the other. The line the readings are folded under carries the
threshold too, so that readings of two computations put at the same place are two lines and the rows
beside one are not taken for the rows beside the other.

Within a computation the threshold is the bound the comparison was written against, as the table
holds it (`WrittenAt`). It is read from the comparison before the value it is held against is weighed
and divided, so the bound 63000 held against an average of two months is one threshold with the bound
63000 held against an average of three, though the total is cut at twice the bound in one and three
times it in the other. A row at the points of one of them shows where the bound falls, because the
fault is the bound written wrong. What differs from one place to the next is how the positions are
weighed, which is the weights' to say.

A number two bounds come to is no reason to join them. The bound 63 held twice over and the bound 126
held once are cut at 126 alike, and when the two are read in the branches of one behavior a row
through one branch exercises the bounds of that branch alone.

Where no bound can be told — both sides of the comparison vary, or neither is a number the same on
every run — the threshold is the place the computation is cut at (`CutAt`). Owing more than there is
leaves a point asking for a row; joining what is not one would report a point answered that no row
stands at.

The runs beside a line are owed once for the comparison, whatever threshold drew them, so a point
there does not tell two computations cut at one place apart. The readings of it do: a reading is of
a line at a place and a threshold, and the later of two computations cut at one place does not
replace the earlier.

What tells two computations apart is the places they are cut at, and not the data they are handed.
Two calls of one helper given two tables whose bounds are alike are one computation, as two calls of
a helper holding one guard are one line wherever the guard is cut at one place: a row through one
call is taken for a row through the other. That is the rule for every comparison a helper holds,
and it is not changed here.

The human report says the bound the table holds beside the place a reading is cut at.

Only a line on a value derived from several positions carries the bound. A reading draws other lines
as well — the filter an average is made of cuts one position at its own value — and the bound of the
table is no bound of those.

The document names the threshold under `threshold` in the obligation's id, so that two points of one
line that differ only in it are two entries.

## Consequences

The obligations a lookup owes grow with its thresholds and with its positions, and not with their
product.

Nothing composes a row for the weight of a position yet. The report says so under the finding: the
rows are the author's to write.

Whether rows that fix a weight can be written at all is not decided. A model whose declarations leave
no row independent of the others — three positions each between nought and one whose total is cut at
a value only reachable with two of them at one — owes weights that no row can discharge. Telling an
obligation nothing can discharge from one nothing has yet discharged takes a search over the
declarations' region, which is the generation's to make, and is left to it.

Two comparisons that happen to cut one direction are two computations and each keeps the classes of
its positions where it is cut at one place. An obligation nothing can discharge is reported as
unfixed like one nothing has yet discharged — two positions the declarations hold equal give rows in
one direction, and no row tells their weights apart.
