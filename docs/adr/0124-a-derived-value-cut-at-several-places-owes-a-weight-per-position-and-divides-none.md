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
thresholds the table has and however many positions a window of the table reads. The weights are
fixed where the rows beside the borders determine them. A row at the value nearest a border
satisfies the sum of the model's weights of the positions, each by the value the position holds,
equal to a number the threshold fixes. A computation that weighs a position by more or less moves such
a row by the weighted difference, so the weights are fixed where the vectors of weighted values the
rows give span the space of the positions, and the weight of one position is fixed where its own axis
is in the span. The span is worked out in exact arithmetic.

The two sides of a border are spanned apart. A position weighed more than the model weighs it moves a
row across the border one way and one weighed less moves it the other, so a row where the rule holds
catches the one and a row where it does not catches the other, and neither says anything of the one it
does not catch. Which value is where the rule holds is the comparison's: a strict comparison holds one
value further up than a non-strict one, so a rule that took the threshold itself for the evidence would
fix weights that a computation weighing a position by less still agrees with. A weight is fixed where
its axis is in both spans, and a side the border has no value on, because the type ends there, is not
asked.

Only the readings of a row that stand at a border's point are evidence of it. A row inside a
container has a reading for each element, and one of them standing at the point is no reason to take
the numbers of another: whether a reading stands and what it reads as are asked of one walk, so that
the reading that was found to stand is the reading whose numbers are taken. A row whose answer is
not the model's is evidence of nothing, and a point that could not be worked out may have rows nobody
can name, so a weight is not said to be unfixed past it.

This is a property of what the rows determine, not of how a row is shaped. A row that moves one
position alone is one way to fix a weight and not the only one: three rows that each move two of three
positions fix all three, and a position weighed by minus one has no row that moves it alone and can
still be fixed.

Where nothing was read against the computation, where a border of it was not read and the rest leave
a weight unfixed, or where the exact arithmetic gave out on a row, no claim is made about the weight
and the document says `undecided`. It is not a finding. A row the arithmetic gave out on is left out
alone: what the other rows fix stays fixed.

The obligation is keyed on the computation and the position, never on a threshold: where a row stands
moves with every row written, and an obligation whose identity moved with them would be a new
obligation every run. It is a warning, E1940, and it appears in the document under `partition.weights`
beside the borders, each entry with the word `shown`, `not_shown` or `undecided`.

It sits beside the lines one step from a border (E1938), which hold a border against a fault of one
border in one weight, and replaces neither. Both are measures of what the rows show about the same
computation, and a row can answer both.

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
