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
expression is what is written at a call. A computation is therefore the comparison as one call of it
reads it (`DerivedValue`: the author's line and the copy of it a call made). One comparison inside a
helper, read at two calls with two values — `gradeOf(a + b)` and `gradeOf(a + 3 * b)` — is two
computations, each of which can weigh its positions wrongly on its own. Read at one call over the
different windows of a table's input, it is one computation however many weighings of the positions
those windows make. The comparison alone merges what is written at two calls; the weighing alone
splits what one call writes.

A derived value is a form over at least two positions: a total, a difference, any weighing of them.

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
fixed where the rows on the borders determine them. A row on a border satisfies the sum of the
model's weights of the positions, each by the value the position holds, equal to the threshold the
model wrote. A computation that weighs a position by more or less agrees with such a row only where
the weighted difference sums to nought, so the weights are fixed where the vectors of weighted values
the rows give span the space of the positions, and the weight of one position is fixed where its own
axis is in the span. The span is worked out in exact arithmetic.

This is a property of what the rows determine, not of how a row is shaped. A row that moves one
position alone is one way to fix a weight and not the only one: three rows that each move two of three
positions fix all three, and a position weighed by minus one has no row that moves it alone and can
still be fixed. An earlier form of this measure asked for a row with one position alone away from its
least; it could never be met where the declarations leave no such row, and it said nothing of
positions that weigh against the others.

Where nothing was read against the computation, or the exact arithmetic gave out on a row, no claim is
made about its weights and the document says `undecided`. It is not a finding.

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
its positions where it is cut at one place. A comparison inside a helper called with the same value
at two places is two computations, each owed its weights, and a row on a border of both fixes both.
