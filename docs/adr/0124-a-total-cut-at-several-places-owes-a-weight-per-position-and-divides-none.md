# ADR-0124: A total cut at several places owes a weight per position and divides none

Status: Accepted. Refines ADR-0090 for a total one comparison cuts at several places; a total cut at
one place divides its positions as before.

## Context

A rule that looks a total up in a table compares one computed value against every row's threshold.
In `hr`, `decideRegularly` averages the total remuneration of the payable months and looks the
average up in the standard grade table. The total is a sum of fields, each declared at nought or
above, and each field of each month was divided into classes at the table's lower bounds, together
with their multiples for an average over two or three months.

Those classes do not state an outcome. A value of one field that settles the comparison at one
threshold leaves the next threshold either way, so the grade is not the same through the class and a
row in it stands for nothing beyond itself. The borders of the total already carry the thresholds;
what the classes added was a count of rows owed that grew with the number of positions times the
number of thresholds.

What the classes did not ask for is what a test of a lookup needs besides the thresholds: that each
position is weighed into the total. A wrong constant is shown by a row at a border and a row beside
it (ADR-0090). A wrong coefficient, which includes a position left out, is not: the border can turn
about a point and still pass through it, and a row that writes the left-out position as nought
passes. A domain strategy places points on a border apart from each other for that reason (White and
Cohen, IEEE TSE SE-6(3), 1980).

## Decision

A total that one comparison cuts at more than one place is a family. The comparison is the author's
line and the total is the direction it runs in, so two comparisons that happen to cut the same
direction are two computations and two families, and one comparison read against every row of a
table is one.

The positions of such a total are not divided by its thresholds. The values of one position that
settle the comparison at one threshold are held as borders of the total and not as lines on the
position. A total cut at one place keeps its classes: the values that settle the one comparison are
the same outcome throughout.

In place of those classes each position owes one thing, once for the comparison however many
thresholds the table has and however many of its positions a window of the table reads: a row on a
border of the total with that position alone away from the least it holds, every other position of
the total at its least. Rows for different positions run along different axes, so the rows owed are
independent. A row on a border with several positions away from their least shows the sum of their
weights and no one of them, and counts for none. The least a position holds is what the declarations
leave it, and nought where they leave none. Where nothing was read against the comparison there is
no claim about the weights.

The obligation is keyed on the comparison and the position, never on a threshold: where a row stands
moves with every row written, and an obligation whose identity moved with them would be a new
obligation every run. It is a warning, E1940, and it appears in the document under `weights` beside
the borders of the total, each with the word `shown` or `not_shown`.

It sits beside the lines one step from a border (E1938), which hold a border against a fault of one
border in one weight, and replaces neither. Both are measures of what the rows show about the same
computation, and a row can answer both.

## Consequences

The obligations a lookup owes grow with its thresholds and with its positions, and not with their
product.

Nothing composes a row for the weight of a position yet. The report says so under the finding: the
rows are the author's to write, and the generation names the position and the total the row is for.

A family needs a comparison that is the author's. A total cut by two separate comparisons is two
families, each cut at one place, and keeps the classes of its positions. Where a table's rows are
read by a comparison inside a helper, the helper's comparison is the family.
