# ADR-0108: What has to be varied together is read off the body, and how far is not

Status: Accepted. Fixes where the combinations a generated row is composed for come from.

## Context

ADR-0091 fixes how a combination is counted and ADR-0089 fixes how the count is reported. Neither
says which combinations there are. What has stood in for an answer is the product of the classes of
every two input positions: every position taken to be able to interact with every other.

That assumption is why black-box combinatorial testing enumerates t-way combinations at all. With
the code out of view, which parameters interact cannot be known, so all subsets are covered. The
body is here, and the assumption is wrong in both directions at once.

A charge that is the sum of two decisions — a base charge settled three ways and an express charge
settled two — is offered four rows for the pairs of its three inputs. Answered, they reach
`pairs 12/12` and `branch 6/6`. None of them makes both charges non-zero, so the only answer both
decisions take part in is never produced, and an implementation taking the larger of the two instead
of their sum holds against every one of them. In the other direction the same product asks for a row
at Premium and a total under the free-shipping line, which the body cannot read: the premium arm
never looks at the total.

## Decision

The topology is read and the strength is not.

Which decisions settle one value together is a fact about the rules, and reading it is what a tool
with the body in front of it can do. A group forms where two values each settled by a decision are
consumed into one — an operand of an operator, an argument of a call that answers one value. A node
with several children is not a meeting: two decisions writing two fields of one record arrive at a
constructor and interact in nothing, because no observation is a function of both.

How many factors of a group have to be varied together to catch an implementation fault is not read.
Nothing in a model implies it — it is a claim about how implementations fail, and empirically most
faults are triggered by 2-way to 6-way interactions. Keeping the two apart is what stops "the model
knows what interacts" from becoming "the model requires exhaustive path coverage", which is a
different claim and a false one.

A combination the body has no path to is not built rather than built and then excluded. Nested
decisions inside one operand are one factor of as many outcomes as the operand has paths to a value,
so Premium against a total under the line is not an infeasible cell; it is not a cell. That is what
tells this apart from a constraint written by hand to remove a combination a generator would
otherwise offer.

This is read for the generator and nothing else. No measure changes: the pairs are still counted and
still reported the way ADR-0091 says, the two axes are allowed to disagree, and a behavior with no
body still has the pairs and now has nothing else. What the reading changes is which rows
`--generate` composes, and a row deleted comes back the next time it is run.

Under-reading is the safe direction and is where a group nothing formed leaves things — an
obligation nobody is asked for, which is where the product over the positions already was. A group
formed too eagerly asks for rows that establish nothing.

There is no way to write a group down. A declaration would fix a syntax to a reading whose failure
modes are not yet known, and the reading is the part that can be wrong. One is owed when a group the
rules state is observed to go unread and stays unread after the reading has been given the rule it
was missing.

## Consequences

Rows are added and none are taken away. A cell fixes however many positions its decisions read and
leaves the rest free, and the free positions are what the greedy pass spends on the pairs nothing
covers — so the premium arm, which reads no total, still fills a class of the total rather than
costing a row of its own. The row the product asked for and could establish nothing with is paid for
by a row that establishes something.

A cell is named for the classes it fixes, which is what it was composed for. What the row settles
beside that is the generation's to change and is not in the name.

A group whose product is beyond what will be offered is offered fewer rows. That costs nothing that
has to be said, because generation makes no claim: a measure cut short would have to say so rather
than report a lower strength in place of a higher one, and there is no measure here to cut short.

A decision the reading cannot name an input position for is still two outcomes and steers nothing.
The cells are still two and the rows filling them are chosen as any other row is. That is the
reading being honest about the half it has rather than dropping the group.

Spec: `[#example-partition]`, `[#example-adequacy]`
