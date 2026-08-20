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

An outcome is a path to a value and not a branch of the syntax. An arm answering `unreachable`
answers nothing and aborts, so it is not a way the operand is settled: counted as one, a charge
whose other arm aborts varies two ways where it varies one, and the group it makes asks for a row at
a combination whose left half never reaches the operator. An operator that stops as soon as its
answer is settled does not consume both its sides either — `&&` leaves the right unevaluated
wherever the left settled it — so its two sides are not a meeting and the combinations of their
decisions are combinations no path takes. `NormalReturn` is the reading that already tells a body's
arms apart this way and is what answers it here — at the arms a value is enumerated over and at
every node the walk that finds the groups stands on, which are the two places a branch could be
taken for a path. A group found under an arm that aborts would be offered rows that settle nothing:
the decisions in there are made and thrown away with the run.

Which is a different question from what the pair space asks for, and the two answers do not have to
agree. A class the rules admit stays owed a row however the body describes it: a model's own claim
that a case cannot arise must not take away the row that would show the claim wrong. So the same
`unreachable` arm is not an outcome of the value and is still a class a row is offered at.

A group is a path to the meeting as much as it is the outcomes at it. An operator standing in an
arm is reached only by a row that takes that arm, and a row that varies the factors while going the
other way exercises the operator not at all — so what holds on the way to the meeting is carried
with it, and every one of its combinations is under that. Left out, a row offered for a combination
may never reach the operator it was composed for, and a row already written on the other side of the
fork reads as one that covers it.

A condition is a constraint and not a choice of class. `n > 10` leaves every class above the line,
and writing one of them down would answer for that condition alone and be wrong as soon as a second
one arrives — under `if n > 10 { if n > 0 { … } }` the way in is both, and a reading that assigned
would keep whichever it read last. So a cell carries which classes each position may hold, a
condition narrows it, and a position left nothing is a combination the body has no path to. What is
left over is room: a position a cell leaves several classes is chosen among them the same way a
position it says nothing about is chosen among all of them, which is by what the pairs still want.

Every condition a group is made of has to narrow something, or the group is not offered. A cell is a row that takes the path and settles each factor at the outcome the cell names,
and a condition with no class to put a row at leaves both open — the row may go the other way round
the fork above, or take another outcome of the factor. A factor whose outcomes place at the same
classes goes for the second half of the same reason: no row can be steered from one to the other, so
the cells over it are one row asked for several times. What is left in either case is the pair
space, which is where such a behavior already was.

What a part of a body is made of and what runs when it is evaluated are two questions, and the walk
asks the second. Evaluating a block makes a function; its body runs where something calls it, under
whatever it is called with, which is not a condition on this behavior's inputs. Which arm a
construction that decides one takes is whether the values made the thing, which no class of an input
names. Both are walked past rather than into, and the walk answers for every kind of node rather
than falling back on the ones every part of which is evaluated under the same conditions — that
fallback was the assumption, and it was wrong for those two.

A run of one operator is one meeting of all its values. `a + b + c` is written as one operator
applied twice and is three values making one number, and reading it as two meetings would ask for
the product of the first two against the third and then for the product of the first two again —
the second a projection of the first, wanting rows the first already wanted.

Which position a decision is about is not this reading's question. A name is not a position: a
helper spliced into a body binds the call's argument to the helper's own parameter and matches
that, so a reading that took the word would say about one parameter what is true of another. The
reading that owns the question answers it, and this carries two environments down for that reason —
one saying which position a name points at, one saying what the value at a name was settled by.

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

Two factors may read one position, and the choices that would put it at two classes are not
combinations. There is no path through the body that takes both, so there is nothing there to ask
for — which is the same rule as everywhere else here, and it is what a gate written on both sides of
an operator comes to: the choices inside the gate and the one outside it are cells, and the ones
that open the gate for one side and not the other are not.

The cells are held to the row budget the pairs are held to, and not to a second one. A group has as
many combinations as the product of its factors, which grows with the body rather than with the
number of inputs, so a run of five three-way decisions has two hundred and forty-three. They are
offered one from each group in turn, so a group met first cannot spend the whole budget and leave
the rest of them nothing, and a search that stopped says so in the words it already had. Nothing is
substituted: what a limit cuts off is the depth of the groups and never the strength a group is
offered at.

A value that can be settled more ways than the reading will tell apart is answered as settled one
way. The bound is on the product as it is taken, which is measurable before the work rather than
after it, and going over it asks for nothing rather than for a number of rows nobody would read.

Nothing prepares a group's combinations beforehand; they are read off it one at a time as the budget
is spent. A count decided in advance would have to guess how far the budget reaches, and it cannot:
a combination a row already sits in costs no row, so a list cut to the budget leaves the ones past
that point untried while the budget still holds. What a stopped search says is left is counted over
what the group has from where the search got to, which is exact and costs one pass over the choices;
it is said once, at the end, and about the cells and the pairs together, because one search stopped.

Two limits and they bound different things. One is the budget above, which says how many rows a
generation writes and is shared with the pairs. The other is on how wide a group may be to be
offered at all: a group is walked over past the combinations already answered and the ones nothing
could be built for, so one whose choices run to the billions would stand between the author and
every other group. That one is the group's own number, known before any of it is built, and a group
over it is not offered rather than offered in part.

Spec: `[#example-partition]`, `[#example-adequacy]`
