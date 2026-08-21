# ADR-0109: An outcome is a path to a value and carries what the value is

Status: Accepted. Replaces one clause of ADR-0108, which is named below.

## Context

ADR-0108 says which combinations a generated row is composed for, and it defines an outcome as a
path to a value rather than a branch of the syntax. What it did not say is that a path arrives
somewhere, and the reading built from it holds only the conditions along a path and never what is
at the end of one.

That is enough for every operator that consumes its operands whichever way they come out. It is not
enough for one that stops as soon as its answer is settled, because which of the left's paths go on
to the right is which value each of them comes to. Under `A && B && C` the reading answered three
ways at once and all of them said nothing: the operator's value was read as settled one way, the
walk went into the right only where the left was a single comparison, and the arm of a fork on it
was named by the arm rather than by the comparisons. Three decisions that between them settle one
value were read as no group at all, and what was left was the pair space.

ADR-0108 states the first of those as a consequence of the operator not being a meeting. Not a
meeting and has no outcomes worth reading are two claims, and the second does not follow from the
first.

## Decision

An outcome carries what the value at the end of it is, where the reading can say.

Carried by the reading's own answer and not by what the generator is handed. What a group is
composed against is the conditions along a path, which is what an outcome was and stays; the truth
beside it is how the reading works out which paths there are, and no reader downstream has a use
for it. Put where a reader could take it, it would be a second thing to keep true of a group.

A path to a value and what the value is are two questions, and the second is about the reading
rather than about the body. So a third answer to it is needed and it is not a third truth: a path
whose value is unread arrives at a value just as much as one whose value is read, and what is
missing is this reading's answer for which of the two it arrived at. Read as an absence of a value
it would take away the path, which is the reading saying the body has not got something it has.

The paths of an operator that stops early are the left's settling ones as they stand, and the
left's going-through ones each extended by every path of the right. Not a product: `&&` comes to
false wherever the left does and never looks at the right. A left path whose value is unread stops
where a settling one stops, because whether the right ran at all is what the left's value would
have said. So `A && B && C` has four paths where the product would have eight, and every one of
them is one a row can be steered down.

Composed one operator at a time and the answer does not turn on how the run is written down. Read
from either end `a && (b && c)` and `(a && b) && c` have the same four paths, which they have to:
an answer about the bracketing would be an answer about the writing.

The ways a value is settled to one truth are all of them or none of them. A list with paths missing
from it reads as a whole one — whatever takes it steers no row down the paths it does not hold and
offers no group under them — so one path whose truth is unread makes the whole enumeration
unavailable rather than quietly dropping itself out of it. Under `x > 10 && f(y)` the way to false
through `x <= 10` is known and the other ways are not, and answering with the one would say the
condition holds nowhere else. An enumeration holding nothing is a different answer again and is one
this reading gives: it says the value is never settled that way, which is how an arm no row reaches
is told from an arm nothing can be said about.

That enumeration is what names a way in, and it is one rule read by three: the outcomes of a fork's
value, the walk into a fork's arm, and the walk into the right of an operator that stops early. A
way in this reading carries is a conjunction, so an arm reached several ways is walked once with
those ways carried together, and a group found inside it is offered once per way. Two paths and not one alternative — under `A && B`
a row that made the first comparison fail never evaluated the second — and a group naming both
would name a combination no row sits in.

A comparison is a value this reading knows the truth of where it can name both of its ways, and
neither where it cannot name one. With one of them the other's absence reads as a truth the value
never comes to, and a fork on it would be told one of its arms is never reached. Naming a way
takes the comparison having a place a run is recorded at, which is what a decision is half made
of — so what this reaches is what the plan draws a line on, and a comparison written outside the
condition of a fork is not one of those. The rule is read where it is written inline and not where
it is given a name first. That is a limit of the numbering and not of this reading, and it is
recorded in a test so that it is something said rather than a silence.

A second limit, and it is in front of all of this rather than beside it. Whether an expression can
answer a value at all is read before any of these paths are, and that reading takes an operator
which stops early to be strict in both its sides. So `a > 1 && abort` is answered as reaching no
value, when a run with a small `a` reaches one — and everything under the fork on it, both arms
included, goes unwalked. Which paths a short circuit has is exactly the question this decides, and
the reading that decides it here cannot be the one asked there: it is built on the numbering, and
the numbering is built on that answer. What is owed is a reading of what an expression can come to
that needs no numbering, told apart from what it knows — a comparison this cannot evaluate is not
the same as one that comes out both ways, and `1 > 2 || abort` answers no value while `a > 2 ||
abort` may. Under-reading is where it is left until then, which is the direction everything else
here takes.

Two ways in that settle one decision opposite ways describe no run, so the walk does not go that
way rather than going and leaving what it finds to be thrown out later. Which decision it is is not
which place a run is recorded at: `if a then (if a then …)` is two places and one decision, no row
takes one fork without the other, and reading the second naming as a contradiction would take away
the only path there is.

How many ways in one position is read under is bounded, and by its own bound. The bound on outcomes
is on a product taken at one node; this is on a product taken along the way down, and a condition
that fails four ways standing inside another one is a meeting read sixteen times. The two multiply
with the nesting of the body, so one holding does not hold the other. What is counted is the ways
that survive being held to what already held, because a way nothing could take would otherwise
spend a share of the bound and push out one something could take — which would move where the bound
falls with how the body is written rather than with how much there is to read.

Counted and not estimated, which decides how the walk carries a way in. How many contexts survive
at a position is a fact about the position and about all the ways down to it at once, and a walk
arriving one way at a time cannot know what the ways beside it came to — so it would have to
multiply what it does know, and that product is not the number. Where the arms are uneven it is
larger: a condition asking again about something a condition above it already decided leaves half
the contexts unable to reach the arm at all, and the half that can are then given up on as though
the bound had been passed. Given up on means the arm names itself, which places at no class, so
every group under it goes — a position under the bound losing everything because of how the ways
above it were spread. The walk carries the contexts of a position together for that reason, and the
bound is checked once, where they are all in hand.

Over the bound the fork that would go over is read the one way a fork whose condition cannot be
valued is read, which is by naming its arm. That is where every fork was before the ways in were
told apart, so going over asks for no more than was asked for then. The bound holds by induction
rather than by anything counted along the way: a position is read under at most the bound, and what
an arm below it is read under is either those contexts held to the ways the condition comes out —
checked there — or one per context, which is what there already were. The right of an operator that
stops early has no arm to fall back on, so over the bound it is not walked at all.

A value this reading finds no path to is answered as one it has nothing to say about. Two parts of
a value whose every settling contradicts the other's leave nothing — under
`(if a then x else abort) + (if a then abort else x)` each part answers on its own and no run has
both answering — and whether that is the body having no path or this reading not following one is a
question about how the decisions on either side correlate, which nothing here asks. So it is not
published: handed on it would reach the enumeration above, where an empty answer says the value
never comes to that truth, and said of both truths at once it takes both arms of a fork away. The
reading would be making a claim about the body off the back of its own silence. Normalised at the
one place a reading is answered rather than at each shape that can produce it, because it is one
invariant and the shapes that can break it are however many there are.

None of this makes the operator a meeting. ADR-0108's reading of that stands: the two sides are not
consumed into one value, and the combinations of their decisions are combinations no path takes.
What is replaced is the clause that went on from there to "so the answer is that the operator is
settled one way, which asks for nothing".

## Consequences

Rows are added and none are taken away, which is ADR-0108's shape and holds for the same reason.
A fork on a chain of comparisons varies as many ways as the chain has of settling rather than two,
so a value made out of it is a factor of that many; the arms of such a fork and the operands after
the first are walked into, so the groups standing in them are offered where they were not offered
at all.

The measures do not move. The pairs are still counted and reported the way ADR-0091 and ADR-0089
say, and this is read for the generator and nothing else.

A group offered once per way into an arm costs a row per way. They are held to the row budget the
pairs are held to and to the bound above, and neither is a second budget: what the bound cuts off is
how many ways in a position is read under and never the strength a group is offered at.

The groups come out by the meeting first and by the way in second. A meeting reached several ways is
one place in the body and as many groups, and they are written down together because that is when
the walk is there. A generation whose budget runs out reaches a different set of them than it would
have under the other order, and this is the order to have: which groups a stopped search got to is
then said by where the meetings are written, and not by which way round a fork above them a row
goes.

Spec: `[#example-partition]`, `[#example-adequacy]`
