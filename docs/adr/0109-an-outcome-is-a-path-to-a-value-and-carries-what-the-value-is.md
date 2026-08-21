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

Whether an expression arrives at a value at all is read before any of these paths are, and that
reading was taking an operator which stops early to be strict in both its sides. So `a > 1 && abort`
was answered as reaching no value, when a run with a small `a` reaches one — and everything under the
fork on it, both arms included, went unwalked. It was written down here as a limit of this reading
and it was not one: which paths a short circuit has is exactly the question decided above, and the
reason it could not be asked there was that this reading is built on the numbering while the reading
that answers what arrives is what the numbering is built on.

That is now the same reading asked without a numbering, and what made it one reading is that three
facts were being carried as two. Whether a run arrives at a value, what a boolean value comes to, and
whether a way to it can be written down in the numbering's words are three, and the third had been
folded into the second: a comparison the plan could not place was answered as a comparison with no
value, so a fork on it lost its arms and an operator over it lost its paths. Held apart, the reading
of what arrives is the reading of the paths with the naming taken away, and there is no second
account of the body to keep in step with the first.

Four things hold of it, and they are what the separation is.

A naming decides what a way is called and never whether there is one, and it is a structure and not a
rule to keep. What the body does is read with no naming at all, and the naming reaches only the list
of ways: a condition it has no words for leaves a way written in part, a pair of conditions it sees
settle one decision opposite ways leaves a way out, and more ways than it will hold apart leave the
list saying nothing. None of those can move what arrives or what a value comes to, because that half
was never computed with a naming in it. Said as a rule instead, two of the three went on moving it —
a naming that could see two arms of one decision contradict answered that no value arrives where the
reading without one answered that a value does.

Not knowing is never both. A value this reading has worked out no truth for settles nothing: it does
not send an operator into its right and it does not stop one there, and no path is offered on the
strength of it. A way to a value that arrives is offered where the way is worked out or where what
follows it arrives anyway. Which is a different question from whether an arm of a fork stands, and it
is asked differently: an arm stands unless the reading worked out that the condition never comes out
its way, so a value with no truth worked out leaves both arms standing. Two questions and two names
for them, because one name for both is how not-knowing gets widened into both.

A value is answered as known only where a value of what it is over stands behind it. Not a rule about
the shape of the node, in either direction: `a == a` is a comparison and comes out one way, `1 > 2` is
a comparison and comes out one way, and a position of the input holding a truth is no comparison at
all and comes out both ways. A reading answering "a comparison comes out both ways" would offer the
first two a path no run takes; one asking the question only of comparisons would answer that
`flag && abort` arrives nowhere, when every run with a false `flag` arrives. So each way is asked
about on its own, against the range of what is compared — which for a whole number is read off the
ends, so a number at the end of the range closes the way past it. A way nothing stands behind is not
offered, and where nothing stands behind either the value is answered as one this reading has nothing
to say about. Under-read, and the direction everything here takes.

A way found twice is one way. The reading answers a set for that reason: what is counted anywhere
downstream is what the body does and not how many times the reading got there.

What is still not read is what correlates two paths. Under
`(if a > 0 then true else abort) && (if a <= 0 then true else abort)` no run arrives, and each side is
read on its own and arrives — so the operator is answered as arriving. The same holds of the model's
own rules: a behavior requiring `a > 1` has no run with a small `a`, and `a > 1 && abort` is answered
as arriving all the same. Both are the liberty this reading has always taken with arms of a fork,
which are counted without anything having asked whether the condition can come out that way, and
neither is decided here.

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

Rows are added, and one kind is taken away. A fork on an operator that stops early is where they are
added: both of its arms were going unwalked, and every meeting standing in either of them is now
offered under the way in that reaches it. What is taken away is an arm the condition never comes out
the way of — `if true then … else …` has one arm a run enters and a comparison against the largest
whole number has the other, and numbering the one nothing enters is a row owed for a combination the
body has no run at. Read from the same place everything else about arms is read from, so the
numbering and the walk into an arm cannot come to differ about which arms there are.
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
