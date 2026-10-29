# ADR-0125: A fold owes a row whose step reads what an earlier step answered

Status: Accepted. Extends ADR-0121 with a third family of rewrites; the two it lists keep their
meaning.

## Context

A fold threads what its step answers into the step on the next element:

```souther
let total (xs) = List.fold((acc, x) -> acc + x, 0, xs)
```

Issue #2813 is what the replacement measure said of this body with the rows `([]) -> 0` and
`([1]) -> 1`, the two rows `--generate` had offered: every rewrite told apart, adequacy satisfied.
The same two rows pass a step of `(acc, x) -> x`, of `(acc, x) -> x - acc` and of
`(acc, x) -> acc * x + x`. A row of no element runs no step, and a row of one element runs the step
once, on the seed. The step never reads an accumulator it produced, only the seed `0`, and `0` is
what `+` leaves alone, so all four steps come out as `x`. The fault is run and changes nothing.

Test design has asked for the missing row for a long time. Beizer's loop testing asks a simple loop
for zero, one and two passes, because what one pass leaves for the next is read only on the second
(Software Testing Techniques, 2nd ed., 1990). In data-flow terms, the step defining the accumulator
and the step on the next element using it are a def-use pair (Rapps and Weyuker, IEEE TSE SE-11(4),
1985), and only an input of two or more elements covers it.

Neither rewrite of ADR-0121 reaches it. A fold is the language's one loop, an ordinary recursive
helper (ADR-0051), and the backend emits a fold walked from the head of its list as the loop it is:
the step's body is the loop body, and no fork of the helper is left in the code a run goes through.
The body above owes no arm, so it is asked about the values its rows came to, and two values are
told apart by two rows.

## Decision

The walks a body runs are rewritten two ways, and each is a third family beside the two of
ADR-0121. A walk stopping after its first step answers what that step answered: the fold over the
first element alone, as `List.fold(step, seed, List.take(1, xs))` would. A walk handing every step
the seed in the place of what the step before it answered answers the step on the seed and the last
element. Both are edits of the source an author could make, both leave a row of fewer than two
elements as it was, and each tells a different fault: a step that never reads its accumulator,
`(acc, x) -> x`, is the walk under another spelling once it is handed the seed, and only stopping
after one step tells it from a fold keeping the first element.

A walk is a fold walked from the head of its list, or the build a fold that only grows a collection
became, and the tree that runs carries it as a loop where its step runs where it stands. Every walk
the source wrote is a loop of its own there. Two builds the emitter joins into one loop, a `map` over
a `filter`, are not one walk: the joined loop goes over the list the inner one goes over and runs the
outer step where the inner one adds, so stopping it after a step is the inner walk stopping and
resetting it is the inner walk reset, and says nothing of the outer one, whose steps are the elements
the inner one kept. The join changes when each step runs and no answer, so it is the emitter's, made
in the classes that record nothing, and the classes that record a run keep each walk the loop it is.
A walk is written by the source that wrote the fold, in the copy of whatever wrote it, so a fold inside
`List.map` is the language's fold, and a rewrite of it is one for every call that reaches it, as an
arm of a library helper is (ADR-0121). It is shown at the fold where this compilation holds the
source it is written in, and at the behavior otherwise, by the definition that wrote it.

Three walks are not rewritten. A walk that reads nothing a run is handed — no parameter, no name bound
to anything that reads one, no behavior called — answers one value on every run, and either rewrite
of it answers one value too: changing it is changing a constant, which ADR-0121 does not ask about.
So is every walk in a value, which is handed nothing. And a walk over what listing a set or a map
answers (`Set.toList`, `Map.toList`, `Map.keys`, `Map.values`) goes in an order the language leaves
unspecified, as the library says of `Set.fold`, so its first element and the step before another are
no element and no step the model names, and a row telling either rewrite apart would turn on that
order. The order is a property of the list, not of the call that made it: a list made of one that has
none has none, however it was bound or worked on (`List.reverse`, `List.map`, `List.take`, a helper
that returns it), and only `List.sort` gives it one again. A list-typed node has the order of the
lists it is made of, and a node of another type, a function handed to `List.map` among them, is none
of its order.

A walk the language owes a row of is owed whether or not this compiler can run it rewritten. A step
that is not written where the fold hands it over, as in `let step = if flag then add else sub`, is
handed to the library's one method as a value, and a switch in a method every fold of the program
runs would rewrite them all. Such a walk is kept all the same, a run records that it reached the
call once the call's arguments are worked out, and both rewrites are left undecided because the step
is not expanded (`step_not_expanded`): the adequacy is undetermined, never satisfied by rows that
were never put to the fold and never not satisfied by a rewrite nothing could run. The reason is a
limit of this compiler, so no run and no row changes it. It is not a figure and is not
`too_large`, which a wider run or a smaller method answers. A walk one of whose places cannot be
run rewritten is left open at all of them, since a rewrite of it is an edit of one source. The
proofs that need no run still hold, a list written with one element or none among them, and the one
proof read off a run does not: a run through such a walk records no second element, so that its
absence shows nothing. Expanding the loop around a step handed as a value would remove the limit,
and is a change to how folds are emitted that belongs to its own issue.

A run records entering a walk at a place of its own, a third family of the one numbering beside arms
and conditions. Nothing is owed for entering one, and no branch measure counts it. What it is for is
the question of which rows a rewrite of the walk is put to: a row that never entered the walk comes
out the same under any rewrite of it, and a walk no row stating its answer enters is the arm it
stands in going unreached, which is owed there. A run also records taking a second element of a
walk, once per entering. The walks are numbered after every other place, so an arm's number does
not move with which loops a body holds.

The rewrites ride in the classes the arms' siblings ride in, behind a switch at the walk asking the
per-thread selector how to walk. The seed a walk is handed again is the value it started from,
worked out once; a builder is made again, since the steps write into it. A method that cannot hold
the switch is written again without it, and the rewrites of that walk are left undecided as a
sibling left out is.

What is proven the same is narrow, as ADR-0121's proof is. A list written with one element or none is
walked no further than its first, by either rewrite. A step whose body never reads the accumulator it
is handed is the walk under another spelling when handed the seed. And a list that reads nothing a
run is handed is one list on every run, so a run that answered and was seen walking it no further
than its first element shows every run does: that is the one proof read off a run, and it rests on
the list being the same value wherever it is worked out. It also rests on the run having answered,
since only a run that came back went through every walk it entered to the end; the evidence is made
from runs that answered and from no others, by the one constructor that says so. Everything else is
asked, and a rewrite no search finds an input for is undecided, never concluded the same.

The search for an input starts from the rows that entered the walk, the ones holding the most
elements first and a candidate of each in turn. A list one of them holds is grown by one element and
then by two, each with the new element put first as well as last, since a walk stopping after one
step parts from the walk only where what the later elements do differs from what the first does.
That is how a list grows wherever it stands, in a field of a record as much as the value itself. The
candidates come in the order a list of two is reached in: a list holding something grown, a list
holding nothing grown and then the list it made, and only then what no list of two was reached by,
which is not left out. The order is the kind of list each growth is of, so the first candidate is
the first one made, and nothing is made and set aside to find it. The elements are taken from what
the rows of the module ran with, which counts every value a row holds at the position it stands at,
an element of a list, a field of a record, the case of a sum, what an optional or a map holds. Beside those, a list of the same length with one
element changed for another the rows hold, and a string the body parts with a piece more at a
separator the body parts strings at, a walk over the pieces of a string being handed more elements
only through the string. Each of these is made as the search asks for it, one candidate at a time,
so what a long list or many values cost follows the runs the search is given. Then a row in each
class of each position, and last a row with one position
moved. The row `--generate` offers is chosen among the rows meeting its requirement for the rewrites
it tells apart (ADR-0123), and the walks a row entered are among what it is asked; which walks a row
entered and how far it took them is no part of the way a row went, so a row of two elements is
compared with a row of one.

The finding is E1939, as for the other two families, and schema 27 names the two rewrites
`fold_after_one_step` and `fold_from_the_seed` in a rewrite's id, with the fold's coordinates.

## Alternatives

Partitioning a list by its length was refused. The rules draw no line there, and the obligation
belongs to the step, not to the input: a list of two elements is what telling the rewrites apart
takes, and it falls out of the search rather than being asked of every list a model takes.

Handing the step the seed alone was the issue's proposal and was not enough. It leaves a step that
never reads its accumulator with nothing owed, which is right of that rewrite, and the rows `[]` and
`[1]` still cannot tell a fold keeping the last element from one keeping the first.

Rewriting the arms of the recursive helper was refused. The arms exist only in the helper's method,
which a fold walked from the head of its list never calls, so which rewrites a body was asked would
turn on how its folds happened to be emitted. Rewriting `foldFrom`'s step argument at the call, in
the tree an analysis reads, was refused for the reason ADR-0121 refused a class per rewrite: the
classes run are the ones measured, and one set of them carries every rewrite.

Recognising any recursive helper that threads a value into its own call as a walk was left for
later. A parameter a self-call hands a value computed from it is a walk's accumulator only where it
decides no fork of the helper; resetting the index a walk counts with would loop for ever. The one
loop the language has is the library's, read off its body (`TheWalk`), and a helper an author
writes to recurse is asked about its arms as before.

## Consequences

A body walking a list over rows of fewer than two elements is refused under `--strict` where it was
satisfied, and `--generate` offers a row of two elements for it. That holds of a fold the model
writes and of one inside an operation of the language, `List.map`, `List.filter`, `List.all` and
the rest, since each is a fold over the list the body hands it.

Each row entering a walk is run once more for each rewrite of it, and a rewrite the rows leave open
is searched for, at the level that asks for every measure.

Rows offered at a point of a line over a total now share the total between elements where one element
carrying it would leave the sum's fold untold, since the row chosen at the point is the one telling
the most rewrites apart (ADR-0123).

A walk the lowering does not carry as a loop, one handed its step as a value, is not rewritten. The
recursion in a helper an author writes is not a walk. A walk over a list of records the rows hold none
of, each field of which the rules divide no way, is often left undecided: the type offers one value
to grow the list by, and two elements alike tell neither rewrite apart. A fold over `List.take(1, xs)` is the walk the
model states, and stopping it after one step changes nothing: what tells the model from one meant to
sum the whole list is the intent, which no rewrite of the source written recovers.
