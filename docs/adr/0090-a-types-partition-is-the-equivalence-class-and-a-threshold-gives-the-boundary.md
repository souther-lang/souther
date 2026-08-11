# ADR-0090: A type's partition is the equivalence class, and a threshold gives the boundary

Status: Accepted. Fixes what the compiler may derive as an equivalence class, and what it may not.
Revised in place for #427: what a threshold is intersected with is what the *position* admits, which
is the field's type read under the rules of the record holding it. Revised again for #510: what a
line is drawn on is a numeric *term*, not a position — the content of a location, or a size taken of
one. Revised again for #622: which values a term's line can be drawn on is one table, and a rule
written over values it does not hold is reported as unread rather than dropped. Revised again for
#649: what decides whether a clause draws a line is which terms the clause reaches, not which
declaration it is written on.

## Context

Choosing test values is two steps that are usually done at once and badly: divide the input into
classes expected to behave the same, then pick a value from each and the values at the edges. Both
steps are judgement, and both are usually re-done from scratch by whoever writes the tests, which is
why coverage arguments end in opinion.

A model written in Souther has already done the first step. `data Kind = Domestic | Overseas` is a
partition of the trips into two classes, written by the author for reasons about the domain. So is a
`Bool`, so is an optional, so is a sum of five cases. `data Amount = Int invariant value >= 0` says
where the values stop. A `guard cost <= 100000` says the behavior treats the two sides differently,
which is exactly the claim a class is.

None of that is testing information that happens to be lying around. It is the same information,
written once, in the declarations. The question is which of it the compiler may read.

The pressure is to read more. An `Int` parameter obviously "should" be tried at zero, at one, at
something negative; a `String` at empty and at something long. Every coverage tool in the world does
this, and it is what an author expects to see.

## Decision

Only what the model states. A position the model draws no line through has **no classes**, and the
report names it as *not derivable* rather than dividing it.

A type states classes: `Bool` is two, an optional is two, a sum is its leaf cases. A record is not a
class — it is taken apart field by field, two levels deep. A threshold states where one class ends:
an invariant bounds what can exist, and a `guard`'s comparison against a constant divides what a row
can write. Thresholds at one position merge into one partition and are intersected with what the
position admits.

What a position admits is not what its type admits. A field's type says which values exist of that
type; the record holding it may relate that field to another, and the position admits that rule read
at this field — `startsAt < endsAt` over minutes of a day leaves `startsAt` stopping at 1439. Read off
the type alone the position offers 1440, which no row can be written at, and the report cannot tell
that gap from one worth closing.

Which terms a clause reaches decides what it may do, and the declaration it is written on does not. A
clause that bounds one term against a constant without relying on another term may place an edge
there: `value >= 1` on a newtype, `n >= 1` on the record holding `n`, `List.length(xs) >= 1` on the
record holding `xs`. A clause relating terms may take an existing edge in and may not place one:
`startsAt < endsAt` moves both ends of a day without dividing either position, and
`List.length(xs) >= minLines` is no different for counting something.

Placing an edge and taking one in are two answers, and the second is about an edge the first
produced. `data R = { a: Int, b: Int } invariant a < b invariant b <= 10` leaves `a` running to 9 and
draws no line through it: the 9 is there because `b` stops at 10, and a position whose only limit is
another position's is one the model draws no line through. `b` has a line at 10, which its own clause
placed. Reading the narrowed range as the edge is the mistake this separation exists to prevent, and
it is the same mistake the older wording prevented by naming the declaration instead.

The declaration stood in for the question and stood in for it wrongly in one direction. A record
stating a bound on one of its own fields states the rule a newtype over that field's type would
state, so reading the declaration made a rule measured or unmeasured according to whether the
aggregate holding it has a second field. An order with lines and a customer has to write the rule
about its own field, and that was the spelling that disappeared — the measure rewarded wrapping every
constrained field in a newtype of its own, which is a modelling choice and not a rule about the
domain.

A clause reaches a position from wherever it governs it: the newtype chain of the position's own
type, the record the position is a field of, the declarations under that record the position sits
inside, and the names wrapped round that record. The last of those is a place the same rule can be
written — `data NonEmptyBag = Bag invariant List.length(value.xs) >= 1` states what `Bag` could have
stated about its own field — and leaving it out puts this whole question back one level up. A
newtype's value is the same location as the newtype, so the clause names the `xs` a reader of a
`NonEmptyBag` sees rather than a position under a `value`. A line is named by the declaration the clause is written on. `data Inner = { n: Int }
invariant n >= 1` names `Inner` at every position an `Inner` is held in, and `data Outer = { inner:
Inner } invariant inner.n >= 5` names `Outer` where its clause is the tighter of the two. Where a
record's own clause is the tighter, the line is the record's: `data Moved = { n: Count } invariant
n.value >= 5` over a `Count` of at least 1 draws its line at 5 and names `Moved`, where before it
named `Count` narrowed within `Moved`. Where two clauses place an end at one value, both name it.
Only a clause relating terms is said beside a line rather than as one, since it moved an end another
clause placed.

What is read of any of these is an ordering of numbers and nothing else; a rule of another shape
leaves the position where its type left it, which is the safe direction — an edge too far out is a
row nobody can write, and an edge never moved is not one either.

An edge whose rules were not all read is not a gap. Both answers were wrong: counting it asks for a
row that may be impossible, and falling back to the type's own edge is no better, since the rule that
could not be read refuses that value as readily as the one beyond it. So it is reported, left out of
the denominator, and refuses no build — which is what ADR-0091 already does with a combination nothing
has settled, for the same reason. What settles it is a witness rather than an argument: a row at the
value went through the decoder, and from then on the edge is counted like any other.

Nor is an edge at a count, unless every count that measure could give is one some value has. What the
projection settles is which numbers the rules leave, and three is a number they leave whether or not
three of the thing exist: a `Set<Bool>` is capped at two by how many booleans there are, and a
`List<T>` of one needs a `T` that something inhabits. Whether such a value exists is a question about
what is counted and not about the count, and the domain has no term for it. So such an edge is
settled by a value — a row at it, or one this built — and not by an argument, which is the account an
edge nothing has settled already gets. The projection was never entitled to say it, and it went
unsaid only while a count could be bounded from the position's own type alone: given a second place
to write the rule, a floor no value reaches becomes a row an author is told to write.

A string's length is the one that stays proven. A string of any length is written by repeating a
character and a character is always to be had, so what the rules leave is what some value has. The
line has to be drawn there and not at distinctness, which is the other place it suggests itself:
"a list repeats an element" is an answer only once there is an element, and it is wrong about a list
of something nothing inhabits. Nor may it be drawn at every count — that takes away every
`String.length` edge in the corpus, twenty of them, over collections that have no values.

Whether the rules were all read is asked of the value and not of the position. A bound is about one
position; a row at its edge is a whole value with that edge in it, and a rule about any other position
can refuse to be part of one. A pattern on a label narrows no minute and still leaves every minute
beside it with edges nothing has shown reachable — the two labels a record cannot both carry are as
good a reason for that as a rule about the minutes themselves.

That question reaches as far as the construction it can refuse and no further. Down the fields a value
must have, at any depth, since a rule four records down refuses the outermost construction exactly as
one on the top does; and not into what a construction need not make, because a rule inside an optional
or a collection is a rule about a value that can be left out. The depth a report takes an input apart
to is a limit on what is worth measuring and cannot stand in for this.

A line is drawn on a number, and the number is not always what a position holds. The terms are the
ones the discharge procedure already names: the content of a location, and `List.length`,
`String.length`, `Set.size`, `Map.size` taken of one. Identifying the two was a defect and not a
restriction — a length bound is the commonest invariant in the specification's own examples, and
every position carrying one came back as a position the model draws no line through, which is a
false sentence rather than a narrow reading. It was said of a `guard` comparing a length too, in a
report of the very behavior that wrote the comparison.

So the term is what an axis, a cut, and a coverage question are all keyed on. `ValueOf` is one term
among them rather than the default beside a special case: keeping the plain path as the identity is
what let three separate readers each answer "is this observation a number" and each be right about
the positions it was written against.

A position has one term, and which one is settled by which of them the model wrote a rule about — a
`String` is the one value measured two ways, and a rule about its length is what makes the length the
term. The position's own type answers first and its answer stands. A rule reaching the position from
the value it sits in states an end on a term; it does not say which term the position is measured at,
and letting it say so takes an axis away — a `Name` bounded on its own order, held in a record that
bounds the length of it, would stop being measured on that order, and the line the author wrote would
go out with nothing saying it had.

Where the type chose nothing, one such rule may choose. Only one: where they arrive about both terms
there is nothing here to choose between them, and the position is left as one nothing divides rather
than given whichever was looked at first. That is the coarser of the two things that could be said
and the one that claims nothing; what would settle it is a position carrying both terms, which is not
here. What is spaced like an `Int`, what its own values are, and how
it is read off a row are three properties of the term — a size needs no boundary domain of its own,
and its non-negativity is its own rather than something a rule has to state.

A position no rule measures keeps its own name. A `String` nothing says anything about is not
derivable and is reported as the position, because naming its length there would put a term in the
report that nobody wrote.

One carrier says which values carry a line, and every reader asks it. A line is drawn on every
ordered value: an `Int`, a `Decimal`, a `Date`, a `DateTime`, a `String`, an enumeration, and a
single-value newtype over any of them. The carriers are
matched exhaustively wherever a count is read or written, so one added stops the build at every
place that would otherwise answer for it by omission, and the primitives are matched exhaustively
where a type is classified, so a primitive added stops it there. A newtype is reduced to its base
before either is asked.

A `String` is the one carrier with no count under it, and what that costs is the value beside a line
and nothing else. It was left out of the measure entirely instead, on the strength of the count: the
algebra held every ordered value as one number, and a string has none to embed into. But three of the
four things a measure produces need only the order — the line, the classes either side of it, and the
row at the line — and only the fourth, the row just below, needs a value the language does not name.
A carrier with no step already gets that answer; a `Decimal` and a `DateTime` have had it all along.
So the place a value sits on its carrier's order and the number it counts to are separate, and only
the second is a number.

A position that is one case of an enumeration, or a union of some of them, is not a carrier. It is
comparable on its sum's order — that is the wider question the type checker asks — and it ranges over
less than that order, so a line drawn from the sum's places would ask for a row at a value the
position cannot hold. Measuring such a position would need the carrier to hold the admitted values
beside the full order, and nothing needs that yet.

What an enumeration counts to is the place its case takes in the declaration, which is the order the
values have (spec §primitives). That count never leaves the carrier: an ordinal is a small integer,
which is the most plausible-looking wrong value any of the five has and the one a report is least
likely to give away, so the cases are what a row carries and what a line is named by.

The carrier is the enumeration itself, and not an order a value of it can be compared on. Which
order two operands are comparable by is the wider question the type checker asks, and it answers with
the sum for a case and for a union of cases as well — `Qualified < Won` compares on `Stage`. Which
counts a position ranges over is narrower: a position declared as one case holds one value, and a
union of cases holds some of them. Answered with the wider order, such a position took the whole
enumeration's counts, and the line drawn on it asked for a row at a value the position cannot hold.
So a position that is not the enumeration draws no line, and says so as a position whose comparison
went unread — which names the compiler rather than the model, and is the coarser of the two things
that could be said. Measuring a case or a sub-union would need the carrier to carry both the order
and the values that position admits, and neither this nor anything else needs that yet.

Which counts a carrier holds is the carrier's, and every producer of an end asks it. A strict
comparison over a carrier that steps is sharpened onto the count beside the one it names, and where
the carrier has none there, there is no end — read off the range of a `long` instead, `value > Won`
sharpened past the last case and reached the reader that writes an obligation as the value it stands
for. Holding a count is a question and not a correction: a date-time's counts sit on a grid at the
nanosecond and what writes one rounds onto it, so a carrier handed a count between two moments says
it holds none rather than naming the nearer one.

A threshold on an enumeration gives boundaries and no classes. Every other carrier divides a
position its type left whole, so the ranges a cut leaves are the classes; an enumeration already has
one class per case, and `s < Qualified` divides `{Prospecting, Qualified, Won}` into `{Prospecting}`
and `{Qualified, Won}`, which is coarser. The meet of the two partitions is the cases, so the classes
do not change and the rows the line owes are owed all the same. Rebuilding the classes from the
ranges would take away distinctions the model had already drawn.

Why a table rather than a predicate at each reader: there were three, and they disagreed. A `Date`
was a carrier to the reader that drew a `guard`'s line and not to the one that read an invariant's
bound, so the same rule about the same position answered differently depending on where it was
written — and the report said nothing about the difference, because the reader that dropped the
bound had nowhere to say so.

What a value carries and what lies beside it are separate. A carrier says whether a line can be
drawn; the type's own spacing says whether the value beside that line exists. A whole number and a
date have a neighbour; a `Decimal` and a `DateTime` do not, the second because which step a
date-time moves in is a decision this language has not taken. Deriving the second from the first is
what left a date-time unread entirely: an unsettled step is a reason to ask for no neighbour, not a
reason to draw no line.

A rule this could not read is named, whichever rule it was. A `guard`'s comparison already said so;
an invariant's bound did not, and a bound it dropped left the position looking like one no rule
bounds — which at a position whose only rule was that bound made the report state the opposite of
the declaration. The two producers now say it in the same words, because they answer the same
question: this position was written about and this could not draw the line.

An invariant's bound gives a boundary and not a partition: everything outside it is refused at
construction, so there is no class on the far side to cover. A `guard`'s line has values on both
sides, so it gives a partition *and* boundaries — the value, and its neighbour where the type has
one. That is a question about the rule and not about the term: a length bound is owed one row at its
edge, and a guard on a length is owed the value and its neighbour, for the same reasons a number is.

Only a comparison that is the whole of a `guard`'s condition is read. A condition built with `&&`,
`||` or `!` contributes no threshold.

A cut keeps every rule that drew it. One value can be an obligation several times over — but a rule
that took a line in is not a second line. A relational clause and the bound it narrowed settled one
edge together and are one obligation, named by both.

## Consequences

The report says "no finite equivalence class can be derived here" and stops. It does not say the
model is underspecified, and it must not: a `String` a behavior ignores entirely has one class, and
that is a perfectly good model. What the compiler can say is what it can derive, and the diagnostic
is named for that.

Reading the size terms turned 232 of those reported positions into measured ones across
`souther-examples`, and the boundaries owed went from 197 to 304. Two modules moved from
`undetermined` to `not satisfied`, which is the answer they should have had: the obligations were
always there and nothing was asking for them. No position gained a not-derivable line it did not
have, because a term is only taken of a position some rule measures.

Reading the clause wherever it is written moved four positions in `souther-examples` and the
boundaries owed went from 75 to 78. All four are one declaration — a CRM lead whose record states
`touches >= 1` beside a rule relating two of its dates — and the shape is the one the issue was found
on: an aggregate with a second field has to write the rule about its own field. The corpus is thin
evidence of how common that is rather than of whether it is right, since it has few record-stated
bounds on input types; what it does show is that no adequacy verdict moved and nothing that was
measured stopped being.

One position left the report for it. A behavior that gained an axis pushed another past the axis
limit, which is reported as omitted rather than dropped in silence. That is the limit doing what it
is for, and it is worth knowing that adding lines spends that budget.

Deriving the line and writing a value at it are separate abilities, and only the first is here.
Nothing composes a string of a given length (#528), so those edges are reported as unmet with the
reason saying that this compiler has no way to write one — not that the edge cannot be written at,
which is the sentence this ADR exists to keep out of the report.

Measured across the models in `souther-examples`, 398 positions came back not derivable when this
was first written. That is a lot of prose about nothing being wrong, which is why it is reported and
never warned about
(ADR-0089's grading, and the warning policy on top of it). Had the alternative been taken — divide an
`Int` at zero — those 398 would have become 398 rules nobody wrote, each with a coverage gap
attached, and an author working through them would be writing rows against a specification that does
not exist.

The restriction to a whole-condition comparison loses real thresholds. `kind == Domestic && cost <=
100000` has a threshold in it and this does not see it. The alternative is worse: the arm is reached
without `cost` having been compared, so reaching it is not evidence about `cost`, and treating it as
evidence would report a boundary as exercised that nothing ran against. Reading inside a compound
condition needs a probe on each comparison rather than on each arm, which is a different instrument.

Keeping a rule per cut means the same value can be owed three times. That is the point: an invariant
and two guards that name 100000 are three rules, and a row that meets one of them has met one.

Spec: `[#example-partition]`, `[#example-adequacy]`
