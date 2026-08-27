# ADR-0090: A type's partition is the equivalence class, and a threshold gives the boundary

Status: Accepted. Fixes what the compiler may derive as an equivalence class, and what it may not.
Revised in place for #427: what a threshold is intersected with is what the *position* admits, which
is the field's type read under the rules of the record holding it. Revised again for #510: what a
line is drawn on is a numeric *term*, not a position — the content of a location, or a size taken of
one. Revised again for #622: which values a term's line can be drawn on is one table, and a rule
written over values it does not hold is reported as unread rather than dropped. Revised again for
#649: what decides whether a clause draws a line is which terms the clause reaches, not which
declaration it is written on. Revised again for #868: a rule left unread is a rule about where the
values stop, and is answered per rule rather than per position. Revised again for #870: a border is
what owes the four coverage items of domain testing, and a point it owes none of says which of three
things settled that. Revised again for #907: whether a range is the whole of what the rules leave a
position is settled by a certificate, and having none of them is not the range being wider. Revised
again for #1029: whether a comparison divides one position, relates several, or says nothing is read
from one canonical comparison, and the operands as written do not establish its subject on their
own.

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
class — it is taken apart field by field, down every path that opens no declaration twice. A
threshold states where one class ends:
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

A clause reaches a position from wherever it governs it: the position's own type and the names
wrapped round it, the record the position is a field of, the declarations under that record, and the
names wrapped round any of them. A name worn is a place the same rule can be written — `data
NonEmptyBag = Bag invariant List.length(value.xs) >= 1` states what `Bag` could have stated about its
own field — and leaving it out puts this whole question back one level up.

Which is a fact about how a position is named rather than a list of places to look. A name wrapped
round a value is not a step of the path: the atom of `w.value.n` *is* the atom of `w.n`, which is
what the discharge check has always read by, so a reading that counted `value` as a step filed every
position under a wrapper where nothing asks for it — and stopped at the wrapper rather than going
through it. Counting it as no step reaches a wrapper at a parameter, a wrapper on a field, and a
stack of them, because none of those is a separate case once the naming agrees.

So a wrapper is read like any other governing declaration, and does all three things one does: it
places ends, it projects ranges onto the positions under it, and it can hold a clause this could not
read. `data Wrapped = Base invariant value.a < value.b` places no edge and still leaves `a` stopping
one below where `b` stops. Lifted as ends alone, a wrapper's relation narrowed nothing and a guard
beyond the narrowed range drew a line at a value no `Wrapped` holds; and an edge under a wrapper
clause nothing could read came back certain. A line is named by the declaration the clause is written on. `data Inner = { n: Int }
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

Whether the rules were all read is one of three things an edge stands on, and it had been standing
in for all three. A rule that never reached the reading is one of them; whether an end could be
written down as a number is another; and the third is whether the range the reading did produce is
the whole of what the rules leave that position. The third is the one this got wrong. It was decided
by asking, of each rule, whether the range alone entailed it — which establishes it soundly, since
ranges entailing every rule are the feasible set, and is not what being the whole of it means. A
range can be exactly what the rules leave a position while stating no rule that relates it to
another.

So it is a certificate: something established it, and what did the establishing is carried. Having
none is that nothing established it, which is the only thing a reader may act on. An edge nothing
licenses is an edge nothing licenses, and it is never a claim that the range is wider than the model
— the same distinction ADR-0091 draws about a combination nothing has settled, and the same reason.

The certificate this compiler constructs is the ranges together with the relations its closure holds
between them. Which is what the inference already used and did not say: a difference of two positions
is held exactly by the closed relations, so `a - b <= 2` beside two positions running 0 to 7 comes
back proven while the two ranges by themselves hold `a` at 7 beside `b` at 0. Naming it is what makes
its hypotheses askable. Two of them are: every position the rules relate to each other has its values
spaced the same way, since the step from a system to one of its ranges is a theorem about a system of
one kind of value; and the box no relation can still narrow, which is a property of every closed
state and is asserted where one is made rather than asked here. Positions no rule mentions together
are two systems written down beside each other and are not held to the first — which a record with a
whole number in one field and a decimal in another is.

The three are asked of what owns each. Whether every rule reached the reading is the reading's, and
is asked of the value rather than of the position for the reason above. Whether the ranges are the
whole of what the rules leave is the algebra's, because the derivation is there and so is the theorem
the answer rests on. Whether an end was written down as the number the rules stopped at is the
handover's. An edge stands where all three hold.

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
ordered value: an `Int`, a `Decimal`, a `Date`, a `DateTime`, a `Time`, an `Instant`, a `String`, an
enumeration, and a single-value newtype over any of them. A `Time` and an `Instant` were the two
this said and did not do (#846): each was ordered and read, and each was missing the conversion
that writes a count back, so a rule over one came back naming no line. What made that a gap in the
list rather than a decision was that nothing about the values said it — writing the two
conversions was all it took. The carriers are
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

That question is what the sentence covers, and it is narrower than every rule about the position. An
ordering compared against something no end came out of is one of these. An equality names a value
rather than an end, a denial takes one away, and a format, a membership or a quantifier says which
values exist: none of them is a line, so none of them is a line that went unread. A report has
nowhere to put one, and naming it would send an author after a boundary nobody wrote. What such a
rule leaves open is which values stand at the position, which is another reading's question and is
answered where that reading gives up.

Which limit stopped a comparison is one answer for both producers and not a classification each of
them makes. A relation asks for a class about several positions, a carrier nothing orders asks for
that order, and what is left is a form this does not take apart.

**And whether a comparison is a relation is the canonical comparison's answer, not the operands'.**
`x < y + 1` relates two positions as surely as `x < y` does, and it does so because the arithmetic
reads it as `x - y < 1` — a quantity over both of them. Positions named on either side establish
nothing on their own: `x < x + 1` names one position twice and cancels to `0 < 1`, which relates
nothing and states that every row satisfies it; `x < y * y` names two and stops the reading before
anything is known about what it divides. A comparison whose reading stops has no subject yet, so no
boundary and no partition is inferred from how it was spelled — what is recorded is that the reading
stopped, and which measures are thereby short of something is that reason's to say.

Read the other way round, the subject came off the operands while the line came off the canonical
form, and one rule was measured by one reading and reported by the other: a border was drawn at a
position nothing was owed about, and a question was raised about a place its rule never stopped.

And it is asked per rule. A position carries more than one statement, so a line read at it says
nothing about the rule beside it. Held as what a position is left with when nothing divides it, a
bound on a field's own type answered for the record's clause about that same field, and two
declarations differing by one bound said opposite things about the clause above them.

An invariant's bound gives a boundary and not a partition: everything outside it is refused at
construction, so there is no class on the far side to cover. A `guard`'s line has values on both
sides, so it gives a partition *and* boundaries — the value, and its neighbour where the type has
one. That is a question about the rule and not about the term: a length bound is owed one row at its
edge, and a guard on a length is owed the value and its neighbour, for the same reasons a number is.

What owes a row is the border, and it owes one at four points. Domain testing keys an `ON`, an
`OFF`, an `IN` and an `OUT` point on each border, and the same value can be one role for one border
and another for the next — so none of the four is a property of a value or of a class, and two of
them were answered by the measure that counts how many of a position's classes some row is in, which
is a different unit and has no word for a row on the far side of a line. The border answers for all
four, including the roles it owes nothing in.

A point nobody is owed a row at says which of three things settled it, because they ask different
things of a reader. The rules leaving no value there is the model's own answer and the point is
*excluded* — the word this specification already uses for a case the rules refuse, one arity up —
so an invariant's `OFF` and `OUT` points are counted out rather than left blank, and so is the `IN`
point of a side the rules leave one value wide. A carrier naming no neighbouring value is this
language having no way to write the point down, which is an item that cannot exist rather than one
nobody has got to. A rule that names a value rather than ordering the values around it has no side
for a nearest-outside point to be nearest on: under `x == 5` the 4 and the 6 stand alike, and
choosing one would invent the answer.

A line between two positions owes the same four, and they are the four of a border on the
difference the two terms fall apart by. A point of it is a pair standing exactly so many steps apart
and a side of it is a pair standing further apart than that, so `a < b` is at its `OFF` point where
the two are equal and at its `ON` point where `a` is `b` less one. Read as a place at one term the
step looked like something nothing could name, and the pair one step inside the border fell into the
side beside it — which is not a point going unreported but a row at the `ON` point being counted as
the `IN` point, and an `ON` point nothing owes passing a build that asks about it. What the carrier
answers for here is the same thing it answers for at a place: where it names no value one step from
the line, the two points against the line are not named.

Which of the four a build is told about is decided per measure, the way it is for every other
finding. A row against the line is what simplified domain coverage asks for and is a gap a build can
refuse over; a row away from the line is one of the two items reliable domain coverage adds, and it
is reported and refuses nothing. Both come off one assessment of one border, so a build is held to a
reading of one measurement rather than to a second one made to different rules.
A comparison is read wherever in a condition it is written. `cost >= 0 && cost <= 100000` draws both
lines and `cost <= 100000 || cost >= 500000` draws both, and which arm stands as evidence for each is
asked per comparison rather than per arm — a condition stops as soon as it is settled, so an arm says
nothing about an operand that never ran. That instrument is `OriginRef.GuardOrigin.Witness`, and it
is what lifted the restriction this said at first: only a comparison that was the whole of a
condition was read.

One shape is still lost, and it is not a restriction anybody stated. An equality against a case of a
sum takes the whole condition's lines with it: `kind == Domestic && cost <= 100000` reads no
threshold at all, and the position comes back not derivable exactly as it does for `kind ==
Domestic` written alone. The `cost` comparison is not merely uncounted — it is unread because of what
stands beside it, which is a defect rather than a line this declines to draw.

A cut keeps every rule that drew it. One value can be an obligation several times over — but a rule
that took a line in is not a second line. A relational clause and the bound it narrowed settled one
edge together and are one obligation, named by both.

The declaration named as having taken it in is the one whose clause relates the coordinate, and not
the value the position sits in. The same relation can be written on the record, on a record inside
it, or on a name wrapped round either, and only the one that wrote it has anything to answer for:
read off the value, an edge a wrapper narrowed was reported as narrowed by the record under it, and a
reader following that name finds no such clause there. It is not only what is printed — the name
tells one line from another — so a value standing in for the provenance made two lines one wherever
two declarations round a value each related a coordinate.

Which of them is holding the end is asked by taking each away. Having written a relation about a
coordinate is not the same as having decided where it stops: a second relation reaching a value the
first has already passed changes nothing, and named as the narrower it would make a line's identity
turn on a clause that moved it nowhere. The closure answers with a number and not with how it got
there, so the question is put to it again — seed the value without one declaration's clauses, and an
end that moves is an end that declaration was holding.

Per end, because they are two answers. One declaration can hold a minimum while another holds the
maximum, and a single name for both is wrong about at least one of them.

Where taking any one away leaves the end where it is, two or more of them are saying what the edge
says, and each is as much the answer as the others; choosing one would invent the thing that is not
known. Which is a reason to name them together and not a reason to name everything that was asked. A
candidate that moves the end nowhere when it is the only one left moved it nowhere here, and it is
out whatever the rest are doing — otherwise a clause reaching a value the coordinate had already
passed changes a line's identity by being written, which is the defect this paragraph exists to
prevent, coming back through the case where nobody is essential.

What is left is clauses that reach an end only together. Taking those apart is a search for the
smallest sets that suffice, and that is combinatorial; exactly which constraints a bound was derived
from is the closure's to record and it does not. So the set is the answer there, and saying so is the
limit of what this knows rather than something to guess past.

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

Reading inside a compound condition took the instrument this said it would take: a probe on each
comparison rather than on each arm. Without it the arm is reached without `cost` having been
compared, so reaching it is not evidence about `cost`, and treating it as evidence would report a
boundary as exercised that nothing ran against. With it, each comparison carries the site its own
value is recorded at, and what the shape of the condition decides is which arm a row that reached the
comparison can be in.

What remains lost is the sum equality above, which the whole-condition restriction used to hide: a
threshold beside `kind == Domestic` was one of the many this did not read, and is now the only one.

Keeping a rule per cut means the same value can be owed three times. That is the point: an invariant
and two guards that name 100000 are three rules, and a row that meets one of them has met one.

Naming the certificate changed no edge. Over the compiler's own suite, 10,994 readings and 4,156 edge
assessments: every reading the closure could certify was one the older test already passed, so the
theorem bought nothing it was not already quietly relying on. What it removes is a claim, not a
limit — a range the certificate cannot reach used to be reported as wider than the model.

Nothing was added to certify more. An edge could also be settled by a point checked against every
rule, which is a proof about one value rather than about a range, and it was measured before it was
written: of the 4,156 assessments, 68 were on a range no certificate reaches, and 60 of those already
had a row — one built through the module's decoders, or one already sitting there. The remaining
eight were held up by a rule that never reached the reading, which no point can lift. So the search
that builds rows is where an edge this cannot certify gets settled, and it is settled there for 73
per cent of every edge in the corpus. A second solver beside it would have had nothing to answer.

This decision is reconsidered where a proof about one end appears — a point of that kind, an end
rounded on a cut, or any reason to certify one end of a position and not the other. The certificate
here holds of a whole value, so nothing needs an edge to carry its own evidence, and none does: the
evidence exists on the cuts one reading draws and is collapsed to a boolean by its only reader, while
the cuts a threshold adds afterwards never carry it at all. Making only the first kind finer would
leave the two kinds of cut answering different questions. What comes first is one evidence model
every cut has, and then the finer answer on top of it.

Spec: `[#example-partition]`, `[#example-adequacy]`
