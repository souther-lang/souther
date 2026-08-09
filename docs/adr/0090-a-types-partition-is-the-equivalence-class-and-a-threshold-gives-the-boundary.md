# ADR-0090: A type's partition is the equivalence class, and a threshold gives the boundary

Status: Accepted. Fixes what the compiler may derive as an equivalence class, and what it may not.
Revised in place for #427: what a threshold is intersected with is what the *position* admits, which
is the field's type read under the rules of the record holding it. Revised again for #510: what a
line is drawn on is a numeric *term*, not a position — the content of a location, or a size taken of
one.

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

A record's rule takes an edge in and does not put one there. A position its own type leaves open stays
one the model draws no line through: a rule between two fields is not a partition of one of them, and
treating it as one would divide an `Int` the author never bounded. What is read of such a rule is an
ordering of numbers and nothing else; a rule of another shape leaves the position where its type left
it, which is the safe direction — an edge too far out is a row nobody can write, and an edge never
moved is not one either.

An edge whose rules were not all read is not a gap. Both answers were wrong: counting it asks for a
row that may be impossible, and falling back to the type's own edge is no better, since the rule that
could not be read refuses that value as readily as the one beyond it. So it is reported, left out of
the denominator, and refuses no build — which is what ADR-0091 already does with a combination nothing
has settled, for the same reason. What settles it is a witness rather than an argument: a row at the
value went through the decoder, and from then on the edge is counted like any other.

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
the positions it was written against. What is spaced like an `Int`, what its own values are, and how
it is read off a row are three properties of the term — a size needs no boundary domain of its own,
and its non-negativity is its own rather than something a rule has to state.

A position no rule measures keeps its own name. A `String` nothing says anything about is not
derivable and is reported as the position, because naming its length there would put a term in the
report that nobody wrote.

An invariant's bound gives a boundary and not a partition: everything outside it is refused at
construction, so there is no class on the far side to cover. A `guard`'s line has values on both
sides, so it gives a partition *and* boundaries — the value, and its neighbour where the type has
one. That is a question about the rule and not about the term: a length bound is owed one row at its
edge, and a guard on a length is owed the value and its neighbour, for the same reasons a number is.

Only a comparison that is the whole of a `guard`'s condition is read. A condition built with `&&`,
`||` or `!` contributes no threshold.

A cut keeps every rule that drew it. One value can be an obligation several times over — but a rule
that took a line in is not a second line. The bound and the record that narrowed it settled one edge
together and are one obligation, named by both.

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
