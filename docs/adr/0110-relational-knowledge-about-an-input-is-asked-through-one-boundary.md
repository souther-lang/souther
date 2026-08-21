# ADR-0110: Relational knowledge about an input is asked through one boundary

Status: Accepted. Fixes where a question about several input positions at once is answered.

## Context

Everything the reading of an input hands over is per position. `Position.numericDomain()` is that
position's range, the admissible values are that position's, the unread reasons are about that
position. A rule that relates two positions divides neither of them, so nothing under
`souther/compiler/inputs/` had a unit for it.

ADR-0107 gives the interval algebra the relation and PR #906 makes each position's range take it in.
Neither reaches across the boundary, because the boundary has no form to say anything about. What a
caller with a form in hand could do was compose the per-position answers, and a product of
per-position answers cannot carry a relation.

Two fields each running from none to five, held together at five by their record, compose to a sum
running to ten. A guard cutting that sum at eight then drew a border on a quantity the model never
arrives at, the rows for it were rows nobody can write, and the report said of each that every value
tried had been refused.

The same loss appeared once more, and not as the same symptom. A search for a row at a point of a
form was handed the ends of each position and walked the box between them. Where the record holds
two fields three apart, each position's own range is already narrowed by the relation and their sum
already runs exactly as far as the form does — and the box still has a corner the rules refuse. The
search offered an assignment in the corner, the row was refused at construction, and one refused
candidate was reported as every value having been tried, of a point another pair stands at.

Conditioning the rules on an assignment was not missing. `FieldDomains` has taken a settled map since
#479, and two searches in `partition` already used it: a representative value of a declaration
composed field by field, and a row's value for one parameter chosen a position at a time. The third
search never found the capability and took the box.

So the capability existed and had no boundary. A search written without one either re-derives it or
goes without.

## Decision

The declarations reaching a behavior's input are asked through one boundary, in the vocabulary of
that input's paths and forms.

`Quantities` answers where a form over several positions runs, where one position runs, what is left
once positions are fixed, and why nothing is left. Conditioning is a refinement of what is asked
rather than a second reading: fixings accumulate and the declaration is read once from the top, so
fixing nothing changes nothing, fixing twice is fixing both, and the two orders agree — of what is
left and of what is proved empty alike. Which route proved an emptiness is not observable, or a cache
and an arithmetic would decide what the model says.

**Every term is answered for on its own first, and the relation is met onto that.** What one term
runs between is where it stands if it has been fixed, what its own position was read to hold, and
what the term guarantees of itself; what the rules relating the terms leave the form is met onto the
sum of those. Meeting only narrows, so a border can go away for being asked about properly and can
never appear.

That order matters because the reading that relates positions has a name for some terms and not for
others, and answers a form one parameter at a time. Asked only there, a floor on a position the
arithmetic has no word for is dropped — a string stops at `"A"` and there is no number for a relation
to be about — a value the caller has just fixed at a coordinate no clause ever named is forgotten,
and one term the reading cannot name takes the answer about every other term of that parameter with
it. All three are the same mistake: an answer already in hand given up because the mechanism asked
for it declined.

A form that is one term taken as itself is that term's own answer, met with what the relation leaves
it. The arithmetic is the identity there, and it is the only shape a position the arithmetic cannot
count is ever asked in — a form adds its terms together and two strings have no sum.

**And within a part the facts are solved together rather than met after.** Projecting is not
distributive over meeting either: what the rules leave a form, met against what each of its
coordinates is known to be, is wider than what the rules and those facts leave it together. A rule
holding two coordinates at one apiece says nothing about a form that also names a third the rules
leave unbounded — the third goes as far below nothing as anybody likes — and meeting a bound on the
whole form against another bound on the whole form cannot put the rule back. So what a position was
read to hold and what a term guarantees of itself are taken onto the rules before the form is
projected out of them.

Both of those are one thing said twice, and it is the thing this whole boundary keeps getting wrong:
an answer assembled at a coarser unit than the facts are held at loses whichever fact the coarse
mechanism has no room for. Add at the finest unit that carries the relation, and solve within it
rather than meeting projections.

A term is queryable where what it sits under is something the behavior takes. **Owned is not the
same as known about.** The walk that reads an input's positions stops two levels down, where a report
stops being about anything an author would call one input, and nothing stops a rule from naming what
is under that — the reader that turns an expression into a path follows as many fields as are
written. Such a term is this input's and is answered for, with whatever it guarantees of itself and
nothing the declarations relate it to, because the reading has no position there for a relation to be
about. The reading already has a word for that position: *the walk stopped before reaching what is
under it*. Ownership settled by which positions the walk found instead, an ordinary rule naming a
field of a field of a field stopped a measurement rather than being measured.

What is refused is a term under something the behavior does not take, which no reading of this input
could ever answer for — as an emptiness it would be a bug wearing the words of a contradiction in the
model, and as unbounded it would be one wearing the words of a model that says nothing. Whether a
path names a field the type actually has is settled where the term is made, and not here: a path is a
location and the declarations are what say what is at one.

Rules reach an input from the declarations of its parameters and from nowhere else, so two parameters
are related by nothing. A form spanning both is answered by solving each parameter's part of it
against that parameter's rules and adding the results: the parts stay forms and only the answers are
added. That composition depends on nothing relating two parameters, and a behavior whose own clauses
relate them is the day it changes.

**One coordinate, read and written.** A position is measured at its own value or at a count taken of
it, and the two are different numbers under one path. Reading was given that pair and settling was
not, so a rule over two counts was read whole when it was asked about and left unconditioned the
moment one of them was fixed — a contract with an exception in it on the day it was written. Both
sides name a coordinate, and a settling of one is stated in a single place
(`ConstraintState.settling`), so a reading made with a position settled and a reading settled after
it was made say the same thing rather than two things that happen to agree.

**Settling does not read the clauses again.** A settling is an equality on one atom taken onto
everything else the clauses came to, which is what the reading does with one at the end of its own
work — so arriving there directly is arriving where the reading already is. Read again instead, a
search fixing a position per step down a box read every rule of every declaration per step: twenty
thousand readings for one behavior, against twenty-seven for the same answer. What a settling hands
back answers about the constraints and not about a reading, and what a reading derives beside them —
which values a position may hold, what it must hold, which rule placed an end — is neither recomputed
nor offered, so nothing can read a settled state for an answer worked out before the settling.

**A capability, not an answer.** Asking the declarations a further question takes a way of reading
them, and what a question is answered with is compared as a value by whatever decides that a compile
changed nothing. So `Quantities` is built where it is used and never kept in `InputDomain`, which
holds what the behavior takes and nothing that reads it. It is built once per walk and handed down:
one per comparison would read every parameter of a behavior once per comparison written about it.

**Knowledge, not search.** What is answered is what the rules leave. Where a row goes, how long to
look for one, and what follows from having given up stay in `LevelRealizer`. It walks what
`Quantities` soundly leaves, which the actual set is a subset of; `Impossible` is sound by the
direction of that inclusion and not because the two are the same.

**One place turns a placement into an answer.** What a search hands back is the same thing whatever
it was searching for — one position at a place of its carrier, two of them a distance apart, a form
at a level — and each of those searches is written on its own. Written on its own, each also had to
remember to hold what it found against the rules, and two of the three did not; they were noticed one
at a time, which is what a per-shape obligation costs, and a fourth shape of line would have cost a
third noticing. So the obligation is not per shape.

**Narrowing may be given up and the answer may not.** A search reads the rules again as it fixes
positions and skips what they leave nothing beside. Past a budget it carries on against what they
left before anything was fixed, which is wider and refuses nothing it would have kept — that is
giving up precision. What it may not give up is what it hands back: an assignment out of the wider
box that nothing held against the rules is one the record can refuse, and offered as a row it comes
back refused where it is built, which a report says as every value having been tried of a point some
other pair stands at. So the narrowing is budgeted and the last step is not. A complete assignment is
put to the rules whatever the budget did, and what is handed back is one they were not shown to
refuse.

Not one they were shown to leave. Nothing here builds a value, and an emptiness nobody proved is not
a value proven to exist — what settles that is the row itself, where it is built. What the last step
removes is narrower and is the whole of what was wrong: an assignment the rules are already known to
refuse, offered as though it were a row.

**Two other readers condition a declaration, for two different reasons, and neither is this boundary
not yet reached.** `Partitions.composed` builds a representative value of a declaration reached while
producing a fixture: there is no behavior, no parameter and no path rooted at one, so its subject is
the declaration and the declaration's own words are the right ones. `Generator` does have an input for
its subject, and finds that input's positions with a walk of its own that descends to eight where the
reading of an input stops at two — deliberately, since one stops where a report stops being about
something an author would call one input and the other goes on until there is a value to build. Two
walks answering "which positions are there" differently is a fault of its own, and deciding which
depth owns which question is not what this boundary settles. A test over the compiled classes names
both, with the reason each is there.

A proof of emptiness is said in this input's words, which is the whole reason it is not the
declarations' proof handed on. Where that proof names a position, the path it names is the value's
own — `x` for a field of the record the clause was written on — and the caller's is the parameter and
that path together. The where is carried across and the why stays where it was proved: one step and
no further, because what sits under the step is a proof about some other value whose places are not
this input's to spell.

## Consequences

`Cutting` no longer composes a reach out of per-position ranges, and `Partitioning` carries the
reading rather than a map from term to bounds. `Position.numericDomain()` and
`Quantities.runsBetween(term)` were measured against each other over every position the conformance
corpus reaches before the second was allowed to answer for the first; they agreed everywhere, on a
corpus that reaches twenty-four positions of which eight say anything, so what carries the claim is
the checked-in answers and the suite rather than that measurement.
