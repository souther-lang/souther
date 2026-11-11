# ADR-0129: A statement is against a place or a written value, and a written value is no subject

Status: Accepted. Extends ADR-0122: what a condition means is read once, and so is what it is
against. Follows ADR-0085: sameness is defined once and every reader asks it there.

## Context

A condition is read as propositions about subjects, a subject being a value a row controls: a place
of the input, or what a dependency answered. `Map.containsKey(key, rates)` is read as some key of
`rates` being the value at the place `key`, and a row is composed holding it. A key the source
writes, `Map.containsKey("USD", rates)`, is neither. It stands at no place and a row writes nothing
toward it, so the statement was left unread, and a count over it carried nothing to evaluate.

The limit was not in one reader. The reading of a statement, the demands on a container, the places
a rule of a declaration reads, and the entries a record's builders keep each named the member of a
container, or the other side of a sameness, by a place and by nothing else. A rule that asked a
container for a written member was dropped by the clause reader, so a type with such a rule could
not be composed; the search for a counted element built a collection holding the one value it found
named; and a case was told apart by the name it is shown under.

Three ways to give a written value a place in the vocabulary were weighed.

- A subject that is a constant. A subject is what a row controls, and what its readers ask of it —
  the place it stands at, the element it is of, whether it is under another place — has no answer
  for a constant. Every reader that matches on what a subject stands at would carry an arm for a
  subject that stands nowhere.
- A proposition of its own for a subject being a written value, beside the sameness of two subjects,
  with a demand target, a set of names the search tells apart and a writer of values into rows of
  its own. This was written first. Every exhaustive switch over the propositions had to list the new
  kind, each layer grew a second name for one distinction, and the second reader of the entries a
  record's builders keep did not learn it at all, because nothing made it.
- One type for what a statement is against, used by every layer that names a member.

## Decision

`Operand<P>` is what a statement about a member of a container, or about two values being one, is
against: the value at a place `P`, or a value the source wrote. The layer using it says how it names
a place.

A sameness relates a subject to an operand, and a value written is always the other side. The
demands on a container (an element is, or is not, a value; a key is, or is not, a value) are against
an operand of the input's places. What a rule of a declaration asks a container to hold, in the
places a clause reads and in the entries the record's builders keep, is against an operand of the
rule's places, and both read a written member through one fold. A value written is written into a
row by one writer of a constant at a type.

A value has a spelling it is shown by and an identity it is told apart by, which for a case is the
declaration and not the name. A proposition is told apart by the second.

Whether a demand is the plan's — asked as it is, of every element — is the quantifier's and the
container's to say, and a value being written does not make it the plan's. A written value needs
nothing handed on from another parameter, so under a quantifier that does not ask the plan it is
asked of the container once where some element is asked it, and not at all where none is.

A collection an element holds is told apart by which of the values a statement names it holds, so a
search for an element builds the collections holding some of them, taken from the ends — none of
them and all of them, then one and all but one, and so on — within the figure a search tries and
with that figure said where it is passed. What a statement needs of them is not known there, and
the subsets it needs are those its structure makes extreme: a conjunction needs all, a disjunction
one, a denial all but one or none. The subsets are made and not walked to, so the work is that of
the ones made however many values are named.

What a statement names at a place is a value written there or how many the place holds, and the two
are cases of one type and not one kind of number: a value is put at the place, and a number of
elements is no value to put there. Where a statement names both of one collection, it is built
holding the values chosen and that many.

Each collection is asked of the builder that owns collections (`Witnesses.holding`), with the
values named and not chosen kept out of it and with the range of how many the place may hold, which
the rules of its type and of the record holding it leave. What may stand beside the values chosen is
that builder's to say: a list may hold a value again and a set or a map may not, the rules give a
floor, and a collection beyond what a proposal may hold is not built and the budget is said. A
second builder of collections in the search would have to repeat each of those and would come apart
from the first at the first it missed.

## Consequences

A written member is read and composed wherever the same member at another place of the row is: in a
count, in a rule of a declaration, and where a record is built. A reader that names a member by a
place and nothing else is the defect this closes, and a new reader of a member takes an operand.

A newtype's constructor written where a place of that newtype's type is asked for is the value it
wraps: the place holds it under the name it wears, and a row writes it back under that name. The
fold that reads a written value takes the construction so only for the reader that asks, with the
newtypes of its own reading; a rule is discharged on what the fold alone says, which a construction
is not a constant of, and a case is no value a member is asked to be. A rule of a declaration
cannot make a construction at all, so the readers of its clauses read primitives only. A row's value
is compared with a written scalar under the names it wears.

A container beside the elements, asked the same thing by every element, is asked the same thing of
the row however it is written, so a count over it takes no number between none and all of the
elements.

Two questions are left. Whether holding a written member divides the place of the members, as a
comparison against a constant divides a position, is not decided (#3144). Where the question of
whether an observed value is a written value lives is not settled (#3145).
