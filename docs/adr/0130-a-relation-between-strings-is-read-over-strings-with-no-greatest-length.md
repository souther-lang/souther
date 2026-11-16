# ADR-0130: A relation between strings is read over strings with no greatest length

Status: Accepted. Follows ADR-0128: what a representation cannot write is no fact about the values.
Extends ADR-0122: what a condition means is read once, and so is the world its classes are drawn in.

## Context

A relation between two strings parts each side by what the other side can hold: the strings some
value of the partner is, and the strings outside which none is. The classes of a place are cut from
those two sets, and a class is where some row has the relation come out one way and another row the
other.

A `String` holds no more than a greatest number of code points, which the language keeps in one
place (`Strings.LONGEST_TEXT`). It makes a fact the sets can be wrong about at its edge: a piece of
an address after its `@` is at least two shorter than the address, so a string of the greatest
length is no piece of any address, whatever the language of the addresses says.

The reading met that edge three ways in turn, each with a defect of its own.

- Strings past what a piece can be were left on no side of any rule. A value of the place was then in
  no class, and the classes were not every value the place holds.
- Strings past it were put on the false side. The false class then took in strings of that length
  only, which no row can write, so a model whose strings are not bounded by a rule of its own could
  not be complete at that place.
- Strings short of it were cut from what the other side can hold by the room a value written round
  them needs. A region was left open for the length of that room, which no model declared.

All three came from the same absence. Nothing said which world the sets are over, so each reader of
a set derived what was sound from the strings a `String` can hold, found the edge wrong in one
direction, and moved it to the other.

## Decision

The classes of a place of strings are drawn as though a `String` had no greatest length. The sets a
relation leaves of a side, and the regions a rule's statement is made of, are over the strings of
the languages at every length, and a length cuts a region only where a model declared it: a rule on
the length, or the lengths a pattern holds.

This is the rule the language already keeps for lengths and for sizes. The longest string ends no
class of a length, and no collection size ends a class of a size, since where the representation
stops is no distinction a model made and a class of it only a value at the edge could fill is one no
row is in. A set of strings is the same case, and is read the same way.

What a class claims is therefore a claim about the strings without that edge, and it is not a proof
that a value is there. A string within a few code points of the greatest length, whose partner would
be longer than any value, is read as having one, though no value does: a place a model holds to such
lengths has values, and none of them is the piece of any value of the other.

The error runs one way, and the reading is held to it. The sets say more strings can be a partner's
than a value allows, never fewer, and they are used only to make an obligation: a class of a
position, which a row is owed for. Nothing is met by a set. What meets an obligation is a row that
ran, so a class the unlimited world has and the world with the edge does not is owed a row no value
can be written for, and is said as a gap; it is never shown met. The classes the edge alone would add
are the ones not drawn, which no row could meet.

The one reader of what a statement says is the making of those classes, and an architecture test
holds the readers to it: a new one has to say what it does with the sets, which is never to take
them for a value there is.

The edge has its own facts and they are said once, not as the open part of every relation past them.
An operation that ends a run only where its answer would be longer than a `String` holds, or a
collection would hold more elements than one holds, is read as answering on the runs the classes are
drawn over, and is listed with where it is written: `stopsPastTheRepresentation` of the partition of
the behavior. A stop at an `Int`'s end, a refused construction and the rest are unchanged, and so is
every proof that a body ends no run, which asks the operation's own account.

## Alternatives

**The edge on the false side.** The strings a value cannot hold a partner for are put on the false
side by their length. Exact for the world with the edge, and refused: the class that comes of it
cannot be filled by any row, which is the defect that made the edge a thing to leave out in the first
place.

**The edge on no side.** Refused for the reason above: a value in no class is a gap in the
partition, and a claim that the classes are every value the place holds is false.

**A bound by the room a value needs.** A string is shown to have a partner only up to the greatest
length a value could be written round it at. Refused: it is a boundary of the edge under another
name, and opens a region at a length nobody declared.

## Consequences

- A claim that a place is divided into these classes, and that every class has a row, is a claim over
  the classes a row can be in. Classes only the edge could fill are not drawn, as they were not for a
  length.
- A model that holds a string to lengths within a few code points of the greatest is read as though
  the greatest were not there: the class it is owed is owed a row no value can be written for, and
  is a gap and never a met obligation. Nothing in the corpora does, and a bound a model declares is
  still a distinction and still cuts.
- The partition of every length is held by a test: the true, the false, the open and the unreached
  strings of a rule are every length, so a value of the place is in a class at any length.
- The partner of a string near the edge having none is the fact of no operation, so nothing lists
  it. A reader that needs it for a value reads the language of the values, which holds the edge.

## References

- ADR-0128
- Specification: `[#what-a-collection-holds]`, `[#example-partition]`
