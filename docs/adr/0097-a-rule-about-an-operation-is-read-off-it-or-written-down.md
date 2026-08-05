# ADR-0097: A rule about a library operation is read off the operation, or its absence is written down

Status: Accepted

## Context

Two checks read the standard library's operations and each kept its own table of them.

The totality check credits a value a combinator hands its closure as a sub-term of the container, so
recursing on it is structural. The invariant-discharge check binds that same value to the container's
element type, so a construction inside the closure is analyzed rather than left opaque. Both needed
the same three numbers — which argument is the closure, which of its parameters the element arrives
on, which argument the container is — and both wrote them out: the same twenty-four rows, in the same
order, in `TotalityChecker` and in `DischargeRules`.

An operation the library gained therefore had to be added twice, and adding it once was not an error
but a silence: a table with no row for an operation answers "nothing is true of it", which is also
what it answers when nobody looked. `List.distinctBy` was in neither table, and in neither of the
neighbouring ones. A valid recursive helper written through it was rejected, and a guard on the list
it was built from stopped discharging — with nothing said about a missing row.

Counting the range of each table showed the same shape elsewhere. Of the thirty-three operations that
answer a container built from a container, fourteen had a rule and nineteen had nothing: most of them
because a shape genuinely cannot say what `Map.union` or `Set.insert` keeps, one of them because the
row was never written. Which was which was recorded nowhere.

## Decision

**What the checks know of a library operation is answered by the operation, and where it cannot be,
the question states which operations it is asked of and every one of them answers.**

Two halves, in this order.

*Read it off the declaration where the declaration determines it.* What a combinator hands its
closure is stated by its signature: the argument that takes a function is the closure, and the
parameter whose type is what a container argument holds is the element. So it is derived rather than
listed, and an operation the library gains is answered for by being declared. A signature that admits
more than one reading — two function arguments, two parameters that could each be the element —
raises where it is read rather than answering half.

*State the range and answer it where the declaration does not determine it.* What a construction
keeps of the container it was built from, what a predicate over a container says and how far, whether
a number is a size, which operator a call is the function form of: none of these follow from a type.
Each is a question with a range — the operations it is asked of, settled by what they are declared to
be — and an operation in range answers it either with a rule or by being named among the ones there
is nothing to say of, with the reason. Adding an operation to the library fails the build until
someone decides which, and the decision is written where the next reader finds it.

A rule is worth having only where something can travel through it. What the check states of a
container it names by that container's kind — `List.length` and `List.all`, or `Set.size` and
`Set.contains` — so a rule relating a set to the list of its elements carries nothing however true it
is. Those are among the operations there is nothing to say of, and the reason recorded is that a
statement spanning kinds is what would have to exist first.

## Consequences

`List.distinctBy` is credited by both checks, and eight constructions that could only drop elements
or keep their number — `Map.remove`, `Set.remove`, the two intersections and differences,
`Map.updateIfPresent` — now carry a size where they carried nothing.

Adding an operation to the standard library is no longer a change to the library alone. It answers
the combinator question by being declared, and it fails the compiler's tests until the questions its
declared shape puts it in range of are answered.

The judgment stays where a reader can weigh it. Deriving what a signature determines does not turn
the rest into a derivation: that a map hands its closure the value rather than the key, and that a
filter keeps what held of every element, are still written down and still argued in prose.
