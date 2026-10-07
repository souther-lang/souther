# ADR-0122: The meaning of a condition is read once, off the analysis representation

Status: Accepted.

## Context

A body is held two ways. The analysis representation keeps the language's operations standing as
the calls they are — `List.filter`, `List.isEmpty`, `Bool.not` — so a rule about one is read off the
operation (ADR-0097). The runnable representation expands every helper with a body, the library's
included, into what it does: `Bool.not(p)` becomes a `let` and an `if`, `List.filter` a fold.
Partitioning reads the first. Coverage and reachability read the second.

Each of them also worked out, on its own, what a condition means. Partitioning read whether a
filtered list holds anything as whether some element met the filter's closure, and read it in two
places that did not agree on when it applies; it read `List.any` as a quantifier in three. Coverage
read a condition one comparison node at a time and knew no operation at all. Reachability read a
denial only where the analysis tree spells one, while walking the tree where it is spelled as an
`if`. So spellings that mean the same thing came out differently depending on who asked:
`List.isEmpty(xs)` and `List.length(xs) == 0`, `Bool.not(p)` and `p == false`, a filtered list's
size held at least one and the same list asked whether it is empty (issues #2202 and #2209). Every
new way of deriving a value — a filter, a mapping, a branch building a list — needed a reader of its
own in each of them.

The two representations are not the defect. They answer different questions, and the
correspondence between them already exists: `ModelOccurrence` is what the two readings of a body
agree about, and the emission indexes cross from it to the places a run records.

## Decision

The meaning of a condition in static analysis is defined once, from the analysis representation and
the library's checked operation facts. It is a proposition about the subjects the condition is
finally about — a position of the input, an answer a dependency gave, or a value nothing reads,
which stays named as unread — reached by carrying what is asked of a derived value back through how
it was derived. Nothing is pushed back by guessing: a step is taken only where the operation's
declared facts or the construct's own semantics make the two statements equivalent, and where none
does, the proposition says it stopped there and why.

The runnable representation represents execution: which paths a run takes, where a construct is
materialised, and what a run records. No analysis defines the meaning of a condition of the model
from it. A fork inside a copy of a library operation is no condition of the model, so no obligation
is drawn on it; it is still a path a run can take, and reachability keeps walking it, taking nothing
from its condition that the shared meaning does not give.

The two are joined by `ModelOccurrence`, the construct of the model a materialisation is one of. The
join is partial — a construct inside a library operation has none — and one to many: one construct
is materialised wherever the body holds a copy of it, and the index of meanings keeps every copy.

Three identities are kept apart:

- **Which proposition.** Decided by the proposition's structure, so two spellings of one statement
  are one proposition and a variable bound by a quantifier is told apart by where it is bound, not
  by what it is named.
- **Which construct of the model it was read from.** Carried beside the proposition, occurrence by
  occurrence, and part of the answer's identity: `p` and `p || p` are one proposition and two
  derivations.
- **Which place a run recorded.** The run's own, reached from a construct through the emission
  indexes.

Partitioning, coverage and reachability each still do their own work on the meaning — which answers
a condition can give, what a fork turns on, what a row must hold, which arms a run can enter, what a
row was seen to do — and none of them reads a construct's meaning on its own. A condition the
meaning cannot read, and a condition no place a run records is equivalent to, is unresolved and is
reported as such; it is never taken as read, and never filled in from what the fork around it
answered.

## Consequences

- An operation joins every analysis at once by declaring what it means. Whether a result holds
  anything, holds true or holds a value, as a statement about some element of what the operation
  walked, is declared as a law equating the two, not as a dependency between them.
- Evaluation order is not the proposition's. `p && q` and `q && p` are one proposition, and which of
  them a run consulted is told by the run and by the order the runnable body evaluates them in.
- A row's evidence for a column of a decision is taken only from a place whose recorded answer the
  meaning shows to be that column, either way round; a place that answers more than the column, such
  as a fork whose condition joins it to another, is no evidence for it.
- Choosing a value for each input to satisfy a proposition is a separate capability from stating the
  proposition. A disjunction the meaning states and no row composition can yet satisfy stays
  unresolved for composition and is not dropped from the meaning.
