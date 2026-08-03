# ADR-0091: An unbuilt candidate does not prove a combination impossible

Status: Accepted. Fixes how combination coverage is counted and reported.

## Context

Two positions with two classes each is four combinations, and asking how many of them the rows sit in
is worth asking — most rules that involve two inputs are decided by those two, which is why pairwise
testing exists at all.

The number wants to be a ratio. Three of four, seventy-five per cent, a bar in a report. And the
denominator is not known.

A combination a row sits in is proven reachable: the row is the proof. A combination no row sits in
has not been shown to be anything. It may be a gap somebody should fill, or it may be impossible —
a record whose invariant relates two fields admits neither of two classes together, and no row will
ever sit there. Nothing in the model separates the two cases without trying to build a value.

Trying to build one does not settle it either. Two classes covering wide ranges have representatives
chosen from each, and those particular two can break a rule that relates them while other values of
the same two classes do not. `lo <= hi` refuses `lo = 101, hi = 51` and accepts `lo = 101, hi = 200`,
and both are the same combination of the same two classes.

So there are three states, and a ratio has room for two.

## Decision

Counts, not a ratio. A combination is *reached* (a row sits in it), *proven impossible* (a search
settled it), or *untried* — and the three are reported as three numbers:

```
pairs 12 reached / 15 known reachable, 7 untried
```

A single ratio is printed only when nothing is untried.

A candidate refused at construction moves nothing into *proven impossible*. It is reported as its own
reason — every value tried was refused — and the combination stays untried. Only a search that
exhausted a finite domain, or a constraint shown to be contradictory, may claim impossibility, and
nothing does either yet.

Single-position class coverage is measured on its own rather than derived from the combinations. A
behavior with one divided position has no combinations at all, and coverage derived from them would
report it as complete while a class of its one input goes untouched.

## Consequences

Nobody gets the percentage. A report that said 3/8 would read as five gaps when it may be five
impossibilities, and an author working the list would spend the difference finding out. Three numbers
are harder to put on a dashboard and are what is actually known.

`provenInfeasible` is in the shape from the beginning and stays zero. Leaving it out until something
fills it would mean changing the schema — which a build reads — to add a state that was always there.

The generator inherits this. It tries a class's candidates in order rather than giving up on the first
refusal, because the refusal was about the values and not about the classes; and where every candidate
was refused it says so, in those words, rather than calling the combination impossible. What could not
be written names the position that had nothing rather than the combinations that wanted it: a position
with no value makes every combination it takes part in unfillable, and saying so per combination is
one fact repeated as many times as the arithmetic allows.

Measuring single positions separately is a second traversal of the same rows, and duplicates part of
what the combinations already say. That is the cost of not letting a behavior with one input look
fully covered.

Spec: `[#example-adequacy]`, `[#example-partition]`
