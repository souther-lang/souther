# ADR-0127: A step handed over as a value is applied inside the loop around the call

Status: Accepted. Extends ADR-0126; the rewrites it lists and the rows they owe keep their meaning.

## Context

ADR-0126 rewrites a walk by a switch at the walk. A fold whose step is written where the fold hands
it over is emitted as a loop around the call, with the step's body as the loop body, and the switch
stands in that loop. A fold whose step is chosen as the program runs, or reaches the fold as a
value, was left to the library's `foldFrom`, one method for every fold of the program. A switch in
it would rewrite them all, so such a walk was reached, recorded, and left undecided with the reason
`step_not_expanded`.

That limit was a property of how folds were emitted, and not of the program: what the walk is does
not depend on whether its step can be written into the loop.

## Decision

Whether a call is emitted as a loop is decided by what the call is (`Core.Call.isWalk`) and by the
step being applied at all (`omitsFunctionBody`), and no longer by whether the step is a block. One
loop is emitted for both. A step written where the fold hands it over is its body, as before. A
step that is not is worked out once, before the walk, into a local, and applied at each element with
`Fn.apply`, the way any function value is applied. Choosing it again at an element would be another
fold. The seed and the list are worked out once as well, so handing the seed again does not work
its expression out again.

The walk is recorded after the arguments it is handed have been worked out, as a call of the
library's method records it: a run that stopped working them out has not entered the walk.

A build of a list or a map writes into its builder in the step's own body and has no step to hand
over, so it is still emitted as a loop only where the step is a block.

The coverage plan no longer reports a reason for a walk the classes carry no switch at, except the
method that could not hold the switch. `step_not_expanded` is no longer raised. It stays a word of
the report schema, since reports written before carried it.

## Consequences

The rows a fold owes are put to a fold whose step is a value as to any other, and the adequacy is
decided by them: rows of at most one element are asked for, and rows of two are enough.

A step applied as a function value costs what applying one costs: an `Object[]` of the boxed
arguments per element and a boxed result. The loop is the caller's own, so the call site applying
the step sees the steps of one fold and not those of every fold in the program.
