# ADR-0104: A behavior states a relation between what it is given and what it answers

Status: Accepted. Completes the postcondition side counted by ADR-0003 without changing its
decision about preconditions or violation destinations.

## Context

A data invariant can relate values carried by one data, but no existing declaration can relate a
behavior parameter to its answer. `findTodo : (id: TodoId) -> Todo | NotFound` cannot state that the
answer carries the requested id: neither output case knows the request, and wrapping both sides in
one result changes the model to satisfy the checking mechanism.

The existing invariant-discharge analysis also draws an important boundary. It can carry affine
relations between numeric positions today, while a structural equality between positions is runtime
only. Adding a postcondition must report that distinction rather than imply a proof the constraint
domains cannot hold.

## Decision

`ensures` is a reserved behavior-signature clause. Its expression names the answer as `value` and
at least one parameter by the name written in the signature. A property of the answer alone remains
a type invariant; a property of inputs alone remains ADR-0003's precondition and business-case
decision.

A single output type takes an expression directly. A sum output names the case or cases for which
the expression is stated, and the expression is elaborated once for each named case. An arm may be
unspoken for and there is no wildcard. Clauses may be named under the invariant clause-name rule.
A `>->` composition carries no clause because it writes no parameter list and stage clauses are not
inferred transitively.

One generated `<Module>.<Behavior>$Ensures.check(parameters..., value)` implements the clauses.
A Souther implementation calls it at the exit of `$Impl.apply`; an injected answer calls it where
it crosses into generated code. Example and fake values invoke that same generated method. A
violation is a `ConstraintViolation` carrying an `EnsuresFailure`, not an output case and not an
`InvariantFailure` relabelled with a behavior name.

An `example` row and a `fake` row write both sides of the relation down, so each is run through
that check while the module is compiled and refused where it does not hold (E1928, E1929). This is
the policy ADR-0093 said the language did not have. That decision is about two descriptions of one
behavior — a stand-in and a recorded row — where nothing names either as the right one, and it
stands: E1919 remains a warning naming both. A written value against a declaration is a different
pair, and the declaration decides it. An arm is part of what a row wrote, so a bare case name naming a unit case
is a whole answer and is held; a `_` row of a fake and a `with` write only one side of the relation
and are held only where the behavior answers. A bare case name carrying fields is not held yet: the
arm names the answer, but the check is asked about an answer rather than about an arm, so a rule
reading only the inputs is decidable from such a row and is not decided. A table with a row that is
refused is not one to stand in with, as a table that will not build is not, and is not compared with
the rows recorded for the behavior either: ADR-0093's comparison names neither side as right, and
this has named one, so the two cannot be said about one pair.

Callers seed a clause only after the output arm is known and only where parameter-to-argument
substitution leaves terms the existing analysis can name. Classification uses the invariant
capability procedure with the parameter and answer locations supplied to it. Structural equality
therefore remains checked but runtime only until a congruence domain exists.

The declaration and every helper it names travel with the module. `BOUNDARY_VERSION` moves from 15
to 16 because an older compiler cannot read the new clause or preserve the assumption it publishes.

## Consequences

A model can state lookup and filtering meaning without changing output shapes. The run-time cost is
paid once per checked call, like an invariant is paid once per construction. A relation that can
really fail in ordinary business data is still a result case reached by a guard; writing it as
`ensures` turns a modelling mistake into an abort, exactly as ADR-0003 warns.

No body-wide refinement proof, congruence domain, precondition construct, new output case, or
transitive composition relation is introduced.
