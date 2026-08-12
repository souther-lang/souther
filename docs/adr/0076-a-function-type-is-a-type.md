# ADR-0076: A function type is a type, and a position asks what it requires

Status: Accepted. Amends ADR-0025, generalises ADR-0004.

## Context

ADR-0025 decided that functions are first-class values. The grammar did not follow: a function type
`(A) -> B` could be written in one position, a helper `let`'s parameter, and nowhere else. A name is
a value where its type can be written, so that one position decided where a function could go.

The result was a language that accepted a function value and then refused to let it travel. A lambda
chosen at runtime could be bound and applied but not handed to `List.map`; a helper's name could be
called but not named; a binding could not say what function it held. Two of those refusals the
language stated. The other two were the grammar's, and had no reason behind them.

Issue #198 asked for measurement before design, and the measurement does not support the feature on
convenience grounds. In souther-examples — 24 modules, 7007 lines, 289 helpers, 101 lambdas, 76
higher-order calls — no author writes a function-typed parameter at all; every one of the 23 in the
tree is in the standard library's own `.sou`. No corpus line gets shorter. Partial application was
declined on a stronger showing than that (one place in 215 lambdas), and this is not proposed as a
convenience.

What it is proposed as: ADR-0025 is already decided, and the implementation accepts or refuses the
same type by the syntax that produced it. That is the reason to do it, and the measurement is
recorded so that nobody reads a corpus need into it later.

## Decision

**A function type is an ordinary type term.** It may be written wherever a type may be written: a
helper's parameter, a behavior's input and output, a data's field, a newtype's base, a type argument,
a tuple element, a local binding's annotation. A function type's parameters and result are whole
types, so `->` is right-associative and a function may take a function and return one. A
parenthesised single term is grouping; `(A, B) -> C` takes two parameters and `((A, B)) -> C` takes
one tuple, mirroring what ADR-0036 decided for a lambda's parameter list.

**Being writable in a position is not being usable in it.** What a position admits is decided by what
that position requires of a type, asked of the type and not of the syntax that spelled it:

- *boundary-representable* — an external representation. Required by a data's field, a newtype's
  base, and a behavior's input and output, which are where a codec is derived or crossed. This is
  ADR-0004 as a predicate over types rather than a restriction on where a function type may appear,
  and it is what finds a function nested inside `List<(Int) -> Bool>` or `Map<String, List<(Int) ->
  Bool>>`, which no syntactic rule reaches.
- *equality* — required by `==` and `/=`, by a `Set`'s element, and by a `Map`'s key. Asked of what
  elaboration decided, not only of what was written: `List.distinct` grows a set of what it has seen,
  and only the elaborated type says what its elements are.
- *ordering* — required by `sort`, `max`, `min`, and by the key a `sortBy` projects to. The refusal
  is about the key's result type, not about the function projecting it.

The three are separate predicates. That a function is the only type failing all three is a fact about
the types there are now, not a claim that they are one question; a type carrying a representation but
no ordering would separate them, and only their shared walk would move.

**A module's published surface requires none of them.** A published value and a published helper
cross as source, expanded at the reader's call sites (ADR-0075), so nothing is encoded and a
published function-typed value is a published helper by another spelling. This holds under the
current source-expansion scheme; introducing an ABI that passes run-time values between modules would
put the question back.

**A name in a value position is the function it names.** A helper written where a value goes is the
lambda that applies it. A recursive helper expands the same way, since the call inside stays a call.

**A binding's type may be written, and is what settles a lambda's parameters.** ADR-0025 reads
parameter types off the applications in the body, and every one of those is typed in the enclosing
scope. An application inside a lambda binds its arguments there, so it says nothing here — which is
exactly where a combinator's expansion puts the application, and is why a function value could not be
passed to one. Such an application is not a constraint and is not an error. When no application can
be read, the type is written down instead.

## Consequences

Issue #198 closes. The four lines it opens with compile, and a function taken out of a collection
runs.

`Ast.TypeTerm` is a sealed sum of a reference and a function type. Making it one rather than another
field on a reference is what put every reader that must decide about a function type in front of the
compiler; a silently unhandled case is the failure mode this change could most easily have had.

`Backend.BOUNDARY_VERSION` moves to 4. A published helper's signature may now contain a function
type, and an older compiler reading a newer jar would not parse it. The check is an exact match, so
the move asks for a rebuild rather than refusing only the jars that use the new form.

Nothing here reaches past Elm or F#. Both write function types in every type position, including a
record's field; Elm refuses them at a port, by a recursive predicate over the type, which is the
boundary rule above. Where Souther's port line falls differs because a Souther `data` derives a codec
by being declared and an Elm record does not, so the field is the line. On equality Souther follows
F#, which refuses the comparison when the type has no equality, rather than Elm, which compiles it
and fails at run time. Currying and user generics stay out (ADR-0010), so this is narrower than
either.

## References

- Specification: `[#delimiters]`, `[#blocks]`, `[#fn-declaration]`, `[#equality]`
- Issue #198 (a function value flows only where the syntax puts it)
- ADR-0025 (first-class functions — amended here), ADR-0004 (derived codecs — generalised here),
  ADR-0009 (value equality), ADR-0010 (no user generics), ADR-0036 (tuples and parameter lists),
  ADR-0039 (Set), ADR-0040 (typed Map keys), ADR-0075 (a module publishes its helpers)
