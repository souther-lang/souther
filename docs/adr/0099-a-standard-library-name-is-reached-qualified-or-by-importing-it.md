# ADR-0099: A standard-library name is reached qualified or by importing it

Status: Accepted (implemented 2026-07-18, recorded 2026-08-07). Supersedes the auto-import half of
ADR-0028.

## Context

ADR-0028 gave the standard library a reserved namespace the compiler ships, and said that namespace
is auto-imported: `map`, `length` and `trim` resolved bare in every module, with nothing written to
bring them in. That was the one place in Souther where a name appeared undeclared. Everywhere else
the language refuses to deliver a name implicitly — there are no wildcard imports, and an import
line lists the names it brings.

The rule was reversed on 2026-07-18, following Elm and ML: the library is reached through the short
qualifier its module is published under, or by importing the names a module writes bare. The same
change dissolved the overloaded primitives into per-module names, which the qualifier is what tells
apart — `String.length` and `List.length` are two functions, and a bare `length` was one name for
both.

That reversal was implemented, migrated across the examples and the specification, and never
recorded. ADR-0028 kept saying the namespace is auto-imported, and so did a comment in `bool.sou`,
a Javadoc in the inliner, and the names of two tests. `souther api --source` prints a library
module's own source, comments included, and `souther doc cli/start-here` sends a reader there to
find out why a function is shaped the way it is — so the comment in `bool.sou` was published
documentation stating a rule the compiler had refused for three weeks. A reader who trusted it wrote
`not(x)` and was told to write `Bool.not(x)` (issue #374).

The decision itself was sound and is not in question here. What was missing is the record: with no
ADR to point at, nothing said that the sentences describing the old rule were now describing
nothing, and the specification being right did not help a reader who was sent to a source comment.

## Decision

**A standard-library name is reached through its module's qualifier, or by importing the name into
the module that writes it bare. Nothing is delivered implicitly.**

The qualified form always works and needs no import: `List.map(f, xs)`, `Bool.not(b)`. Which module
a name comes from is written where the name is written.

An import elides the qualifier and does nothing else. `import Bool ( not )` lets a module write
`not(b)`; it does not change what the name means, and a module may always write `Bool.not(b)`
instead. There is no wildcard import, so the names an import brings in are the names it lists.

An import beside a declaration of that name is a conflict, refused on the import line, and not a
shadowing. One spelling standing for two things has to be chosen between, and nothing at the call
site could do the choosing. A module's own `not` and the library's `Bool.not` are two spellings and
may be written in one body; it is `import Bool ( not )` beside `let not` that is refused.

A bare name the library publishes and the module did not import is reported as what it is — a
library function, reached either way — and the report names every module that publishes it. A bare
`insert` could be `Map.insert` or `Set.insert`, and offering one of them says the other does not
exist.

What stays bare is what no module publishes: operators, `if` and `match`, literals, a module's own
declarations, and the names the language itself gives.

This settles what a module can see. How a name that is visible is then resolved — that a binding in
force wins, and that the question is asked once — is ADR-0067's, and is unchanged.

The reserved namespace keeps every privilege ADR-0028 gave it: generics, recursion, `intrinsic`,
`private`, and a user module's inability to name itself under `souther`. Only the delivery of its
names changes.

## Consequences

The rule now has one statement in the specification and one executable statement in the compiler's
tests, and the places that had described it in passing no longer describe it at all. A source
comment in a library module says why that declaration is shaped the way it is — why `not` is written
in Souther rather than as a primitive, why it needs no class — and says nothing about how a caller
reaches it, because that is a rule about every library name and not a fact about this one.

The report for a bare library name is derived from the published surface rather than from a table
written beside it. That table had gone stale in four places while nobody was looking: `insert`,
`remove`, `append` and `addDays` are each published by two modules and the table named one, so a
reader reaching for `Set.insert` was told about `Map.insert` and left to conclude the set had no
such operation. Deriving it also removes the hand-written English that was being passed to a
localized message, which is why the candidates are now a list the catalog puts in a sentence.

The order that list is offered in, the order the prelude sources load in, and the qualifiers that
exist are one declaration in `Reserved` rather than three that had to agree.

An ADR recorded three weeks after the fact is worth less than one recorded with the change, and the
status line says so rather than presenting this as having been there all along. The failure this
records is not that the wrong rule was chosen; it is that a decision was implemented with no record,
and the prose describing the rule it replaced outlived it in four places.

## References

- Specification: `[#stdlib]`, `[#imports]`, `[#reserved-namespace]`
- ADR-0028 (the reserved namespace and its privileges — the auto-import half is superseded here)
- ADR-0067 (a name is resolved once — what a visible name means, where this says what is visible)
- ADR-0010 (no user generics — why the library needs a namespace of its own at all)
