# ADR-0075: A module publishes its helpers

Status: Accepted. Refines ADR-0005, revises ADR-0074.

## Context

ADR-0074 published a module's values and left publishing a *helper* — a `let` with parameters — open, naming three things it would bring with it: construction authority, an executable body under a compatibility contract, and a reader assembling calculation without going through a behavior. This decides those.

Without it, a module that wants another's pure calculation either restates it or declares it a behavior. Declaring it a behavior puts something in the behavior list that the specification does not name, and ADR-0005 keeps that list one-to-one with the spec DSL's. Restating it is the duplication issue #163 removed for values and left in place for rules.

## Decision

**`exposing` may name a helper.** A helper is one of a module's definitions, and what `exposing` lists is what the module offers. The `>->` restriction stays: a helper does not appear in the spec DSL, so it is not a stage.

**A published helper crosses closed**, as a published value does (ADR-0074): its body with its own module's values and non-recursive helpers already substituted into it, expanded at the reader's call sites. A value and a helper are told apart by the predicate that decides it everywhere — a written parameter list — and a behavior's own `let` is neither, whatever its shape.

**A recursive helper travels with the body that calls it.** Closing cannot remove one: it is lowered to a method (ADR-0038), so the call stays a call. It comes along under the name of the module that declares it, and so does every recursive helper it reaches in turn — a mutually-recursive group arrives whole, and one the reader never imported arrives because the body it did import calls it. The importing module emits them as methods on its own `$Fns`, which is what it already does for a recursive standard-library helper it reaches.

The declaring module is the helper's *identity*, not where its method goes. `$Fns` stays package-private in every module, so publishing a helper opens no Java-reachable entry to a construction — what ADR-0002 gives up is not given up. Two modules may declare a recursive helper of one name and one importer may emit both; they are two methods, named apart, because a bare name could not tell them apart.

The alternatives are the ones issue #197 lists, and each fails on the same point: making `$Fns` public opens the Java entry, nestmates need a shared nest host that a different-package importer cannot join, publishing only helpers that construct nothing decides publishability from the body rather than the signature, and a Java-boundary wrapper is one more path to keep agreeing with the others.

**What a published body builds is not the reader's to declare.** Expansion makes a carried construction look like the reader's own, and the permission check would ask the reader for `constructs` on a type the declaring module may keep to itself — a name the reader has none of. Publishing the definition is what states that origination. A construction therefore records the module whose published body carried it, and the check reads that rather than the shape.

It is preservation, not a grant. What the mark covers is a type of the module that published the body; a type of some *third* module the body happened to build is neither the reader's nor the publisher's to hand over, so it stays the reader's to declare — which it can, because the module declaring it exposed it (ADR-0059). Declaring a carried construction anyway is not called building nothing.

**A published helper's argument and return types are part of the exposed surface.** A reader writes the arguments, so it must be able to name their types; those are settled from the body (ADR-0066) and read as settled. What the body reaches for on the way is still not asked, as for a value.

**ADR-0074's refusal of a published value that reaches a recursive helper is withdrawn.** That rule refused what this ADR now carries, and it was not a corner: `let total = Amount(List.fold(...))` reaches `List.foldFrom` and could not be published. The surface rule keeps its reach through such a helper by reading the return type the helper is required to declare — a recursive helper is not expanded, so a construction inside it was never what the rule read.

**The body a jar carries is under the boundary version.** A published body travels as source and is compiled by whoever imports it, so what the front end makes of it is part of what a compiled module promises. `Backend.BOUNDARY_VERSION` covers it, and moves for a change to how a carried body is read as surely as for a change to a descriptor — the difference being that such a change is the front end's rather than codegen's. `PublishedModule` already refuses a jar that disagrees, so the disagreement is reported as one.

## Consequences

Issue #197 closes. A rule is written once. `exposing` is no longer a list of behaviors plus a few values: it is what the module offers, and this is the last of ADR-0005's sentence about it to be refined.

The operation boundary thins, and nothing here prevents that. A reader may now assemble calculation out of published helpers without going through a behavior, so a module has two kinds of published API: behaviors, which are the business operations the specification names, and helpers, which are shared calculation. That a helper cannot be a `>->` stage is a fact about the spec DSL and not a mechanism — a published helper API can become the de facto business API, and no check will say so. This is accepted as the price of publishing, not overlooked: the alternative is the restatement issue #197 was raised about.

Duplication moves rather than disappearing. A non-recursive helper was already copied into each caller by expansion; a recursive one is now copied into each importing module. What is not duplicated is the decision about what the rule says, which is the point.

## References

- Specification: `[#exposed-values]`, `[#exposed-surface]`, `[#fn-rules]`, `[#published-modules]`
- Issue #197 (a module cannot publish a helper), issue #163 (a fixture cannot be named)
- ADR-0074 (a value is part of a module's published surface — revised here), ADR-0072 (a `let` with no parameter list is a value), ADR-0005 (a helper is not a behavior), ADR-0038 (a recursive helper is a method), ADR-0059 (construction is closed to declared paths, not to the declaring module), ADR-0066 (a helper is typed by its body), ADR-0067 (a name is resolved once), ADR-0002 (construction is declared)
