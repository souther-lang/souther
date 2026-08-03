# ADR-0092: A non-recursive helper carries the type variables its body leaves open

Status: Accepted. Amends ADR-0066.

## Context

ADR-0066 decided that a helper's parameter types come from the helper, and it named the case this
amends:

> A parameter the body leaves open MUST be annotated. A type variable is written only in core and
> call sites are not read, so no type is left for it to be given […] one whose container is named but
> whose element nothing settles (`let count (xs) = List.length(xs)`).

That reading is right about the two rules and wrong about what follows from them. Souther's types are
already polymorphic where core's are: a core signature's `'a` is implicitly universally quantified,
and a non-recursive core helper carrying one is monomorphized by inline expansion at each call site
(`[#stdlib]`). `let isEmpty (xs: List<'a>) = List.length(xs) == 0` is not compiled to a polymorphic
method — it is expanded at each call with `'a` resolved to that call's concrete type. A non-recursive
user helper travels the same way: its settled types are written back onto its parameters and its body
is expanded per call, and a published one crosses and is expanded at the reader's call sites
(ADR-0075). So the machinery an internally polymorphic user helper needs is the machinery already
running for every helper. What was missing was permission.

The asymmetry this removes is one sentence wide: for a non-recursive helper whose body decides what a
value *is* and leaves open what it *holds*, core could keep the unsolved variable and a user module
could not. Nothing else moves. A user module still cannot write `'a`; a recursive helper still writes
all of its types; `data` and `behavior` still take no type parameters.

ADR-0028 confined generics and recursion to core together, and wrote "User modules remain bounded —
no generics, no recursion, no intrinsic." ADR-0038 returned the recursion half after finding the
factual claim under it was wrong. This is the same move on the generics half, and ADR-0028's own
consequences already say only that half is left standing.

ADR-0010 is not reopened, but what it decides has to be said more narrowly than "no user-defined
generics", because that phrase mixes what an author writes with what the language means. A helper an
author defined is now usable at two element types in one module, which is limited parametric
polymorphism over a user-written definition however it is compiled; inline expansion is an
implementation of it, not a reason it is not one. What ADR-0010 decides, stated as four things and all
still true: no user-written type parameters, no generic `data`, no generic `behavior`, and no
polymorphic values. What is added is the fourth thing it never asked about — that a non-recursive
helper is generalised by the compiler over what its body left open, and instantiated at each
expansion. Its vocabulary argument runs through
ADR-0001's correspondence with the spec DSL, and a helper does not appear in the spec DSL at all
(ADR-0075), so that argument does not reach one.

ADR-0086 is not amended either. It declined let-polymorphism — a binding that generalises without
being expanded — and recorded that `let r = List.reverse` applied to a `List<Int>` and a
`List<String>` already compiles, because a name bound to a declaration *is* the declaration, expanded
at each use. A helper is expanded at each use for the same reason. What is not gained here is a
polymorphic value: what travels is the declaration.

### What was measured

Of the 240 helper `let`s in the bundled prelude and every module of souther-lang/examples, every one
that takes a collection names its element with a business type. Not one is element-agnostic. So this
is not a restriction the model was pressing against; it is one that costs the language an explanation
it cannot give — that the type system has polymorphism the surface can only use from inside core.

Two things the issue raised turned out not to arise. Hover renders the definition's own source line
and never a `Type`, so a carried variable reaches no editor surface. And a published helper crosses
as the source its author wrote, which carries no annotation at all, so the reader settles it again by
the same rule and no type variable is written into any published text.

## Decision

A non-recursive helper may retain the type variables that remain inside a body-determined outer type
constructor. Those variables are scoped to the helper definition and instantiated independently at
each expansion. A bare unconstrained variable is not a body-determined parameter type.

- **What counts as determined.** The outermost layer of the type denotes a concrete type constructor,
  and nothing inside it answers no value. `List<'a>` says the value is a list; `'a` says nothing.
  The rule is stated over what a type is, not over a list of the constructors there are, so a
  constructor added later means what this already says of it. It is asked of the outermost layer,
  which is also where a function type is refused: what must be written is a parameter that is
  *applied*, and a collection of functions is a value the expansion carries like any other
  (`let forwarded (fs) = countFns(fs)` takes the `List<(Int) -> Int>` its callee declares, as it did
  before this). A type that answers no value is refused at any depth, which is the existing rule about
  the bottom an empty collection carries.
- **A stated answer always wins.** The walk records an answer that leaves something open and keeps
  going; it takes it only where nothing states the whole type. Two open answers about one parameter
  are merged rather than the first winning — they are two readings of one value — and two that
  disagree about what the value is leave the parameter as open as it was. Taking them together is
  unification, done locally and symmetrically — variables settled to types and to each other,
  constructors taken apart, a variable refused a type it stands inside, and what was settled
  substituted through once every reading is in. What it is not is the unification a call is typed
  with, which checks an argument against a declared parameter in that direction and hands its
  bindings to the rest of the call: nothing settled here reaches past the parameter.
- **What the body gets wrong is not decided here.** A parameter whose outer type the body stated is
  that type, and a body that disagrees with it is reported by the standalone check that follows, at
  the position of the disagreement — which is what ADR-0066 already says happens to a settled type the
  rest of the body will not take. A mistake standing beside an open element is reported as the mistake
  it is: `let bad (xs, s: String) = List.length(xs) + (s * 2)` names the arithmetic, not `xs`.
- **The variables are the helper's own, and a variable carries where it came from.** A library
  signature is resolved once and shared by every call site, so two unrelated calls hand back one
  spelling — `List.length` and `Set.size` both wrote `'a`. Variables are therefore minted where a
  declaration is read, from the variables that declaration wrote and that call did not solve, and a
  minted variable names the parameter it was minted for. That origin is what the rules ask, rather
  than the spelling: a variable the core wrote is attached to nothing, one minted for the parameter
  being settled is what is being worked out, and one minted for another parameter says this one holds
  whatever that one holds. What links two parameters is a position that reads them together, not a
  spelling two libraries share.
- **Two readings hold what a variable stands for while they are read, in both directions.** A
  variable says one thing everywhere it appears, so `('a, 'a)` read against `(Int, String)` is two
  answers rather than one left open. Holding one direction only would make the answer depend on which
  reading was found first, and the two readings are of one value — neither is the one being checked.
- **A recursive helper is unchanged.** It is lowered to a method and has no expansion to monomorphize,
  so it writes all of its parameter types and its return type.
- **`exposing` is unchanged.** A published helper crosses as its own source and the reader settles it,
  so a helper whose element is open is published like any other and no rule is added for it.
- **A fixture cannot be built against one.** An `example` row that applies such a helper is refused,
  because a call settles the element from the argument it is given and a fixture is built before there
  is a call to settle it. This is an ordering, and the report says so.

## Consequences

`let count (xs) = List.length(xs)` compiles, and `count([1, 2])` and `count(["a"])` both work in one
module. That is the visible change, and it is the same thing a name bound to a core function already
did.

The vocabulary cost is real and is not hidden here. `let ids (xs) = List.length(xs)` written by an
author who meant `List<CustomerId>` now compiles, where before the annotation was demanded and the
business type got written down. That is a loss against ADR-0017's "declare, don't infer" and against
the vocabulary argument of ADR-0010, paid for the consistency above.

What a helper is remains what it was. It is a declaration expanded at each use, not a value of a
polymorphic type: handing one to a combinator by name expands it there, and binding one to a name
crosses into what ADR-0086 answers, where each use instantiates the declaration afresh.

`check.helper.infer` splits in two. What is left annotated is a parameter read only through a field
and a parameter the body says nothing at all about, and those are refused for different reasons —
reaching a type from a field is a structural question a nominal model does not ask (ADR-0012), so no
amount of further body will settle it, where a body that says nothing might have said something. An
author told only to annotate could not tell which they had.

Two questions the inliner asks of a declared type — does it carry a collection, does it hold a type
variable — were read off the spelling. They are asked of what the reference denotes now (ADR-0067),
which is what everything downstream of `Resolve` already does. This is a tidy-up rather than a fix:
both are only ever asked of an author-written return type, which `Resolve` always resolves, so the
spelling and the denotation agreed at every reachable call. It is here because a settled type carries
no spelling at all, so the day either question is asked of one, the spelling would answer no about it.

A minted variable is shown as `_` rather than by the name it was minted under. The name is not one an
author wrote or could write, so its spelling says nothing to a reader, while what is open about the
type is what they need to see.

A fixture that could monomorphize itself from the row's own argument type is the honest end state for
the `example` case, and it is not this change: it needs the row's argument typed before the helper's
signature is instantiated, which the fixture builder does not do today.

Collecting an open answer costs a walk that no longer stops at the first position that names a type,
for the helpers that reach one. Measured over the bundled corpus, compiling `crm` and `issuetracker`
is unchanged within noise.

## References

- Specification: `[#fn-rules]`, `[#stdlib]`, `[#type-variables]`
- Issue #303 (a helper whose body fixes only the container), issue #302 (a parameter settled by
  reading one position)
- ADR-0066 (amended), ADR-0010 (polymorphism is limited to stdlib types), ADR-0028 (generics live in
  a privileged core), ADR-0038 (recursion returned to user helpers), ADR-0075 (a module publishes its
  helpers), ADR-0086 (a function name is a value), ADR-0012 (nominal types), ADR-0017 (declare, don't
  infer), ADR-0067 (a name denotes a binding)
