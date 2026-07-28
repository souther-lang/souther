# ADR-0068: What a name may be used for does not depend on which module reads it

Status: Accepted

## Context

Souther's `exposing` decides what another module may see. A second set of rules then decided what a visible name may be *used for*, and those rules were not the same on both sides of a module boundary. A `let` body could call a behavior it required and no other; an imported behavior could not be called from a body at all; and the requirement was that the callee have no implementation, so writing any logic in Souther made a behavior uncallable everywhere except as a `>->` stage.

None of that was decided. The body-call rule entered as one of four bullets in the commit that made *required* behaviors callable (`f0fd3ff`, "guards: only required behaviors may be called from a body"), and the cross-module half was never a rule at all — an imported behavior's name was simply absent from the set of names a body could resolve, so it was reported as an arbitrary JVM call (E1401).

The specification said the opposite in two places and contradicted itself in a third. `[#fn-rules]` said "a behavior of another module may be imported and called"; `[#sequential-composition]` told an author to "call it inline in the implementation" when a multi-argument behavior cannot be a stage; and `[#published-modules]` said "a `let` may not call an imported behavior". The first two describe what this ADR decides; the third has been removed.

Elm, F# and Haskell differ in almost every surface detail of their module systems and agree on one thing: an export list controls visibility, and what a name may be used for follows from what the name is, identically inside and outside the declaring module. None of the three can express "exported but not applicable".

## Decision

**What a name may be used for is decided by what it is, and is the same in the module that declares it and in one that imports it.**

For a behavior, the deciding question is the requirement set (`[#requirement-propagation]`), not whether an implementation is written:

- An **empty** requirement set: a `let` body calls it by name. Nothing is injected and nothing is written in `requires`.
- A **non-empty** requirement set — no implementation, or a `let` that declares `requires` — is named in `requires` and called through that name. It arrives bound, as any requirement does.

E1607 changes accordingly: it reports a name that requires nothing (call it instead), a `>->` composition, or a name that is no behavior in scope. The rule it used to state — an implemented behavior is composed, not injected — is retired.

A call is not a stage. It yields the callee's declared output and the caller opens it with `match`; nothing departs on its own. A stage and a call also differ in who owns the behavior: a composition *builds* its stages, so their requirements accumulate into it, while a caller *receives* what it calls, so the callee's own requirements stay with the callee. One behavior may be reached both ways, and which a module writes says which relationship it means.

Two things follow that were not expressible before, and both need a check.

- **Behaviors do not recurse.** A behavior may not reach itself through calls, `requires`, stages, or a mixture (E1608). A `requires` cycle leaves nothing to build first and a call cycle does not terminate. Recursion stays a property of a named module helper, where it is proven total (ADR-0052).
One thing this decision does **not** settle. An exposed name may rest on one that is not: a behavior's input or output type, or a data's field type, may be kept to the module while the name resting on it is published. The generated class is public and states the type anyway, so a reader cannot write it — and a field of such a type is read by generated code that cannot reach it, which is an `IllegalAccessError` rather than a diagnostic. F# refuses that shape at the declaration (`FS0410`, measured on dotnet 10.0.302); Elm allows it because inference means a caller never has to write the type, which is not open to a language that writes its signatures. Adopting F#'s rule is right and is not free: twelve of this compiler's own test fixtures expose a name resting on an unexposed one, so unlike the rest of this decision it carries a migration. It is issue #187's to settle.

## Consequences

The `>->` stage rule is untouched, and so is ADR-0005: the behavior list still equals the spec DSL's, and a helper `let` still cannot be a stage or appear in `exposing`. ADR-0016 is untouched — a requirement is still a constructor argument, and now the argument may be a behavior that has its own implementation. ADR-0017 is untouched: the caller still declares what it requires, and nothing is inferred.

Nothing is added to inference. A behavior's signature is written (ADR-0017), so both sides of a call are declared and typing one is strictly easier than typing a call to a helper, whose parameter types come from its body (ADR-0066). No fixpoint and no unification enter.

Nothing is added to what an edit costs. A call reads the callee's declaration — its signature and whether its requirement set is empty — and never its body, so editing a behavior's body does not re-check the behaviors that call it. `requirementSets` already memoises and already detects cycles through stages; the call and `requires` edges join the same walk.

The invariant rule needed a new reason. It had been justified by the requirement set — a behavior may touch the outside world, so it may not appear in an invariant — and a behavior that requires nothing would now pass that test. The reason is instead that an invariant is part of what a type is and travels to an importing module as source, together with the helper `let`s it names, so it may name only what travels with it. No behavior is callable from an invariant, whatever it requires.

Prior art is the reason this is a correction rather than a design. Elm exposes values and types in one list and every exposed value is applicable; Haskell's export list is the same and adds re-export; F# controls accessibility with modifiers and signature files. Souther sits with them on what this decision settles, and apart from F# on one thing it does not (below).

## Where Souther sits

| | Souther | Elm | F# | Haskell |
| --- | --- | --- | --- | --- |
| Module per file | one | one | one (`module`/`namespace`) | one |
| Export list | `exposing (…)` | `exposing (…)` | accessibility modifiers, `.fsi` | `module M (…) where` |
| A visible name is usable at its kind | yes | yes | yes | yes |
| Export a function | as a `behavior` | yes | yes | yes |
| Export a helper (`let`) | **no** | — | — | — |
| Import form | `import M ( … )` | `import M exposing (…)` | `open M` | `import M (…)` |
| Wildcard import | **no** | `exposing (..)` | `open` is one | default |
| Qualified access without an import line | **yes** | no | yes | no |
| Re-export | no | no | via type alias | `module N` in the list |
| Cyclic imports | no | no | no (across files) | `hs-boot` only |
| Hiding a type's construction | `constructs` on the builder | leave constructors out of `exposing` | `private` constructor / `.fsi` | leave constructors out of the list |
| Public signature on an unexposed type | allowed (issue #187) | allowed (inference) | `FS0410` | allowed (inference) |
| A sum over cases from another module | **no (E1606)** | yes | yes | yes |
| Two same-named imports, told apart by qualifier | types yes, **behaviors no** | yes | yes | yes |
| Effects/dependencies in the signature | `requires` | none (pure) | none | effect in the type |

Bold marks where Souther is alone. Four of those five are the surface someone coming from the three would notice, and each has a reason of its own:

- **No helper export.** `exposing` lists what the spec DSL has (ADR-0005), and a helper is not in it. A pure function meant to be shared is written as a behavior, which — after this decision — is applied like any other function. The keyword differs; the capability does not.
- **Qualified access with no import.** The standard library already worked this way, and ADR-0058 extended it rather than adding a second rule. Closer to F# than to Elm, and strictly more permissive than both — it removes an error rather than adding one.
- **No sum over imported cases (E1606).** The only one of the five with no design content: a case class carries the interfaces it implements, decided when its own module is generated, so a union declared elsewhere cannot enrol it (ADR-0057, measured against `ClassCastException`).
- **Behaviors that cannot be told apart by qualifier.** A behavior name is also a field name in the class that injects it, so qualifying does not separate the fields.

The first is a consequence of what `exposing` is for; the second widens what is legal; the last two are the JVM showing through, and the specification names them as such rather than as module-system principles. What is *not* on the list any more is a name that is visible and not applicable, which none of the three can express and Souther no longer does either.

## References

- Specification: `[#modules]`, `[#requires]`, `[#calling-a-behavior]`, `[#requirement-propagation]`, `[#e1607]`, `[#e1608]`
- Issue #159, issue #187
- ADR-0005, ADR-0016, ADR-0017, ADR-0052, ADR-0058
