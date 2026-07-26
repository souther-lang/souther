# ADR-0059: Construction is closed to declared paths, not to the declaring module

Status: Accepted (decided 2026-07-26). Answers issue #121; ADR-0002 is unchanged and this removes a rule that was never part of it.

## Context

Two rules were being applied where the language has one.

ADR-0002 is the one: a value of `T` comes from `T`'s decoder, from a behavior whose `constructs` names `T`, or from generated code — and every one of those paths runs the invariant. That is what "no unvalidated value can be built" rests on, and it says nothing about where the behavior is.

The second rule was that the `constructs` had to be in `T`'s own module. No ADR states it. It came from codegen: the generated checked entry `__construct` is package-private, so a `constructs` naming an imported type compiled and then failed with an `IllegalAccessError`, and issue #113 turned that into a compile error.

Two measurements show it was never the rule the language meant.

Java was already exempt. A module's exposed type has a public `decoder()`, so Java code outside the module originates values of it from raw data, invariant and all:

```
decode(500) -> Ok[billing.Amount@b8]
decode(-1)  -> Err[/: must be non-negative]
```

And closed arithmetic never went through `constructs` at all — re-wrapping is a computation over values that already exist, so `a + a` on an imported newtype compiled with no declaration and failed when it ran (issue #124).

So the second rule bound Souther modules only, and only for the declared path; the undeclared one leaked through as a run-time failure.

## Decision

**The second rule is removed.** A behavior constructs what its `constructs` names, wherever the type was declared. A type its module exposes is built through the same checked entry as any other construction, so the invariant runs; a type a module keeps to itself has no name and no entry outside it, so it cannot be built there.

Concretely: `__construct` is public for an exposed data and package-private otherwise, a construction of another module's type is emitted through it, and arithmetic that would build a type its module does not expose is a compile error instead of a run-time `IllegalAccessError`.

## Why this is safe, and where the safety lives

In the languages Souther takes its module system from, construction is guarded by *visibility*: a private constructor, an opaque type, an abstract signature. Souther guards it by *declaration* — `constructs` is written in the behavior's signature and checked. Borrowing the visibility mechanism on top of the declaration is what produced the second rule, and it added something the language never said.

What the declaration gives that a public constructor would not: each origination is stated where it happens, so the model still reads. What the entry gives: the invariant runs on every path, so opening it cannot produce an unvalidated value.

## Consequences

- A downstream context can state a value in an upstream vocabulary — `constructs billing.Amount` — instead of being pushed into declaring a parallel money type. Whether it *should* is a modelling question the compiler no longer decides for it.
- `a + a` on an imported newtype works, and a subtraction that leaves the invariant aborts exactly as it does at home.
- The E1305 rule for injected behaviors now asks the declaring module: a type of another module is buildable from Java when *that* module exposes it.
- What `constructs` does not say is whether the value is *legitimate* in the upstream concept's terms — an invariant is a predicate on fields, not a rule about which values may come into existence. That was equally true inside the declaring module; the circle of who can be careless widens from one module to those that can name the type, and each such origination is visible in a signature.
- The hint that used to tell an author to "have the declaring module expose a behavior that builds it" is gone with the rule. It pointed at a shape ADR-0005 rules out, since a behavior whose only job is to construct a value is not a domain behavior.

## References

- ADR-0002 (declared paths), ADR-0015 (field reads), ADR-0005 (a behavior is not a getter)
- Issues #121 (the question), #113 (the compile error), #124 (the run-time failure)
- Specification: `[#closed-construction]`, `[#jvm-construction-privacy]`, `[#newtype-arithmetic]`
