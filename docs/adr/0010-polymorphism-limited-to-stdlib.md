# ADR-0010: Polymorphism is limited to stdlib types; no user-defined generics

Status: Accepted. Amended by ADR-0028 (decided and implemented 2026-07-18): the user-facing
restriction stands, but the stdlib generics move from compiler machinery into a privileged
`core` written in Souther. Narrowed by ADR-0092 (2026-08-03): "no user-defined generics" below reads
as four things — no user-written type parameters, no generic `data`, no generic `behavior`, no
polymorphic values — all of which stand. What it does not decide is the type inference gives a `let`,
and a non-recursive helper is now generalised by the compiler over what its body left open.

## Context

A business model is written in concrete business vocabulary. The question is whether the language should also let users introduce their own type parameters, as most statically-typed languages do.

## Decision

The only polymorphic types are the stdlib ones — `Option`, `List`, `Map`. Neither `data` nor `behavior` takes type parameters; there are no user-defined generics.

## Consequences

Because business models are written in concrete business vocabulary, an abstract type parameter is never needed. Introducing one would pull the model away from the one-to-one correspondence with the spec DSL (see ADR-0001), which has no generics. The stdlib types that are polymorphic are provided by the runtime, not written by the user, so the absence of user generics does not cost the model any expressiveness it would otherwise use.

## References

- Specification: `[#algebraic-types]`
- ADR-0001 (one-to-one with the spec DSL)
