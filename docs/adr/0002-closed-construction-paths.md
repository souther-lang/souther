# ADR-0002: Close data construction paths; permission lives on the behavior

Status: Accepted

## Context

The spec DSL states, via parse-don't-validate, that "a validated email address is guaranteed to be validated by its type." For that guarantee to hold in the implementation, it must be impossible to produce a value of an invariant-bearing `data` without going through validation. Merely writing `T` as a return type must not be enough to mint a `T`.

## Decision

A value of `data T` can be produced only by: `T`'s derived decoder, the implementation (Souther `let` or injected Java) of a behavior whose construction set includes T, or compiler-generated code. The authority to construct is held by the *behavior*, not by its implementation. That set is written with `constructs` on the behavior; on an let-backed behavior it may be omitted and inferred from the visible body, while an injected behavior must declare it (no body to infer from, and it drives factory generation — ADR-0006, `[#java-base-class]`).

## Why this is not a per-type choice

The ML family makes opacity a decision the author writes per type. Elm's `exposing` distinguishes the
type from its constructors — `module Dict exposing ( Dict, ... )` hides them, `module Maybe exposing
( Maybe(..), ... )` shows them. F# and OCaml put the same choice in a separate signature (`.fsi` /
`.mli`), where a discriminated union or record "must expose either all or none of their fields and
constructors". In all three, a module may choose to hand out a raw constructor.

Souther does not offer that choice, and the reason is the invariant. None of those languages attaches
one to a type, so exposing a constructor there costs nothing but encapsulation. Here a constructor is
the one place an invariant is checked, so a type that hands one out is a type whose invariant is
advisory — and "a validated email address is guaranteed to be validated by its type" stops holding
for the whole language, not just for that type.

What F# programmers write by convention for exactly this reason — `type X = private ...` with a smart
constructor returning a `Result` — is what Souther makes the only way. The guarantee is the same one;
what changes is that it is not opt-in.

Note what this decision does *not* say: nothing here restricts construction to the module that
declares the type. A behavior in any module that declares `constructs T` is a declared path by this
ADR. The compiler currently rejects that when `T` is imported, for a reason that lives in codegen
rather than here (issue #121).

## Consequences

Permission is always on the behavior's declaration. A helper `let` (one with no corresponding behavior) may also construct data, but it does not declare `constructs` itself — its construction set is inferred transitively and must be contained in the `constructs` of the behavior that calls it (otherwise E1002). Blocks work the same way, constructing under the enclosing behavior's authority. So refactoring an anonymous block out into a named helper `let` never changes whether a construction is allowed.

`constructs` is **not** what guards the invariant — `__construct` and the decoder do that, and both check on every construction path (see ADR-0003). Deleting `constructs` would not let anyone build an unvalidated `検証済みメールアドレス`. What `constructs` buys is *model reading*: from the declaration alone you can tell whether a behavior **mints** a new value or merely **passes through** one it was given, which the output type cannot tell you. But that is a reading aid, not a dependency. Unlike `requires`, a construction permission is invisible to callers — whether a behavior mints Member or passes it through, the caller calls it identically — so inferring it changes no outward contract (the failure mode that makes `requires` worth declaring, ADR-0017, does not arise here). So on an let-backed behavior, whose body is visible, `constructs` is **optional** — the optional-inferred rule and its exact checks belong to ADR-0017 and are not restated here. It lives on `behavior` because "this behavior produces a new 事前承認済み" is a statement of the spec (exactly what the DSL's state transition says) for whoever chooses to write it.

The guarantee is "no *unvalidated* value can be built," not "no value can be built." Factories for unit cases are handed out to injected Java implementations for convenience, and unit data have their decoders public (a unit decodes by ignoring input), so anyone can build a unit value — but a unit data has nothing to validate. Invariant-bearing data are what closed construction actually protects: however they are built, they are checked.

## References

- Specification: `[#closed-construction]`, `[#constructs]`, `[#java-base-class]`
- Prior art: Elm `exposing (Dict)` vs `exposing (Maybe(..))` (elm/core), F# signature files and
  `type X = private ...`, OCaml `.mli` abstract types
