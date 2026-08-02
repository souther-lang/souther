# ADR-0087: A rounding mode is an ordinary value of a core-declared data

Status: Accepted. Supersedes the rounding-mode entry under "what is still refused" in ADR-0086,
and the "this argument is a rounding mode" side condition it kept in the compiler.

## Context

Issue #270. `RoundingMode` was the last argument in Souther that was not a value. It was written
at the call and read as the identifier it was written as, never evaluated, so three Decimal
operations were special forms rather than functions: a model could not state a rounding policy
once and pass it, could not choose one from a business rule, and could not hand the operation to a
combinator — three restrictions with one cause. It was also the only exception left in ADR-0086's
rule that a declared function is a value.

The machinery enforcing it was spread over the checker (`requireRoundingMode`, an argument-typing
skip, a resolution ladder rung for the seven names, a refusal of η-expansion), the IR (a typeless
`Core.Builtin` node), and the backend (a `getstatic` of the `java.math.RoundingMode` constant
spelled like the identifier).

## Decision

**Rounding mode arguments are ordinary evaluated values of the core-declared `RoundingMode` data
type. The compiler does not recognize rounding-mode case names or inspect their syntax at call
sites.**

```sou
// souther/decimal.sou
data RoundingMode = HALF_UP | HALF_EVEN | HALF_DOWN | UP | DOWN | CEILING | FLOOR
```

- A prelude module resolves against its own declarations, through the same two-phase name
  collection every module gets (`Symbols.of`), so a core signature may name a data the module
  declares. `Symbols.none()` remains only for sources with no declarations.
- **Runtime-backed data.** The declaration is the checker's source of truth; the JVM
  implementation is provided by hand in souther-runtime rather than generated. The classification
  is a single registration in `Prelude` — declaration in `decimal.sou`, implementation
  `souther.runtime.RoundingMode`, generated: no — and everything follows from it: the declared
  names anchor to the runtime namespace (where `DivisionByZero` and `NotANumber` already live),
  `Symbols` answers lookups for them from the registration, and, because the declarations belong
  to no compiled module, they never enter derivation or code generation. No other place in the
  compiler may branch on the type's name; a name-based conditional appearing outside the
  registration is this decision failing.
- **The implementation mirrors the generated shape.** Registering the declaration makes
  `RoundingMode` the first runtime-backed enumeration (`isUnitOnlySum` is true), so the emitter
  calls `__tag` / `__order` / `__ordering` on it and reads `INSTANCE` off its cases exactly as it
  does on a generated sum. The handwritten classes are empty records carrying that shape, and a
  pairwise test (`RoundingModeAbiTest`) compares every observable — the static methods, equality,
  hash, text form — against a generated enumeration, so a change to either side that the other
  does not follow fails a test rather than surfacing as a linkage error.
- **No codec, intentionally.** `RoundingMode` is ordinary data for typing, evaluation, composition
  and ordering, but it does not provide a codec and therefore cannot appear where a codec is
  required — a field of another data, an example fixture. A rounding policy is a computation's
  input, not a value that crosses a serialization boundary. The refusal is the ordinary
  missing-codec diagnostic, and tests pin both surfaces so the type never quietly gains an
  external representation.

  The absence follows from where the declaration lives, and it is worth being exact about why,
  because the obvious reading is wrong: an ordinary enumeration receives a default codec *through
  derivation even when it writes no `decoder`/`encoder` clause* — `Deriver.deriveSum` supplies one
  — so writing no clause would not keep a codec away. What keeps it away is that a runtime-backed
  declaration belongs to no compiled module and therefore never enters derivation at all. The
  consequence is that "no codec" cannot be arranged by omitting a clause from a module's own data,
  and that routing a runtime-backed declaration through derivation would both produce a codec and
  emit calls to codec factories on handwritten classes that have none.
- **Shadowing follows the unit-data rules.** Rounding-mode cases are ordinary unit data; a binding
  may take a case's name and the local takes precedence. Shadowed cases have no qualified escape
  syntax — the same is true of every unit data, and this change does not add one.
- The `java.math.RoundingMode` mapping is one `switch` in `DecimalMath`, on the Decimal runtime
  rather than on the value: `java.math` is that backend's implementation detail, not part of what
  a rounding mode is.

## Consequences

The checker's side condition is gone: `requireRoundingMode`, the argument-typing skip, the
resolution rung, the η-expansion refusal, the built-in-shadow rule for the seven names, and the
type-name fallback are all deleted, and `Core.Builtin` is deleted from the IR — nothing produced
it any more. The three operations type against their declared signatures like every other
function; a wrong argument is an ordinary type mismatch, and an applied case (`HALF_UP(x)`) is the
ordinary answer for a type written where a call goes.

The two kernels' JVM descriptors derive from the declaration (`Prelude.kernelSignature`, the
boundary form of each declared type), so the signature exists once. Deriving a descriptor from
the observed argument types only ever agreed with the declaration while every parameter type was
invariant; a sum-typed parameter ends that — an argument's type may be the case it happens to be
while the declaration names the sum — so the descriptor comes from the callee.

The other 61 kernels that build a descriptor from the call were audited against that invariant and
none breaks it, but the reason is worth recording because it is not a rule anyone stated: every
other declared parameter is a primitive or a container, whose boundary form the type settles on
its own, or a type variable in a slot the emitter erases to `Object` — which is what the
declaration would have given. So the agreement is a property of the declarations that exist, not
of the mechanism, and registering a second runtime-backed data and writing it into a kernel's
parameters reproduces #270 exactly. `KernelDescriptorsComeFromDeclarationsTest` turns that into a
checked invariant: a kernel reading its descriptor off the call may not declare a parameter whose
boundary form depends on which value arrives. It was verified to fail by putting `decimal.toInt`
back on the observed-type emitter.

Generalising the declaration-read descriptor to the rest is a separate design problem, not left
undone by oversight: an emitter reading the declaration must still answer the call's Souther type,
and for a polymorphic kernel those are two different sources (the declaration says `List<'a>`, the
caller needs the element it actually holds). Ten kernels also permute their arguments and nine
erase a slot and box it, neither of which the declaration states. Until those are separated, a
mechanical migration would move type variables into places that expect settled types.

`constructs` does not govern a rounding-mode case, stated as the general rule rather than a
namespace check: the discipline governs what the compilation declares
(`Symbols.declaredByCompilation`), and a declaration the language gives is vocabulary — as
`None` is.

The reserved namespace's qualifier list moved to a dependency-free constant (`Reserved`). The
frontend read it off `Prelude`, whose loading parses prelude sources back through the frontend;
that cycle was latent while no prelude source declared data, and the first `data` in one closed
it. A fact of the language now sits where both sides read it without initializing each other.

A mode is evaluated at the call like any argument: bound to a name, chosen by an `if`, computed by
a helper, or fixed by the function value `Decimal.toInt` evaluates to — each pinned by a test
through a different one of the three operations.

Generation of runtime implementations from prelude declarations was considered and deferred: with
one runtime-backed data, a generator is more mechanism than the ABI test it would replace. The
registration records the classification either way, so a second runtime-backed data is the point
to revisit, not to re-decide.

## References

- Issue #270; ADR-0086 (a function name is a value — this removes its last exception),
  ADR-0053 (the declaration is the single source of truth for a signature)
- Specification: `[#stdlib-decimal]`, `[#stdlib]`, `[#unit-data]`, `[#intrinsics]`
