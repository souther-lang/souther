# ADR-0015: Field reads may cross module boundaries; only construction is closed

Status: Accepted

## Context

Souther closes data construction paths (ADR-0002) so that no unvalidated value can be built. A separate question is whether *reading* a field must be equally restricted. If reading were closed too, passing a value across a module boundary would require a getter-only behavior for every field.

## Decision

Reading a field is possible wherever the data's type is visible: within a module, any data; across modules, any exposed data (exposed means importable, and all of its fields are readable — there is no per-field exposure). A behavior may read the fields of its input data even when that data comes from another module. What is constrained is construction, not reading.

## Consequences

Reading a field cannot break an invariant; only construction can, and construction is limited to the paths of ADR-0002. So allowing cross-boundary reads does not weaken the "no unvalidated value" guarantee — reading and constructing are separate permissions. No getter-only behavior is needed to pass a value outward: such a getter would not appear in the spec DSL, so it could not be a behavior at all (ADR-0005).

A field of an exposed data may itself be of a type its module keeps to itself, so a value whose type is *not* visible arrives in a module all the same. The decision above is about the data whose field is being read, and that data has to be visible, so such a value arrives whole and is not readable here: it may be bound, put in a field of this module's own data, and handed to a behavior of the module that declares its type. Reading a field of it is a compile error, as arithmetic on it already was (ADR-0059). That is what the generated classes do — the class is package-private, so its accessors are out of reach — and until issue #187 the compiler emitted the read anyway, which failed with `IllegalAccessError` when it ran.

The line is *opening* the value, not touching it, and comparison falls on both sides of that line. A single-value newtype is compared by the value it wraps (ADR-0047), following the chain to the base, so the comparison names each class on the way down: comparing one whose module keeps it to itself is refused, and so is comparing an exposed newtype that wraps one which is not. Everything else is compared by the module that declares it — a data by its fields, a collection by its elements — which emits `Objects.equals` and names no class, so it compares wherever the value arrives and this module still never sees inside. Measured both ways: `List<Hidden> == List<Hidden>` and a hidden `data`'s comparison compile and run correctly on the JVM, while a hidden newtype's comparison and ordering failed with `IllegalAccessError`.

Elm and Haskell settle both halves the same way: a value of an unexported type passes through a module that cannot name it, its derived `Eq`/`Ord` come along with it (`orderBy a < orderBy b` compiles on GHC 9.6 with `UserId` unexported), and the read that would open it is refused where it is written (`Not in scope: data constructor`, Elm's `NAMING ERROR`). javac draws the line in the same place — holding a package-private-typed value across packages compiles and runs, and calling a method on it does not. F# takes the other route and refuses the signature at the declaration (`FS0410`), which it can afford because `type T = private T of string` exposes the name while keeping the representation private; `exposing` works at type granularity and an exposed data has all fields readable, so requiring the name here would publish the fields with it.

On the JVM, exposed data get public read accessors, because module = package and a package-private field cannot be read across the boundary. Constructors stay non-public, so nothing reaches the fields without the invariant: building one goes through the decoder or through the checked entry, which an exposed data publishes (`[#jvm-construction-privacy]`). Reading a field from Java is the same exposure the encoder already gives by emitting every field as JSON; what is protected is the invariant, not the act of building.

## References

- Specification: `[#field-visibility]`, `[#jvm-product]`, `[#jvm-construction-privacy]`, `[#newtype-arithmetic]`
- ADR-0059 (construction is closed to declared paths), issue #187 (the read that was emitted anyway)
