# ADR-0015: Field reads may cross module boundaries; only construction is closed

Status: Accepted

## Context

Souther closes data construction paths (ADR-0002) so that no unvalidated value can be built. A separate question is whether *reading* a field must be equally restricted. If reading were closed too, passing a value across a module boundary would require a getter-only behavior for every field.

## Decision

Reading a field is possible wherever the data's type is visible: within a module, any data; across modules, any exposed data (exposed means importable, and all of its fields are readable — there is no per-field exposure). A behavior may read the fields of its input data even when that data comes from another module. What is constrained is construction, not reading.

## Consequences

Reading a field cannot break an invariant; only construction can, and construction is limited to the paths of ADR-0002. So allowing cross-boundary reads does not weaken the "no unvalidated value" guarantee — reading and constructing are separate permissions. No getter-only behavior is needed to pass a value outward: such a getter would not appear in the spec DSL, so it could not be a behavior at all (ADR-0005).

"Wherever the data's type is visible" is the whole rule, and issue #187 was the compiler not holding the other end of it up. A field of an exposed data could be of a type its module kept to itself, so a value whose type is *not* visible arrived in a module anyway. Reading a field of it compiled and then failed with `IllegalAccessError`, since the class carrying the field is package-private.

The fix is not a second rule about what such a reader may do. It is that the value never arrives: what a module reaches out with may not rest on what it keeps (`[#exposed-surface]`), so the field that would have carried it out cannot be declared. Rust reports the same thing in the same place (`private_interfaces`: "type `UserId` is more private than the item `Order::by`"), as does F# (`FS0410`), and reporting it at the module that decides it beats reporting it at each reader that walks into it.

The alternative was to let the value flow opaquely and refuse the operations that open it, which is where Elm and Haskell leave it — a value of an unexported type passes through a module that cannot name it, and the read that would open it is refused where it is written. It was measured and rejected: on the JVM the line does not fall in one place. `List<Hidden> == List<Hidden>` and a hidden `data`'s `==` emit `Objects.equals` and run correctly, while a hidden newtype's `==` and `<` unwrap to the base (ADR-0047) and fail — so "what counts as opening it" comes out of what codegen happens to emit, and an author cannot predict it. What lets Elm and Haskell hold that line is inference, which Souther does not have at a signature (ADR-0017); what lets F# and Rust hold the declaration line is a way to expose a type's name while keeping its representation private, which Souther does not have either. Between the two, the declaration line is the one that can be stated in a sentence.

The cost is that exposing a type also opens its fields to readers, since `exposing` is type-granular. That is smaller than it looks: an exposed data's `decoder()`/`encoder()` are public API (`[#jvm-codec]`), so its representation already round-trips at the boundary. Giving `exposing` a way to publish a name without its representation — Haskell's `module M (T)`, OCaml's `.mli`, Rust's private fields — would remove even that, and is a separate decision.

On the JVM, exposed data get public read accessors, because module = package and a package-private field cannot be read across the boundary. Constructors stay non-public, so nothing reaches the fields without the invariant: building one goes through the decoder or through the checked entry, which an exposed data publishes (`[#jvm-construction-privacy]`). Reading a field from Java is the same exposure the encoder already gives by emitting every field as JSON; what is protected is the invariant, not the act of building.

## References

- Specification: `[#field-visibility]`, `[#exposed-surface]`, `[#jvm-product]`, `[#jvm-construction-privacy]`
- ADR-0059 (construction is closed to declared paths), ADR-0047 (a newtype compares by its wrapped value), ADR-0017 (a signature is written, not inferred)
- Issue #187 (the read that was emitted anyway). Rust 1.94 `private_interfaces`, F# 10.0.302 `FS0410`, GHC 9.6, Elm 0.19.2, javac 25
