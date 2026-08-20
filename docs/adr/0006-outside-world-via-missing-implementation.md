# ADR-0006: Outside-world dependencies are behaviors with no implementation, injected from Java

Status: Accepted

## Context

Souther must not implement outside-world effects — database queries, HTTP calls, file
access, clock reads, id generation, message sending. These are exactly the things the
specification DSL annotates with `// depends:` (depends on) and `// side effect:` (side effect).
The language needs a way to name such a dependency as a type while leaving its
implementation outside, and to do so without adding surface that the spec DSL does not
have.

## Decision

A behavior whose type is declared but that has no implementation is an outside-world
dependency: its implementation is injected from Java. There is no keyword — the *absence*
of an implementation is what means "supply this from outside." An implementation is
either a same-named `let` (`[#fn-declaration]`) or a `>->` composition on the right-hand side (`[#composition]`); a
behavior with neither is the injection target.

## Consequences

The spec DSL has no `required` word either; a dependency is marked only by a comment
note. Because Souther also uses no keyword, the DSL line survives verbatim — `behavior
now = () -> DateTime` with no `let` is the whole declaration.

Code that uses such a behavior lists its name under `depends on`, which then surfaces as an
argument of the using `let` (see ADR-0016). The read-only "// depends" versus mutating
"// side effect" distinction is documentation of intent only; it does not affect the value
composition rules.

`constructs` on a non-implemented behavior (`[#constructs]`) reads the same as if it were
implemented in Souther — `findMember` mints what it mints, but does *not* mint `Member` (it
reads an outside value through a decoder). Its failure cases are usually unit data, which are
in no construction set and so are not named (`[#constructs-excludes-unit-data]`); a clause with
nothing left to name is not written at all.

The generated Java base class (`[#java-base-class]`) hands out a factory for each unit case of
the *output type*, which is where the failure cases are read from — not from this clause. The
clause supplies the factories for the field-bearing data and newtypes it names, which a decoded
pass-through output cannot be told from by shape alone.

The base class an implementation extends is public whatever `exposing` says, so the
implementation overrides `apply` from outside the module and *writes* the behavior's input
and output types where it does. A type the module keeps to itself cannot be written there,
and no raw-typed override stands in for it — javac reports the erased signature as clashing
with the one being overridden rather than overriding it. So an injected behavior's input and
output are exposed by the module that declares them, whether or not the behavior itself is in
`exposing` (issue #187). This is the same rule an exposed name follows, applied to the one
other thing a module reaches out with (`[#exposed-surface]`).

The *cases* of a multi-case output are not reached by it: that output is generated as a union
interface of its own, public regardless, and a case is returned through the `protected`
factory or through the decoder without being named — measured, not stipulated, since javac
accepts and runs such an implementation from another package. That is what E1305's unit-data
allowance rests on.

Which behaviors get a `let` and which are injected is not mechanically derivable from the
DSL: `// depends:` is a note, not an obligation, so its absence does not prove a behavior is
internal. The one-to-one correspondence (ADR-0001) is therefore at the level of the
*declaration*, not the implementation form (`let` / injection / `>->`); the modeler chooses
the form using the `// depends:` / `// side effect:` notes as a guide.

## References

- Specification: `[#no-impl-for-outside]`, `[#injected-behavior]`, `[#java-base-class]`, `[#exposed-surface]`
- ADR-0001 (one-to-one with the spec DSL), ADR-0016 (requirements as arguments)
- ADR-0015 (what reaches out may not rest on what is kept), issue #187
