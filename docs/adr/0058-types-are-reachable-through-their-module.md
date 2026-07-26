# ADR-0058: A type is reachable through the module that declares it

Status: Accepted (decided 2026-07-26). Supersedes the sentence in `[#imports]` that said a type has no qualified form.

## Context

Souther had two module mechanisms. The standard library was reachable qualified — `String.length` works with no `import`, and `import String ( length )` only elides the qualifier. A user module was not: a name existed in another module only if imported, and no qualified form was accepted anywhere. `probe.up.金額` was a syntax error, in a type position and in an expression.

The gap showed up as issue #101. Two bounded contexts each declaring `金額` or `顧客ID` is ordinary, and a third module integrating both cannot import the name twice. The spec said what to do about it: import the one you mean, and reach the other "through a module that gives it a different name". That is a shim module written for the compiler's benefit, and the type it re-declares is a different type, so it does not integrate the two contexts — it hides one. The only other way out was renaming a type in an upstream module, which is not the integrator's to change.

Underneath the surface gap was a representation one. A type name was carried as a `String` and looked up in one flat map per module, so two `金額` could not both be in it. The backend then derived a class from a simple-name-to-package map, which has the same collision. Names written inside another module's declaration — a spread's element, a field's type — were resolved against the *reading* module's names, which is why reading a field spread in from a third module needed that module imported too (the other half of issue #110).

Elm, OCaml and Java all give a name its home before anything else uses it. Elm canonicalizes to `TType ModuleName.Canonical Name [Type]` in a pass whose comment says "Creating a canonical AST means finding the home module for all variables"; OCaml's `Path.t` distinguishes `Pident` from `Pdot` in the type system; javac carries a fully qualified name with an owner on every `Symbol`. All three then let source name a type through its module — `java.util.List` and `java.awt.List` in one file is the everyday case.

## Decision

**A type is identified by the module that declares it plus the name written there, and source may name it that way.**

- `Type.Ref` and `Type.Union` carry a `TypeName` (declaring module, name). A written name becomes one during resolution, which is the only place source text is read.
- A qualified reference needs no `import`, matching the rule the standard library already follows. `import` only lets a name be written bare.
- `import M as A` names a module locally. The alias holds in the module that writes it and must be a name nothing else answers to there.
- A qualified reference reaches only what the declaring module exposes.
- A name written inside a declaration is resolved in the module that wrote it, not in the module reading it.
- A dependency counts however it is written, so a cycle closed by a qualified reference is E1501 like one closed by an `import`.

Qualified form is accepted in type positions and as a `match` arm's case name. It is not accepted in a construction, because construction is closed to the declaring module's paths anyway (ADR-0002): there is nothing a qualified constructor could reach that a bare one could not.

## Alternatives considered

**Import alias for a name (`import probe.b ( 金額 as b金額 )`).** Declined earlier and still declined: it invents a third name for the type, local to one module, so the same type reads differently in each module that integrates it. Naming the module instead leaves the type's name alone.

**Keeping the shim module.** What the spec prescribed. Rejected: a re-declared type is a different type, so the integrator gets a translation layer where it wanted a reference, and the two contexts still cannot meet.

**A fully qualified `String` everywhere.** Cheapest change — keep `Type.Ref(String)` and put `probe.b.金額` in it. Rejected: every place that compares a reference to a written name would keep compiling and start being wrong. Changing the type is what made the compiler point at those places.

**Requiring an `import` for a qualified reference (Elm's rule).** Rejected for consistency with the standard library, whose qualified access has never required one. The dependency that an `import` line used to record is now read off the references themselves, which is what cycle detection needs regardless.

## Consequences

- Issue #101's collision has a way out inside the module: name each `金額` through its module, or alias the modules.
- `importedPackages` is gone. The backend derives a class from the `TypeName` it is given instead of looking the package up by simple name; `souther.runtime`'s built-in cases (`DivisionByZero`) need no special case, since their name says where they live.
- A field spread in from another data is readable with only the data it is read from in scope.
- A sum's cases are its own module's, whether or not the reader imported them.
- Behaviors are still reached by a bare name only: a behavior is not a type, and qualified behavior references are a separate step.
