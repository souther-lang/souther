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

Qualified form is accepted in type positions and as a `match` arm's case name. A construction expression takes the bare name of an imported type, which is enough to reach it; the qualified form there is not accepted yet.

## Alternatives considered

**Import alias for a name (`import probe.b ( 金額 as b金額 )`).** Declined earlier and still declined: it invents a third name for the type, local to one module, so the same type reads differently in each module that integrates it. Naming the module instead leaves the type's name alone.

**Keeping the shim module.** What the spec prescribed. Rejected: a re-declared type is a different type, so the integrator gets a translation layer where it wanted a reference, and the two contexts still cannot meet.

**A fully qualified `String` everywhere.** Cheapest change — keep `Type.Ref(String)` and put `probe.b.金額` in it. Rejected: every place that compares a reference to a written name would keep compiling and start being wrong. Changing the type is what made the compiler point at those places.

**Re-export — letting `exposing` name a type this module imported.** The other way to give one module access to another's types: a module in the middle publishes what it depends on, and its consumers reach the type through it. Rejected, and this settles the question rather than deferring it (it had been held until qualified reference landed, since Elm's refusal only makes sense paired with `import ... as`).

Three measurements say what the alternative actually is. Java has no name re-export at all: `exports` covers a module's own packages, and `requires transitive` re-exports *readability* — with plain `requires a`, a consumer of the middle module cannot touch the upstream type even where it flows through the middle module's own API ("package pkga is declared in module a, but is not read by module c"); with `requires transitive a` it compiles (javac 25). Elm refuses it in `Canonicalize.checkExposed`, which admits only local declarations and reports `ExportNotFound` for an imported name. F#, OCaml and Scala 3 do have it, and what they have is a transparent alias, not a visibility list: `type Amount = Up.Amount` is the same type (`typeof` agrees, and a value made upstream fits a slot named through the alias), and it does not carry construction — with a `private` representation the alias is rejected at the construction site (`FS1093`, dotnet 10). Scala 3's `export` states its motivation as making composition as easy to write as inheritance, and generates forwarders.

Against Souther that leaves nothing to add and one thing to avoid. The readability Java's `requires transitive` buys is already the rule here: a qualified reference reaches any module of the compilation, so no middle module has to relay anything. What re-export would add is a second name for one type, which in every language that has it is a transparent alias — a declaration form Souther does not have, and cannot spell with `data X = Y`, since that is a newtype and therefore a different type. Introducing the language's first transparent type name is a separate decision from this one. And `exposing` also decides what a Java implementation may build: a data named in `constructs` must be exposed or the build has no way to create it (E1305). A re-exported name would have this module authorise the construction of a type it cannot construct itself — which ADR-0002 closes and issue #124 shows the access error for. The same direction ADR-0057 refused: a module's published surface stays a function of its own source.

**Requiring an `import` for a qualified reference (Elm's rule).** Rejected for consistency with the standard library, whose qualified access has never required one. The dependency that an `import` line used to record is now read off the references themselves, which is what cycle detection needs regardless.

## Consequences

- Issue #101's collision has a way out inside the module: name each `金額` through its module, or alias the modules.
- `importedPackages` is gone. The backend derives a class from the `TypeName` it is given instead of looking the package up by simple name; `souther.runtime`'s built-in cases (`DivisionByZero`) need no special case, since their name says where they live.
- A field spread in from another data is readable with only the data it is read from in scope.
- A sum's cases are its own module's, whether or not the reader imported them.
- A behavior of another module is named through it too, as a `>->` stage and as a `depends on`. A qualified behavior reference is rewritten to the bare name plus the import that brings it in, since a behavior's name is a member name in the generated class and the bare form is what the rest of the compiler needs — the qualifier only says which module to take it from, which is what an import says.
- One module cannot reach two behaviors of the same name, and this is refused rather than deferred. Two same-named types meet in a module because both values exist there — that is what this ADR admits — but two same-named behaviors meet because the module chose to call both, which is the module not having named what it is doing. A module that does depend on two such operations declares two injection targets of its own, under names that tell them apart, and the Java side binds each; that names the dependency in the integrating module's own vocabulary, which is the same move ADR-0057 requires for a consumed case. Mangling a colliding pair's field names (`up$twice`) is therefore not held open: it would also make the Java surface depend on who imported what, which ADR-0057 refused. Naming both is reported instead of one silently winning, which is what used to happen — the failure then surfaced as a type mismatch between two types printed under one name.
- `exposing` keeps meaning "what this module declares". A downstream module names an upstream type through the module that declares it, so an integration module translates rather than republishes — which is what a bounded context does with another context's vocabulary.
