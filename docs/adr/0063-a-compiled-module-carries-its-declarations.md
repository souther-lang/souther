# ADR-0063: A compiled module carries its own declarations

Status: Accepted (decided 2026-07-27). Resolves issue #128.

## Context

A Souther module could only be imported by a module compiled in the same invocation. `examples/ordering` works because its seven modules live under one `src/main/souther` and go through one `compileModules` call. There was no way to publish `shared.money` from one Maven project and `import shared.money ( Amount )` from another, which two teams sharing a domain type hit immediately.

Import resolution was closed over the sources of the call: `visibleDefs` resolved each `Ast.Import` against a map built from the parsed sources, and a miss was `unknown module`. The compiler had no way to obtain an imported module's declarations from anything but a parsed `.sou`.

Shapes alone would not have been enough. `InvariantChecker` reads an imported type's **invariant expression** for the discharge analysis, so whatever crosses the boundary carries expressions, not just field names and types.

Every statically typed language on the JVM and the CLR was measured before deciding. None ships source; all ship compiler-generated metadata, and all stamp a version.

| Language | In the artifact | Source | Version stamp |
|---|---|---|---|
| Java | the `.class` itself (`Signature` and friends were added to the format for this) | no | classfile major version |
| Scala 2.13 | `@ScalaSignature` on the class | no | pickle format version |
| Scala 3 | `.tasty` beside the `.class` — the full typed tree | no | version bytes and the producing compiler string |
| Kotlin | `@kotlin.Metadata` on the class, plus `META-INF/*.kotlin_module` | no | `mv=[2,2,0]` |
| F# | embedded assembly resources `FSharpSignatureCompressedData.<name>` | no | format version |
| Clojure | AOT classes **and** `.clj` | yes | none |

The one that ships source is dynamic and compiles at load time. Nobody collects the metadata under `META-INF`: it is attached to the class or placed beside it. And all of them resolve dependencies from the ordinary compile classpath with nothing else declared.

## Decision

**A compiled module carries what it declares, as the source that declared it, on the classes it generated. An import resolves against the sources being compiled, then against the compiled modules on the class path.**

- Each definition rides on the class it produced: a `data` on the class of that name, a behavior on its interface. A module's own facts — its `module … exposing ( … )` line, its imports, and an index of which classes to read — ride on a `$Module` class emitted for them.
- The declarations travel as Souther source and are read back by the parser. The declaration surface is recursive (`List<Map<K, V>>` nests, and so does a decoder reference) and an annotation type may not have an element of its own type, so types and invariants would be text whatever structure surrounded them. Given that, structure buys a second description of the same syntax and nothing else.
- Two things are not source. Whether a behavior is an injection target is a flag: a behavior is one when its module writes no `let` for it, no `let` is published, and the language has no spelling for the difference. And a `>->` composition declares stages rather than a signature, so the computed signature is published and the stages stay behind.
- Implementation does not travel, except the helper `let`s an invariant calls. An invariant is part of what a type is, so it has to be readable where the type is imported, and it cannot be read without the helpers it names.
- A module read from the path is derived and desugared exactly as a local one, and then differs in one respect only: it is not among the modules being generated. Its classes and its examples belong to the build that made them and are not produced or run again.
- One path serves both things a compile needs from a dependency. Its declarations are read out of the same class files that constant evaluation and example runs load, so what an import resolves against and what an example calls cannot be two different versions.
- Nothing is configured. Under the annotation processor the path is the compile classpath, which depending on a jar already fills in. The CLI takes `-cp` / `--class-path`.
- A `BOUNDARY_VERSION` records what an importing module reaches — `__construct` descriptors and visibility, codecs, a behavior's class and methods, an output union's case names, and the runtime types in those signatures. A module whose number is not the reader's is refused, naming the compiler that built it. A change confined to the inside of a generated method does not move it. The number is not the Souther version: a release that leaves it alone keeps every previously built jar readable.
- A module compiled here may not also be on the path, and a module on the path that needs one absent from it is reported as an incomplete path rather than as an import nobody here wrote.

## Consequences

Cross-jar `import` does exactly what same-compilation `import` does. The module-local output unions of ADR-0057, E1606, and the rule that a `let` cannot call an imported behavior all stand for the same reasons as before, so no language surface changes.

A jar grows by the text of its declarations — 6.5% on `examples/ordering`. Reading and stamping cost about 0.8% of a link, which does not show up end to end.

Between releases that move `BOUNDARY_VERSION`, a library and everything built against it must be rebuilt together. During 0.x that will happen: of the recent changes, ADR-0056 and ADR-0059 would have moved it and ADR-0060 and ADR-0061 would not. Publishing to a shared repository would then hit what Scala 2 answers with `_2.13` in the artifact name. Nothing is done about that here — there are no published Souther libraries, and the case being served is teams that can rebuild together.

A project written only in Souther still has to write one Java file. The annotation processor runs as part of compiling Java, and javac does nothing at all when a project has no Java source.

## Alternatives

**Ship the `.sou` in the jar.** The smallest change, and the invariant expressions come free. Rejected on the prior art: no statically typed language does it, the consumer would re-parse and re-check a dependency whose own build already did, and a jar would carry its implementation.

**Serialize the declarations into a format of their own.** What Kotlin, Scala 2 and F# do. Rejected because the recursive parts have to be text regardless, leaving a second definition of the declaration surface to keep in step with `Ast` — which is still moving — and a reader to maintain, for a compiler with one author.

Related: ADR-0057 (behavior output unions are module-local), ADR-0058 (a type is reachable through its module), ADR-0059 (construction is not closed to the declaring module).
