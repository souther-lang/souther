# Souther

<p align="center">
  <img src="docs/images/souther.png" alt="Souther" width="420">
</p>

Souther is a small JVM language for describing business data, value constraints, and state transitions, then generating types and behaviors that Java can use.

You write business rules with `data` and `behavior`. `invariant` makes value constraints explicit, while behaviors implemented in Java make dependencies such as a database or a clock explicit. This keeps the domain model's boundary intact as it becomes an implementation.

```text
external input -> decoder -> Souther data / behavior -> encoder -> external output
                                   ^
                           Java injects dependencies
```

Souther is intended to turn the specification DSL of [Specification Model-Driven Development (SMDD)](#specification-model-driven-development-smdd) into an executable implementation model. It makes executable the constraints, validated construction, and outside-world dependencies that the specification DSL leaves in comments.

## Start with an example

This example either moves a travel request into the `Submitted` state or rejects it. An `Amount` cannot be negative, and the behavior produces either `Submitted` or `Rejected`.

```text
module example.trip
import String ( length )

data EmployeeId = String
    invariant length(value) > 0

data Amount = Int
    invariant value >= 0

data DraftRequest = { applicant: EmployeeId, plannedCost: Amount }
data Submitted = { ...DraftRequest, submittedAt: String }
data Rejected = { reason: String }

behavior submit : (request: DraftRequest, submittedAt: String) -> Submitted | Rejected
    constructs Submitted, Rejected

let submit (request, submittedAt) = {
    guard request.plannedCost.value <= 100000 else Rejected { reason = "high_cost" }
    Submitted { ...request, submittedAt = submittedAt }
}
```

The example introduces Souther's central ideas:

- `data` represents domain values and states. `|` means alternatives, and `...` composes fields.
- An `invariant` is checked every time that `data` is constructed by a decoder or behavior.
- A `behavior` declares its input and possible business outcomes; `constructs` grants it authority to construct those values.
- `guard ... else ...` is a business branch. `Rejected` is an ordinary domain value, not an exception.

The complete runnable example is [`businesstrip`](https://github.com/souther-lang/examples/tree/main/businesstrip), in the [examples repository](https://github.com/souther-lang/examples).

## Try it

Souther requires JDK 25 and Maven, at build time and at run time alike. Generated `.class` files and `souther-runtime` are pinned to the Java 25 class-file version, and `raoh` — which every derived decoder and encoder calls — is a Java 25 artifact, so an application consuming Souther's output runs on Java 25 and later. `SoutherProcessor` generates bytecode during the host build (see the [examples repository](https://github.com/souther-lang/examples)), so a project using it as an annotation processor needs JDK 25 for that too.

```sh
# Build the runtime and compiler, and run the tests.
mvn install

# Compile a .sou file to .class files.
java -cp souther-compiler/target/classes:souther-runtime/target/classes \
     souther.compiler.Main \
     compile hello.sou -d /tmp/out
```

To try a behavior without writing any Java, `souther run` compiles a `.sou` in memory and drives one behavior: it decodes the `--input` JSON through the behavior's derived decoders, applies it, and prints the result through its derived encoder. A single file run on its own may omit the `module` header — it is named after the file (ADR-0043).

The `souther-cli` module bundles the compiler, runtime, and their dependencies into one really-executable jar, so no classpath or `java -jar` is needed:

```sh
# Build target/souther — a self-contained executable (a launcher stub prepended to an uber jar).
mvn -pl souther-cli -am -DskipTests install

# hello.sou  (no module header needed)
#   behavior greet : (name: String) -> String
#   let greet (name) = "Hello, " ++ name
./souther-cli/target/souther run hello.sou --behavior greet --input '"world"'
# => "Hello, world"
```

`run` runs a behavior that is both runnable and exposed. It is runnable when it has a `let` and depends on nothing, or when it is a `>->` pipeline whose stages are all runnable in that same sense; an injected behavior, one with injected dependencies, or a pipeline with such a stage is refused with a reason. It is exposed when the module's `exposing` list names it — the runner reaches a behavior the way any reader outside the module does — and a file with no `exposing` list exposes everything in it. `--behavior` may be omitted when the module holds exactly one behavior that is both, and `--input` when the behavior takes no argument. A multi-argument behavior takes a JSON array (`--input '[3, 7]'`). The runner drives a single self-contained file — stdlib imports resolve, but it cannot link against other user modules.

The same `souther` binary also compiles to `.class` files (`souther compile hello.sou -d out`). It runs on any Unix shell; on Windows, use it as a plain jar (`java -jar souther-cli/target/souther.jar …`).

`souther-bench` measures what the compiler costs, and what the code it generates costs to run. It carries the sources it measures, so a number means the same thing on any machine, and it checks that they still compile before it times anything.

```sh
mvn -pl souther-bench -am -DskipTests install
java -jar souther-bench/target/souther-bench.jar

# One measurement at a time: cold, warm, phase, edit, scale, run.
java -jar souther-bench/target/souther-bench.jar phase edit
```

To integrate Souther into an application's Maven build, configure `SoutherProcessor` as an annotation processor. The [examples repository](https://github.com/souther-lang/examples) contains that configuration and examples using the generated types from Java, Kotlin, and Clojure boundaries (Spring Boot, jOOQ, Pedestal).

The Java API compiles a source string containing either one module or several linked modules:

```java
Map<String, byte[]> classes = Compiler.compile(source);
Map<String, byte[]> linked = Compiler.compileModules(List.of(employeeSource, tripSource));
```

### Compact object headers suit the shape of a domain model

A Souther model is many small immutable values — a newtype per identifier and per amount, a data per state. On JDK 25 the application running the generated code can take four bytes off every object header with `-XX:+UseCompactObjectHeaders` (JEP 519, production-ready and off by default). It is the deploying application's flag, not Souther's, and it needs no rebuild.

Four bytes off a header turns into eight bytes off an allocation when it crosses the eight-byte alignment boundary, and into nothing when it does not — so the gain is uneven and worth measuring rather than assuming. Bytes actually allocated per instance, on GraalVM 25.0.3 (arm64):

| value | default | compact |
| --- | --- | --- |
| a newtype over `Int` (one `long` field) | 24 | 16 |
| a data with two fields | 24 | 16 |
| a boxed `Long` — one element of a `List<Int>` | 24 | 16 |
| a newtype over `String` (one reference) | 16 | 16 |
| the 32-slot block a `List` grows in | 144 | 144 |

End to end, a behavior building a 1000-element `List<Int>` through `List.map` goes from 66.1 to 57.8 bytes per element. A pure `PersistentVector.append` is unchanged at 50, because the vector's own size does not cross a boundary.

The compiler suite and every example pass under the flag (`mvn test -DargLine="-XX:+UseCompactObjectHeaders"`), including the Spring Boot and jOOQ boundaries.

## Editor support

The VS Code extension lives in [souther-lang/souther-vscode](https://github.com/souther-lang/souther-vscode) and is published to the Visual Studio Marketplace and Open VSX. It bundles the language server and fetches a Java 25 runtime by itself when the machine does not already have one, so installing it and opening a `.sou` file is enough. It gives diagnostics, the document outline, hover, go-to-definition, find-references, rename, completion, quick-fix code actions, formatting, and semantic tokens.

The server is `souther-lsp`, a self-contained jar that speaks LSP over stdio, attached to every release here. Other editors can launch it with `java -jar souther-lsp.jar`. Formatting is also on the command line: `souther fmt <file.sou>` prints the canonical form, `-w` rewrites in place, and `--check` exits non-zero when a file is not formatted.

## Documentation on the command line

The `souther` binary answers questions about the language and its libraries itself, so neither a
person nor a coding agent has to hunt through a workspace or disassemble jars:

```sh
souther doc                    # every specification section and shipped topic, name<TAB>title
souther doc newtype            # one section, by its anchor
souther doc cli/run            # a topic the command line ships about itself
souther doc raoh/tutorial      # a guide a bundled library ships
souther doc --search decoder   # ranked hits, each with the line it matched on
souther api Option             # the stdlib surface with resolved signatures
souther api --search fold      # the names that answer a term
souther api --source Option    # a stdlib module's own source, comments included
souther japi net.unit8.raoh.Issues        # a dependency's public API, with javadoc
souther japi net.unit8.raoh.Issues#add    # one member of it
```

New to the language? `souther doc cli/start-here` names the four sections to read and the order.

`souther doc` serves the specification the compiler was built from — it is bundled in the jar, not
looked up on disk. `souther api` prints the signatures the type checker itself resolved, including
the names that exist only as sugar over a private helper. `souther japi` reads class files without
loading them, and takes javadoc from the `-sources.jar` beside the jar, or from the sources bundled
with the CLI when there is none.

A library may ship its own documentation inside its own jar under `META-INF/souther-docs/`, and
`souther doc` then lists its topics alongside the specification and reads them by a `set/topic`
name. The CLI's own reference is carried that way and is nothing special; raoh ships its guides the
same way from 0.7.1 on, so `souther doc raoh/composition-patterns` reads raoh's own guide at the
version this build depends on.

The same answers are served over the Model Context Protocol: `souther mcp` speaks MCP on stdio,
exposing `doc_search`, `doc_read`, `stdlib_api`, `stdlib_api_search`, `stdlib_api_source` and
`jar_api`, so agent harnesses that prefer tools over shell commands register one command.
`doc_read` with no argument lists every section and topic, which is where a client with nothing
else starts. It answers under protocol revisions `2025-11-25`
and `2025-06-18` — the ones whose opening exchange is `initialize` — echoing the client's own when
it is one of them:

```json
{ "mcpServers": { "souther": { "command": "souther", "args": ["mcp"] } } }
```

## What Souther guarantees

### Construction of invalid data is confined

Only a derived decoder, a behavior declaring `constructs T`, that behavior's Java implementation, or compiler-generated code may construct `data T`. Merely using `T` as a return type does not grant construction authority. Generated constructors are non-public, so the rule holds across the Java boundary.

### Business outcomes are not exceptions

A behavior's output is a sum of named data, such as `Submitted | Rejected`; it has no `Result` / `Either` wrapper or privileged success/failure slot. `f >-> g` sends only the output cases that `g` accepts to the next stage, and passes the rest through unchanged. Whether a case leaves the main path is a property of composition, not of the value itself.

The runtime's `Result` for malformed decoder input is separate from a behavior's domain outcome: the former belongs to the boundary, the latter is domain data.

### The outside world stays at the Java boundary

Souther does not directly call databases, HTTP services, files, clocks, or ID generators. Instead, it declares a behavior with no implementation and Java injects that implementation.

```text
behavior currentTime : () -> DateTime

behavior approve : (request: AwaitingApproval) -> Approved
    depends on currentTime
```

Souther cannot call arbitrary Java APIs; Java can use the generated data and behaviors. This asymmetry makes the boundary between pure domain computation and external effects explicit.

## Language shape

Souther is deliberately small:

- immutable product / sum / unit data, `List<T>`, `Map<String, T>`, and optional fields (`T?`)
- `invariant`, `match`, `let`, `if`, `guard`, record literals, and field spread
- `behavior`, Java injection, `depends on`, `constructs`, and type-routed `>->` composition
- derived decoders / encoders and explicit modules with `exposing` / `import`

It intentionally does not provide exceptions, `null`, mutable state, asynchronous execution, arbitrary JVM calls, type classes or higher-kinded types, a package manager, or a REPL. These omissions keep construction paths, value constraints, and outside-world dependencies tractable.

Not yet implemented: incremental compilation, static invariant proofs, handwritten codec syntax, and JSON Schema / Wasm / JavaScript output. Generated classes carry `SourceFile` / `LineNumberTable` debug info, so a runtime stack trace (an invariant abort above all) points back to the `.sou` source line. An LSP server ships (`souther-lsp`); its name resolution is per-module, and workspace-wide (cross-module) resolution is future work.

## Details and examples

- [Language specification (Japanese)](specification.adoc): the normative syntax and semantics
- [ADRs](docs/adr/README.md): design decisions, alternatives, and prior art
- [Examples](https://github.com/souther-lang/examples): Maven / Gradle integration, decoders / encoders, and Java / Kotlin / Clojure boundary interop (Spring Boot, jOOQ, Pedestal). They live in their own repository because the boundary code moves on Spring / jOOQ / Kotlin's schedule rather than the compiler's; their build tracks `develop` here

The repository has these Maven modules:

- `souther-runtime`: `Option`, `Behavior`, `Fn`, boundary `Result`, `ConstraintViolation`, and numeric / collection helpers
- `souther-syntax`: the lexer, the lossless CST, and the diagnostic types every other module reports through
- `souther-compiler`: parser, name resolution, type checker, deriver, and ClassFile backend
- `souther-fmt`: a canonical layout re-derived from the CST
- `souther-lsp`: the language server
- `souther-cli`: the `souther` executable
- `souther-bench`: what the compiler costs, measured on a corpus the module carries

## Specification Model-Driven Development (SMDD)

The SMDD specification DSL expresses business rules with `data` (AND / OR / List / `?`) and `behavior` (`->` / `>->`). It leaves value constraints, the fact that a value has been validated, and outside-world dependencies in comments. Souther maps those respectively to `invariant`, closed construction paths (`decoder` / `constructs`), and behaviors injected from Java.

The [language specification](specification.adoc) has the full mapping and design principles.

## License

Copyright © kawasima 2026

Released under the [Eclipse Public License 2.0](https://www.eclipse.org/legal/epl-2.0/).
