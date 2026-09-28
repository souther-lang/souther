# Souther

<p align="center">
  <img src="docs/images/souther.png" alt="Souther" width="420">
</p>

Souther is a small JVM language for business rules that stay true: what a value may be, which states
follow which, and what each decision answers. You write them once, as `data` and `behavior`, and
they compile to Java types that keep the distinctions the model made.

What a rule is worth depends on whether anything holds it to account, so the examples that describe
a behavior are part of the language rather than a suite beside it. An `example` is evaluated while
the model compiles, and `souther examples` measures what those examples cover: which class of an
input nothing stands in, which boundary value nothing sits at, which rule of a body nothing goes
through. Where it cannot answer, it says what the question is still open on instead of reporting a
clean result.

```text
external input -> decoder -> Souther data / behavior -> encoder -> external output
                                   ^
                           Java injects dependencies
```

The rest of the language is there to keep that measurable. `invariant` puts a constraint next to the
type it belongs to, so construction is the one place it is checked. A behavior's outcomes are
ordinary data rather than exceptions, so a rejection is a case a caller can be held to. A dependency
on the outside world is declared and injected from Java, so what the domain computes stays separate
from what it reaches for.

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

## Install

On macOS and Linux, through Homebrew:

```sh
brew install souther-lang/souther/souther
```

On Windows, through [Scoop](https://scoop.sh):

```powershell
scoop bucket add souther https://github.com/souther-lang/scoop-souther
scoop install souther
```

`install.ps1` is the Windows install without Scoop. It takes a release, holds it against the `SHA256SUMS` published beside it, unpacks it under `%LOCALAPPDATA%\Programs\souther` with a `current` link at the version it just wrote, and puts that link on the user's `PATH`. It installs for one user, needs no administrator, and owns that directory: an uninstall removes it and the one `PATH` entry it added, and leaves the rest of `PATH` alone.

```powershell
irm https://raw.githubusercontent.com/souther-lang/souther/main/install.ps1 | iex
```

Piping into `iex` passes no arguments, so asking for a particular version, for the distribution without a runtime, or for an uninstall names the script block instead. The script's header says how.

Every release also attaches its artifacts to the [GitHub Release](https://github.com/souther-lang/souther/releases) for a download by hand. `SHA256SUMS` covers all of them, so `sha256sum -c SHA256SUMS` in the directory they were downloaded into says which arrived intact.

- `souther` is the whole of the command line on Unix — a launcher prepended to an uber jar. Put it somewhere on `PATH` and it runs on a Java 25 it finds there.
- `souther-<version>-windows-x64.zip` carries a Java runtime of its own, so nothing has to be installed beside it. The command in it is `souther\souther.exe`, which `jpackage` writes from the same jar the other archive runs.
- `souther-<version>-windows-x64-nojdk.zip` is that same command line without the runtime, for a machine that has a JDK 25 already and for a CI image that would rather not carry a second one. The command in it is `souther\souther.cmd`, which reads `JAVA_HOME` and otherwise takes `java` from `PATH`.

Either Windows archive unpacks to one directory with the launcher at its root, so the directory to put on `PATH` is the same one. Neither keeps the class-data archive described below, so a compile there costs what a first compile costs on Unix.

A JDK and not a JRE, because `souther japi` reads a library's javadoc out of its sources and reaches a compiler to do it. On a runtime without one, that command ends on a class it cannot find and every other command answers as though nothing were missing.

Souther requires JDK 25, and so does an application consuming its output: generated `.class` files and `souther-runtime` are pinned to the Java 25 class-file version, and `raoh` — which every derived decoder and encoder calls — is a Java 25 artifact. The Java that runs Souther and the Java a project's build runs on are separate questions, and a bundled runtime answers only the first.

## Start a project

`souther init` writes a project rather than leaving one to be copied from an example. It takes the coordinate — a group and an artifact are yours to decide — and writes a build that already declares the Souther plugin and one `.sou` holding a model with the `example` rows covering it, so the first compile checks those rows and `souther examples` answers on the first run.

```sh
souther init com.example:hello
cd hello && mvn compile
```

`--build gradle` writes a Gradle build instead. Run inside a project that already has a `pom.xml` or a `build.gradle.kts`, it reads the coordinate out of that build and adds a source directory and the plugin declaration to it. Nothing already written is overwritten, and what it left alone it says.

The build plugins are released from their own repositories, and either compiles `.sou` under `src/main/souther` into the classes the rest of the build reads:

- [souther-maven-plugin](https://github.com/souther-lang/souther-maven-plugin), which takes the Souther to compile with from the `souther-runtime` dependency the pom already declares
- [souther-gradle-plugin](https://github.com/souther-lang/souther-gradle-plugin), where a project with a model names it as `southerVersion`

A build may also run the compiler as the `SoutherProcessor` annotation processor, which is what a project holding Java beside its model can do without a separate plugin. The [examples repository](https://github.com/souther-lang/examples) has both, with the generated types used from Java, Kotlin and Clojure boundaries (Spring Boot, jOOQ, Pedestal).

## Measure what the examples cover

`souther examples` reports, for every behavior, what the rows written beside it reach and what they do not:

```sh
souther examples businesstrip.sou
```

It answers on the positions of an input — which classes the behavior's own rules divide it into, and which of them no row stands in — on the boundary values those rules place, on the rules of the body and which of them a row goes through, and on the invariants of the types the behavior reaches, which are owed a row wherever such a value is constructed. What nothing covers is marked `!`, and `--strict` exits non-zero over exactly those, which is the form a build takes.

An adequacy line closes the report. It is not a grade: where the report could not settle a question it says `undetermined` and lists what each open position is waiting on, separating what a wider search would decide from what only a new row can. A limit of the compiler is never reported as an answer about the model.

```sh
souther examples businesstrip.sou --behavior submitTrip   # one behavior
souther examples businesstrip.sou --generate              # rows for what nothing covers
souther examples businesstrip.sou --strict                # refuse over the gaps
```

`--generate` writes the rows themselves, with the inputs filled in and `<?>` where the answer is owed — a row the report then counts as waiting for one. The [tutorial](https://souther-lang.org/tutorial/) works a model up from a record layout to a covered one by reading this report.

## Run a behavior

To try a behavior without writing any Java, `souther run` compiles a `.sou` in memory and drives one behavior: it decodes the `--input` JSON through the behavior's derived decoders, applies it, and prints the result through its derived encoder. A single file run on its own may omit the `module` header — it is named after the file (ADR-0043).

```sh
# hello.sou  (no module header needed)
#   behavior greet : (name: String) -> String
#   let greet (name) = "Hello, " ++ name
souther run hello.sou --behavior greet --input '"world"'
# => "Hello, world"
```

`run` runs a behavior that is both runnable and exposed. It is runnable when it has a `let` and depends on nothing, or when it is a `>->` pipeline whose stages are all runnable in that same sense; an injected behavior, one with injected dependencies, or a pipeline with such a stage is refused with a reason. It is exposed when the module's `exposing` list names it — the runner reaches a behavior the way any reader outside the module does — and a file with no `exposing` list exposes everything in it. `--behavior` may be omitted when the module holds exactly one behavior that is both, and `--input` when the behavior takes no argument. A multi-argument behavior takes a JSON array (`--input '[3, 7]'`). The runner drives one file: stdlib imports resolve, and an import of another user module resolves against `-cp`, the same class path `compile` takes (`souther compile catalog.sou -d out` then `souther run enrollment.sou -cp out …`).

`souther compile hello.sou -d out` is the same binary writing `.class` files. Most of what a small compile from the command line costs is the JVM loading and verifying the compiler's classes, so the first compile leaves an archive of them under `${XDG_CACHE_HOME:-$HOME/.cache}/souther`, named for the version, and the compiles after it start from that. Deleting it costs one slower compile; where it cannot be written, nothing is written and every compile is that one. An archive belongs to the binary that wrote it and to the JDK that wrote it, so one whose binary has been rebuilt or copied elsewhere, or which the JDK now running will not take, may be left unusable rather than rewritten — deleting it is what puts the next compile back to the faster one.

## Formatting

`souther fmt <file.sou>` prints the canonical form, `-w` rewrites in place, and `--check` exits non-zero when a file is not formatted, printing each difference as the rule it answers to, where in your own source it is, and what the two forms write there. The layout is re-derived from the tree rather than patched into the text, so there is one form and nothing to configure.

## Editor support

The VS Code extension lives in [souther-lang/souther-vscode](https://github.com/souther-lang/souther-vscode) and is published to the Visual Studio Marketplace and Open VSX. It bundles the language server and fetches a Java 25 runtime by itself when the machine does not already have one, so installing it and opening a `.sou` file is enough. It gives diagnostics, the document outline, hover, go-to-definition, find-references, rename, completion, quick-fix code actions, formatting, and semantic tokens.

The server is `souther-lsp`, a self-contained jar that speaks LSP over stdio, attached to every release here. Other editors can launch it with `java -Xss4m -jar souther-lsp.jar`. Where the `souther` binary is already on the path, `souther lsp` serves the same server and needs no jar path and no stack flag — this is what an agent harness takes, alongside `souther mcp`. The stack flag is the compiler's supported one, not a tuning knob: what a definition may say is bounded, and a source at that bound needs about a megabyte to walk. The `souther` binary sets it for itself.

An editor integration should not copy any of this out of prose. Both jars carry `META-INF/souther/tooling.json`, which states the language id, the source extension, the minimum Java and the JVM arguments the server needs, and where the syntax contract and the schema of `initializationOptions.souther` are inside the jar. It is a file in an archive so that a client can read it before it has a Java that can run anything here; `souther tooling` prints the same file. The syntax contract is versioned by the release it ships in and has no version of its own; the options schema has one, in its file name. In the answer to `initialize`, `capabilities.experimental.souther` names each `souther` option the running server reads, one key per option, and a key that is absent is an option that server does not read. An option it does not read is ignored; one it reads, written with a value the schema does not allow, is read as unset and reported with `window/showMessage` after `initialized`.

## Documentation on the command line

The `souther` binary answers questions about the language and its libraries itself, so neither a
person nor a coding agent has to hunt through a workspace or disassemble jars:

```sh
souther --version              # which Souther this is
souther help                   # every command, with a line saying what it is for
souther help compile           # one command's arguments and every option it takes
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

## Embedding the compiler

`souther.compiler.Compiler` is the one class name a caller outside this repository is meant to write
down. It compiles a source string containing either one module or several linked modules:

```java
Map<String, byte[]> classes = Compiler.compile(source);
Map<String, byte[]> linked = Compiler.compileModules(List.of(employeeSource, tripSource));
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

Not yet implemented: incremental compilation, static invariant proofs, handwritten codec syntax, and JSON Schema output. Generated classes carry `SourceFile` / `LineNumberTable` debug info, so a runtime stack trace — an invariant abort above all — points back to the `.sou` source line.

A model is many small immutable values, a newtype per identifier and per amount and a data per state, which is the shape `-XX:+UseCompactObjectHeaders` (JEP 519) suits: it takes bytes off every object header, and on JDK 25 the deploying application can turn it on without a rebuild. Whether that reaches an allocation depends on where the value sits against the alignment boundary, so it is worth measuring on the model at hand rather than assuming. The compiler suite and every example pass under the flag.

## Details and examples

- [Language specification](specification.adoc): the normative syntax and semantics
- [Tutorial](https://souther-lang.org/tutorial/) and [principles](https://souther-lang.org/principles/)
- [ADRs](docs/adr/README.md): design decisions, alternatives, and prior art
- [Examples](https://github.com/souther-lang/examples): Maven / Gradle integration, decoders / encoders, and Java / Kotlin / Clojure boundary interop (Spring Boot, jOOQ, Pedestal). They live in their own repository because the boundary code moves on Spring / jOOQ / Kotlin's schedule rather than the compiler's; its `main` builds against the latest release and its `develop` against `develop` here
- [souther-wasm-compiler](https://github.com/souther-lang/souther-wasm-compiler): a checked Souther program compiled to WebAssembly, developed in its own repository against a released compiler

Changing Souther itself, rather than using it, is [CONTRIBUTING.md](CONTRIBUTING.md).

## Specification Model-Driven Development (SMDD)

The SMDD specification DSL expresses business rules with `data` (AND / OR / List / `?`) and `behavior` (`->` / `>->`). It leaves value constraints, the fact that a value has been validated, and outside-world dependencies in comments. Souther maps those respectively to `invariant`, closed construction paths (`decoder` / `constructs`), and behaviors injected from Java.

The [language specification](specification.adoc) has the full mapping and design principles.

## License

Copyright © kawasima 2026

Released under the [Eclipse Public License 2.0](https://www.eclipse.org/legal/epl-2.0/).
