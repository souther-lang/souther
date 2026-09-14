# Working on the compiler

This is for changing Souther itself. Using it needs none of this — the [README](README.md) is that,
and a release carries the command line already built.

## Building

JDK 25 and Maven. The build is one reactor, and a module is not built on its own:

```sh
# The runtime and the compiler, the tests, and souther-cli/target/souther —
# a self-contained executable.
mvn install

./souther-cli/target/souther compile hello.sou -d /tmp/out
```

`mvn -pl souther-cli -am -DskipTests install` builds the command line alone, which is quicker while
iterating on it. On Windows the build output to run is the plain jar beside it (`java -jar
souther-cli/target/souther.jar …`), and `bin/package-windows.ps1` turns that jar into the
distributions a release publishes.

`mvn test` leaves out the tests tagged `population`, whose subjects are the models this repository
carries rather than a source written to ask one question. `mvn test -Dgroups=population
-Dtest.excluded.groups=` is how to ask for those.

`.githooks/pre-commit` runs Checkstyle over the staged Java files and refuses a commit on a finding.
Every rule it runs is one CI already fails on. A clone turns it on once:

```sh
git config core.hooksPath .githooks
```

## The conformance corpus

`souther-compiler` carries a model written for this compiler, held to reaching every top-level form,
every reserved word and every standard library module the language declares, and checked against
what the compiler answered about it last — the whole adequacy report and every diagnostic, written
down beside the sources. A change that moves an answer is a change to those documents, made in the
commit that moved it. This is what answers "did this break a model of the size someone writes";
running the examples repository is not part of it.

```sh
# Everything the corpus is held to.
mvn -pl souther-compiler test -Dtest='souther.compiler.conformance.*Test'

# One corpus while iterating.
mvn -pl souther-compiler test -Dtest='souther.compiler.conformance.*Test' \
  -Dsouther.conformance.corpus=catalog

# Take up what a deliberate change did to the answers, then read the diff and commit it.
mvn -pl souther-compiler test -Dtest='souther.compiler.conformance.*Test' \
  -Dsouther.conformance.update=true
```

The last one rewrites the expected documents and then fails: a run that rewrote what it was going to
be measured against has not measured anything.

## Benchmarks

`souther-bench` measures what the compiler costs, and what the code it generates costs to run. It
carries the sources it measures, so a number means the same thing on any machine, and it checks that
they still compile before it times anything.

```sh
mvn -pl souther-bench -am -DskipTests install
java -jar souther-bench/target/souther-bench.jar

# One measurement at a time: cold, warm, phase, edit, scale, run.
java -jar souther-bench/target/souther-bench.jar phase edit
```

## The modules

- `souther-test-support`: what the other modules' tests are written against
- `souther-runtime`: `Option`, `Behavior`, `Fn`, boundary `Result`, `ConstraintViolation`, and
  numeric / collection helpers
- `souther-syntax`: the lexer, the lossless CST, and the diagnostic types every other module reports
  through
- `souther-compiler`: parser, name resolution, type checker, deriver, and ClassFile backend
- `souther-build-driver`: what a build plugin drives a compile through, against the protocol released
  from [souther-build-api](https://github.com/souther-lang/souther-build-api)
- `souther-fmt`: a canonical layout re-derived from the CST
- `souther-lsp`: the language server
- `souther-cli`: the `souther` executable
- `souther-bench`: what the compiler costs, measured on a corpus the module carries
- `souther-program-api-test`: what a checked program answers to a reader outside this compiler
- `souther-architecture-test`: the rules the modules are held to about each other

## Branches and releases

Work goes on a branch off `develop` and reaches it through a pull request. `main` carries releases,
and [docs/releasing.md](docs/releasing.md) is the whole of how one is cut.

Design decisions are written down as ADRs under [docs/adr](docs/adr/README.md), with the reasoning
and the alternatives behind each.
