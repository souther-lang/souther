# ADR-0062: The floor is Java 25

Status: Accepted. Amends ADR-0022.

## Context

ADR-0022 pinned the generated class-file version rather than letting it follow whichever JDK ran the
build, and set that pin at Java 21. The pinning was right and stays. The value was not achievable.

Every derived decoder and encoder names Raoh types in its method descriptors, so loading a generated
`data` class requires Raoh on the classpath. `net.unit8.raoh:raoh:0.6.0` is class-file version 69 —
Java 25. A generated program therefore did not run on Java 21 and never had:

```text
$ java21 -cp out:souther-runtime Pure          # touch a generated Amount
NoClassDefFoundError: net/unit8/raoh/decode/Decoder
# and with raoh on the classpath:
UnsupportedClassVersionError: class file version 69.0, this JVM supports up to 65.0
```

The specification stated the opposite in three places — `[#target-jdk]`, the non-functional
requirement that the output is "usable straightforwardly from Java 21+", and ADR-0022 itself — and CI
ran only JDK 25, so nothing tested the claim.

Two ways out: lower Raoh to release 21, or raise the floor. Lowering was feasible (five uses of the
unnamed pattern variable `_`, plus a version-floor check on the Jackson it pulls in), but it buys a
compatibility promise nobody had asked for and leaves the language pinned behind its own dependency.

## Decision

Generated `.class` files, `souther-runtime`, and every other module target **Java 25**. The pin
itself is unchanged from ADR-0022: the version is written explicitly and never left to the running
JDK, because that is what makes the floor a decision rather than a property of whoever ran the build.

`souther-runtime` no longer overrides `maven.compiler.release`; it inherits 25 with the rest.

## Consequences

The claim and the artifact agree, and the floor is one number: Souther needs JDK 25 to build, to
generate, and to run what it generated. Raoh, Jackson 3 and jOOQ all sit at or below that, so nothing
in the chain is now the constraint.

`souther-runtime` is no longer held a language version behind the compiler, which is what let it
adopt the Java 22–25 features the rest of the tree already used.

What is given up is a Java 21 consumer, which is a real cost for a library and close to none here:
Souther generates an application's domain model, the same build that generates it needs JDK 25 for
the annotation processor, and the promise was not being kept anyway.

The floor moves again only by decision. `CompileClassVersionTest` asserts major 69 on every generated
class, so a JDK upgrade cannot quietly carry it.

## References

- ADR-0022 (pin the class-file version rather than defer to the build JDK — the principle this keeps,
  with the value moved)
- Specification: `[#target-jdk]`, `[#non-functional]`
