# ADR-0115: A program Souther accepts is one the JVM can emit and run

Status: Accepted.

## Context

`CheckedProgram.of` compiles, asks for the language's verdict, and only then takes the snapshot.

```java
Compilation compilation = Compilation.ofSources(sources, path);
Acceptance.of(compilation);
...
return new CheckedProgram(modules);
```

That order is what stops one output shipping an artifact for a program another output refuses to
build. What it also does, and what nobody had decided, is put the JVM in front of every reader of a
checked program.

`Acceptance.of` drives `Output.All` before it looks at a single row. That is the JVM backend running:
`Backend.generate` calls `JvmLimits.checkParameterSlots` at each declaration, and a class file writer
answers for the rest. Then the rows are evaluated, and evaluating a row is running the module — which
today is running the classes that backend emitted.

Souther has programs the checker has nothing against and that backend refuses. `data Wide` of 128
`Int` fields needs 256 constructor argument slots where a JVM instance method holds 254, and E2101
says so at the declaration; E2102 and E2103 refuse a method too large and a class with too many
constants. Measured through the boundary this ADR is about:

| `CheckedProgram.of` is given | what it comes to |
|---|---|
| `data Wide` of 127 `Int` fields | a snapshot, the product carrying its 127 fields |
| the same declaration one field wider | `CompileException` E2101, and no snapshot |

One field is the whole difference, and it is a count of JVM slots. The language says nothing about
how wide a record may be.

Until #957 the question could not be asked, every output being the JVM's. #971 changed what
acceptance depends on and not what it does — it asks `ProgramExecution` now rather than reflecting
over generated classes itself, and the implementation that answers is the generated JVM program. So
the order still reads `CheckedProgram.of -> Acceptance -> ProgramExecution -> the JVM`, and an output
that is not the JVM's gets its program only after the JVM has had a run at it.

The fact was written down once, in `Acceptance`'s javadoc, and nowhere else. No test held it and no
decision stood behind it, which leaves it reading as an account of how the code happens to be
arranged rather than as something chosen.

## Decision

**A program Souther accepts is one the JVM can emit and run.**

There is one state at this boundary and not two. A program the language checked and a program an
output may be handed are the same program, and it is reachable only through a compile that emits it
for the JVM and runs it there. A program the JVM cannot emit is refused to the author, whether or
not the language had anything against it.

Three things follow from stating it this way rather than leaving it to the arrangement.

**The refusal names the JVM, and that is correct.** E2101 tells the author how many argument slots
their declaration needs and how many one may take. Under this decision that is not the machine
leaking into the language: the language's ceiling *is* the machine's, and the author is being told
which rule they are at. A refusal that hid the reason would leave them with a program the compiler
declines to explain.

**An output that is not the JVM's may emit only what the JVM could have emitted.** This is the
consequence worth stating out loud, because it is a statement about Souther and not about a build
step. A WebAssembly output has no argument-slot limit; it will still never be handed a program that
exceeds one.

**What moves it is evaluation, not this boundary.** The JVM is in front of a reader here for one
reason: a row is decided by running the program, and running it means running one backend's classes.
When evaluating a row stops needing a particular backend, this decision is the one to revisit, and
whether the two states then need separate names is a question to answer then.

Two answers were weighed and rejected.

Naming a `CheckedProgram` and an `AcceptedProgram` introduces a public lifecycle for a distinction
nothing today can observe. The one observable difference it would create — an output holding a
program the JVM build refuses — is what this decides against, so the split would cost a boundary
type to make possible the thing being ruled out.

Deferring the JVM's emit limits until a backend is chosen was rejected for what it would be decided
from. Those limits would have to belong to a chosen backend, and there is one backend to choose;
which of `Backend.generate`'s inputs are the language's and which the JVM's was settled by writing
something that emits (#1065), and the same standard applies here. A second backend that has to have
this reversed is the evidence, and until one exists the deferral would be designed from a reading.

## Consequences

`AnOutputOutsideTheCompilerReadsACheckedProgramTest` says it, beside the case where the language is
what refuses. It compiles the declaration one field under the limit and reads its 127 fields off the
snapshot, so what it holds is that the count is the machine's limit and not a rule of the language —
a test that only showed the wide one refused would pass just as well if Souther had a width rule of
its own.

`Acceptance`'s javadoc now records a decision rather than an arrangement.

Nothing in the compiler changes. The code already gave this answer; what it lacked was a reason to
keep giving it.

The #1065 spike is unaffected either way. Every shape it emitted — whole numbers, truth values, a
behavior body, `if`, a call, a record construction, a composition — is one the JVM can hold, so its
readings were taken through a boundary this never narrowed. A spike written to show a program the
JVM cannot hold coming out of another backend would need this reversed first, and that is exactly
the trigger named above.

## References
- Issue #1066
- Issue #957 (an output outside the compiler reads a checked program), #971 (acceptance asks
  `ProgramExecution`), #1065 (what a backend other than the JVM reads)
- Specification: `[#e2101]`, `[#e2102]`, `[#e2103]`
- ADR-0046 (an `example` row that disagrees is a compile error, which is why acceptance runs the
  program at all)
