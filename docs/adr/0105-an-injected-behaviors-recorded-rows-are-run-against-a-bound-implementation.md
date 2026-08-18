# ADR-0105: An injected behavior's recorded rows are run against a bound implementation

Status: Accepted. Finishes ADR-0088, whose title said why it stopped where it did — *until it can be
run*.

## Context

A model declares the behaviors it does not implement. A repository behavior is injected, its answer
comes from SQL, and the SQL is written in Java long after the model is. Everything else in the model
is held to something: a `let` body is run by its rows, an invariant is checked where a value is
built, a composition is applied as the class it emits. The implementation of an injected behavior was
the one part never held to anything.

ADR-0088 already put the statement in place. A row on an injected behavior is recorded rather than
refused: its arity is checked, its inputs are built through their derived decoders and held to their
invariants, its expectation is held to the output's cases. Only the running was missing.

What running them buys is a way to hold generated SQL to the model. An agent writes `FindTodoImpl`,
and the rows already written for `findTodo` decide whether it answers what the model says it owes.
The reader is not a human reading SQL.

## Decision

**A binding names its behavior through the ABI and its origin through its own classes.** Which
behavior an instance implements is settled by the binary name
`SoutherJvmAbi.nameOf(GeneratedClass.BehaviorInterface(module, behavior))` gives that behavior's
base, looked for in the instance's supertypes — not by taking `FindTodoImpl` apart. There is one
place that decides how a behavior is spelled as a class and it is the one the emitter uses; a second
speller in the binding is a rule restated, and a restated rule goes on answering after the original
moves. Its origin is `Origin.Published` over `ClassFileDeclarations` reading the bound loader's class
resources. Neither is asked of the caller — `bind` takes the instance and nothing else, which is what
makes it impossible to state either wrongly.

The binding answers for the behaviors it implements and delegates the rest to `Answering.generatedHere`.
The resolution is per behavior because a module declares behaviors of both kinds, and one evaluation
applies each as what applies it.

**The API is enumeration and single evaluation.** `rows()` says what the binding makes runnable,
`evaluate(row)` runs one, and nothing here owns the loop. What changes between rows — the world the
implementation answers out of — is the caller's, and the owner of what changes between iterations
owns the loop. A bulk `evaluate()` would own it, and the hooks it would then grow (before, after,
around, transaction, retry, parallelism) are a test framework, which exists. The compile-time run
keeps evaluating in bulk: there the environment is the fakes and the run owns them.

**An evaluation answers with the observation and with what was said about it.** `RowOutcome` is what
a machine decides from and is what an adequacy measure reads, which is what it was designed for. It
is not a test result: a row that failed a comparison carries `FAILED`, `COMPARISON` and both arms,
and where the two values differ inside one arm that says nothing at all — a title read from the wrong
column is the same outcome as a title read from the right one. Answering with the outcome alone had a
consumer report that a row failed while the compiler had the sentence in hand and dropped it. So
`RowEvaluation` is the pair, and a row not handed over says why rather than only where it stopped: a
bulk run says that once for the behavior and every row of it is in one report, while a row handed
over on its own is the only place its reader looks. The language a diagnostic is rendered in is
handed in, because what answers a reader has to say which reader and that is the consumer.

**What is read is a source set and a dependency path, and a lone file is read as a lone file.**
A module may write its rows beside itself and in an `examples for` file, and may import another user
module whose classes a dependency published. A face taking one file and no path would be narrower than the language it stands in front of, and a
project using either would find its rows unreachable rather than failing. Which module the rows are
of is not decided here either: `bind` asks the implementation, so a source set declaring more than
one module is not bound by the order its files were handed over.

A single source keeps its own route rather than being handed to the many-source one: a module
written in one file may leave its `module` header off, and linking several sources needs each to say
which module it is. It is named by its path, so a refusal says the file the reader is looking at.

A model that does not compile is refused with `CompileException`, which carries the positions, the
codes and the sentences the compiler already writes. This is the first thing a caller sees when a
test suite starts, and rebuilding a summary out of codes would hand a reader less than the
compiler's own entrance does.

**`RowKey` holds a `RowIdentity.Named`, is an address, and is not what `evaluate` takes.** Two
things it must be and the type closes both: it holds a `RowIdentity.Named`, so no key exists for a
row that has no name, and it is made only by `row(behavior, name)`, so no key exists for a row
nothing answers to. Left as a record its canonical constructor would be public, a name nothing
answers to would be written straight past the resolution, `is` would answer `false` for every row,
and the setup guarded by it would silently never run — which is the failure the type exists to
prevent. A key is refused by another enumeration's rows rather than answering `false` about them,
for the same reason. `evaluate` takes the enumerated row, so an unnamed row — addressable by nothing
— still runs.

**`Applied`'s third arm is `Bound`.** Not `External`: where an implementation came from is a fact
about a build, and what an arm of `Applied` says is what applied this row. It carries nothing — the
question is which of several things applied a row, not which Java class it was. No measure branches
on it: `hits` answers what this compile's instrumentation saw, and a branch on the applier would make
it answer two questions.

**A crossing failure is filed under a phase named for it.** `INFRASTRUCTURE` was headed "something
the host was supposed to provide was not there" and had one producer, a row whose value could not be
put in the form the answer reads. It is `VALUE_CROSSING`, which is what that producer says of itself.
It is about one value of one row and can happen after `ANSWERER_ESTABLISHMENT` agreed, which is what
keeps the two apart.

**A stand-in's statement is observed, and the verdict is the consumer's.** ADR-0093 compares a `fake`
with the behavior's recorded rows and gives neither precedence; what it cannot reach is a faked
behavior with no rows of its own. Bound, each explicit entry is an input and an answer in the same
form a recorded row is. `observe` answers `AsStated | OtherThanStated | Unobserved(reason)` with no
severity attached: a disagreement on its own still does not say which side is wrong — a fake written
to reach a composite's error path disagrees because that is what it is for — and ADR-0093 already
draws the layer line this way. `Unobserved` is what keeps `OtherThanStated` meaning two values were
compared.

`observe` and not a second `evaluate`, because one adjudicates an obligation and the other relates two
answers, and spelling them apart keeps a consumer from sliding a fake entry into the row default.

**What stands between values and a bound implementation is one thing, asked as one.** Whether
anything applies the behavior and whether what applies it was built against this module are answered
together, as a sealed `Handing`, so a caller that has values to hand over cannot consider one and
forget the other. Asked as two conditions each caller kept, `observe` asked neither: it applied an
implementation `evaluate` was keeping rows away from, and the same binding meant two things
depending on which call was made. An observation runs under the same deadline a row does, for the
same reason — an implementation that does not come back would otherwise hang the caller's loop where
a row's evaluation would have been given up on. The budget is the caller's to set (`withBudget`),
because what a bound implementation waits for is a database or a socket and how long that may take
is not something a compile knows.

**The `apply` that runs is the one the behavior's base declares.** Read off the instance by name and
arity, an unrelated `apply(String debug)` is as good a candidate, and which one ran would depend on
the order reflection happens to answer in. The base is asked instead, which is the same principle as
naming the behavior through the ABI.

**What a `StandinEntry` says about its table is a place.** `Prepared.FakeTable` is a compile-stage
representation reaching `Hir`, and handing it out is an entrance into the pipeline this face exists
to stand in front of. What a caller has a question about is where to look.

**What is not run.** The `_` row states no input. A `with dep = value` states none either. A row
shadowed inside its table is refused by #716 (E1926). And a second `fake` table written for a target
that already has one never stands in for anything — dispatch takes the first — so its entries are not
enumerated. Nothing refuses such a table today; whether the compiler should is its own question.

**What an injected implementation answered is held to what the behavior declares (E1930).** ADR-0104
put the check where an injected answer enters generated code, there being no body to check it in. A
behavior only the application's own Java calls has no such crossing in the compilation at all, so a
row applying a bound implementation is the only place its clause is ever run. Nothing in the
generated surface carries the contract either: an injected behavior's base class is the same class
with a clause and without one.

The answer is brought into this compile's classes before the check runs, and that is load-bearing.
The emitted check guards each rule with an `instanceof` against the class this compile emitted, so an
answer of another loader's classes matches no guard and every rule is skipped — the check would run
and say nothing, for a wrong implementation as readily as for a right one. Out through the neutral
form and back in through this module's own decoder, read at the case the answer turned out to be,
which is the line the Decoder draws for a value arriving from outside.

## What this does not add

No JUnit, no `DynamicTest`, no assertions, no before/after hooks, no database lifecycle,
transactions, environment setup, scheduling, retries or parallelism: the loop and the world are the
caller's. Fixture construction, fake dispatch, arm resolution and comparison stay the ones
`ExampleVerifier` has — no second example semantics. Holding two builds' declarations together stays
#748's, used as it stands. The result is `RowOutcome`; no new test-result model.

Nothing is added to the language. A SQL implementation's real signature is
`(DatabaseState, TodoId) -> (DatabaseState, Todo | NotFound)`, and the hidden input is written
nowhere in the model. It stays that way: a table is an implementation detail, and giving `.sou` a way
to state world state is a much larger change. Setup and teardown belong to the caller, between one
`evaluate` and the next, tied to a row by `RowKey`.

No verified evidence is persisted. A row that `HELD` says this implementation, in this environment,
answered it — which is what a test result is. Persisting it would let an adequacy report say a
behavior is verified while reading a number produced by a build that had a database. An environment
assertion (`delete` really deleted) is the caller's too: a row that held says the behavior answered
what it owed, and nothing about what it left behind.

## Consequences

The source is recompiled at test time, so an implementation is held to the `.sou` as it stands now
rather than to a record travelling with its classes — which is how a model that moved is found out.
Whether the rows could travel as an artifact instead is a packaging question and not a second
language boundary; nothing needs it yet.

This is the first answerer to state anything but `TheCompilesOwn`, so it is also the first thing that
exercises `DeclarationAgreement` in anger. A binding whose declarations and the module's disagree
stops at `ANSWERER_ESTABLISHMENT`, which is #748's answer used as it stands.

A JUnit adapter is a consumer of this face and its own issue, deliberately not built alongside it: an
adapter built together with the core would push what it happens to want into the core, and whether
this boundary is sufficient is exactly what a consumer that cannot reach inside it proves.
