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

**`RowKey` holds a `RowIdentity.Named`, is an address, and is not what `evaluate` takes.**
`RowKey(String, String)` with a checking factory would leave the unnameable case representable; #718
put the namespace on the behavior and this finishes that decision. It is resolved through
`row(behavior, name)` so a name nothing answers to fails at resolution rather than as setup that
silently never runs. `evaluate` takes the enumerated row, so an unnamed row — addressable by nothing
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
