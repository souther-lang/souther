# ADR-0079: A composition carries an example

Status: Accepted. Takes up the scope note ADR-0046 left open for `>->`; ADR-0048 already took up the
one for a dependency-taking target.

## Context

ADR-0046 made `example` a compile-time-checked row on a behavior and left two targets out of scope: a
`>->` composition and a pure helper. E1902 has refused a composition since, on the stated grounds that
it "has no in-language implementation to evaluate".

That reason was not true. A composition's implementation is its own emitted class: the stages applied
in order, with a case the next stage does not accept branching to the end rather than being offered
onward. Normal execution applies that class, and so does `souther run`. Nothing about it is missing at
compile time.

What the refusal cost is visible in the crm model of souther-examples: `disqualifyAndNurture` and
`closeAndSummarize` are the two units the business names, and they were the only two pinned by a
hand-written JUnit test rather than at compile time (finding F4).

The gap it leaves is not a duplicate of what a stage's example already states. A row on a stage states
that stage's rule. What a case leaving the main line means for the composition's output — that
`closeWon`'s `BelowFloor` is an outcome of `closeAndSummarize` and never reaches `summarizeWin` — is
not any stage's rule, so no stage's example can state it. It is the composition's, and until now it had
no compile-time statement at all.

Measured before deciding: lifting the refusal and running the composition's own class covers every
shape the corpus has — a multi-input first stage (`closeAndSummarize` takes three), a case retired by
that first stage, a named intermediate composition (`whole = half >-> file`), a stage's dependency
faked by a `with` or a `fake` table, an injected first stage, and a dependency two stages share. None
of them needed anything the verifier did not already do.

## Decision

**An `example` may target a `>->` composition.** It is evaluated by applying the class its module
emits — the same class normal execution applies — so the stages run in order and the routing is the
routing, not a second implementation of what `>->` means that could disagree with the first. E1902
keeps one reason: an injected behavior, which you fake rather than example.

A row is written as any other row is. Its arguments are the first stage's, since that is the
composition's input, and its expected result is any case of the composition's output, including one
that departed the main line upstream.

**The fake rule is unchanged.** A composition's dependencies are the union of its stages' (spec
`[#composition-with-requirements]`), and each of them is supplied by a fake at the example, as a
behavior's own dependencies already are. Whichever path a row takes: an input that departs at the first
stage never reaches the second, and the second stage's dependency is faked all the same. What a row
must supply is a property of the composition and not of the input this row happens to use, so adding a
`guard` to a stage does not change which fakes the rows around it need. A dependency two stages share
is one fake, because the composition holds one field for it.

**What each behavior takes injected is one question, answered once.** The emitter used to work the
requirement set out privately, and an example has to pass its fakes in exactly that order. Two walks of
the stages that agree today would bind a fake to the wrong parameter the first time one of them
changed, and neither side would report anything — the fake would simply stand in for the wrong
dependency. So it is a query both read: which dependency, from which stage, in which order. A
requirement carries its requesters, which is also what lets E1908 name the stage that wants a missing
fake instead of naming only the composition.

## Consequences

Issue #164 closes. The two most business-meaningful units of the crm model can be stated at compile
time, and the hand-written test that stood in for them is no longer what pins them.

No new evaluator is introduced, and no new syntax. A row on a composition reads exactly like a row on a
behavior; what changed is which targets are evaluable.

The order a composition's fakes are passed in is now checked by the tests through a stage-distinguishing
row: two stages with different dependencies whose fakes, if swapped, would produce the other stage's
value.

E1902's hint no longer claims that an example runs a behavior "that depends on nothing" — a claim the
next sentence of its own specification entry contradicted, since ADR-0048 made a dependency something a
fake supplies.

## Amendment (issue #1108)

This ADR recorded a limit that was not the language's:

> A composition whose stage names an imported injected behavior is not example-able, for the reason a
> behavior depending on one is not: a fake stands in for an injected behavior of the module the
> example is written in. That limit is inherited, not introduced here.

That is withdrawn. It was an implementation's shape written down as a decision. `depends on` names a
behavior declared here or imported (spec `[#depends-on]`), the check and the emitter carry a
requirement as the declaration it is, and only the rows identified it by the bare spelling an author
wrote — so a requirement carried across a module boundary could be declared and emitted and never
run, and where a namesake was declared beside it, that namesake's table was installed in its place
and the row aborted casting one module's value to another's.

**What each behavior takes injected is one question** is the decision this amends, one rung further
in: *which behavior* a requirement is, is also one question. A `fake` and a `with` name it the way a
`depends on` clause names it, resolved once, and what the compiler carries from there is the
behavior and not the characters. A row of such a table is held to what the declaring module states,
by the check that module emitted.

The composition case follows without a rule of its own, as it did before: a composition's
dependencies are its stages', and a stage may name an imported injection target.

## References

- Specification: `[#example-evaluable]`, `[#example-fakes]`, `[#e1902]`, `[#e1908]`,
  `[#composition-with-requirements]`
- ADR-0046 (`example`), ADR-0048 (`fake`), ADR-0024 (a composition's declared output)
