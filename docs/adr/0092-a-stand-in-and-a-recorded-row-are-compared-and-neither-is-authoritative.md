# ADR-0092: A stand-in and a recorded row are compared, and neither is authoritative

Status: Accepted. Builds on ADR-0088, which made an injected behavior's `example` row a recorded
statement rather than an error.

## Context

ADR-0088 made a row on a behavior with no `let` a record of what that behavior will owe. A `fake` for
the same behavior is a second, independent statement about what it answers: it stands in for the
behavior while some *other* behavior's row runs. Before ADR-0088 the two could not coexist — a row on
an injected behavior was refused — so nothing had to be said about them together.

They can now contradict each other, and the compile is clean when they do. Worse than silence is what
the adequacy report then says. It reads the fake, not the rows, so it reports an arm as one no row
goes through while the model's own record says a row reaches it. An author following that report
writes a row that already exists.

This is not a rare shape. Every faked behavior in the examples repository is injected, and harvesting
a legacy system's answers into rows on exactly those behaviors is what ADR-0088 was for.

Two things had to be settled before this could be reported at all.

**What a stand-in answers for an input.** A fake's table is not a list of independent claims. It
dispatches: the first row stating the arguments, and otherwise the `_` row. A check that compared
row-for-row instead would report a contradiction where the fake would have picked an explicit row,
and stay silent where the fake would have fallen through to its default — which is the same class of
mistake this diagnostic exists to catch.

**Which stand-ins can be compared at all.** A fake row states its own inputs, so a recorded input
picks the row that answers it and nothing is evaluated in between. A `with dep = value` states none.
It does ignore its inputs, but that is a fact about the function it installs, not about which of the
dependency's inputs it was written for: what reaches the dependency is whatever the parent behavior
computes and passes — a normalised field, one of two branches, one of several calls — and reading
that means running the parent. So a `with` is a fixture bound to the run of one row, not a statement
about the dependency, and the two are not the same kind of thing however alike they look at the
injection point.

**Which of the two is right.** A migration may deliberately run a behavior against a stand-in while
the real answer is still being harvested. Nothing in the text tells that from a mistake. Holding the
fake to the recorded rows would make a fake a derived thing rather than a written one, and that is a
much stronger claim than reporting the disagreement needs.

## Decision

1. **A stand-in and a recorded row are compared, and neither is given precedence.** Both are written
   statements about what one behavior answers. What is reported is that they disagree and where each
   is written.

2. **Each side is read the way it is read where it is used.** The rule that picks a fake's row is the
   fake's own — the first explicit row stating the arguments, and otherwise the `_` row — and the
   table it dispatches on is built once, whole, and shared with the proxy the example runner builds.
   A table's default is therefore what a recorded row is held against wherever no explicit row states
   its input, and a table with a row that will not build answers nothing, because it is a table no
   fake can stand in with. A recorded row is read the way the evaluator reads it: arity, inputs
   against their parameter types, expectation against the output's cases and then built. A side read
   otherwise here than there would be held to an assertion the model itself refuses.

   The case a comparison turns on is the one the text names, resolved to the type it denotes. The
   class a value arrives in is a different thing — it does not tell one module's case from another's
   of the same name — and it is what the evaluator compares a *result* against, which is a comparison
   between a text and a run rather than between two texts.

3. **A row-local `with dep = value` is compared with recorded rows only when `dep` takes no input.**
   For a dependency that takes inputs, the `with` does not identify which dependency input is
   answered without evaluating the parent behavior, so no written-statement disagreement is reported.
   A dependency taking nothing has one input, `()`, so there the two are about the same call. A
   `with` takes precedence over a `fake` table while its own row runs; that is dispatch and it settles
   nothing here, since the table remains a statement written for every other row and every other run.

4. **The diagnostic is a warning, and it does not belong to adequacy.** Nothing is counted, no second
   compile is needed and no behavior is applied, so the adequacy dial has no say over it; what it
   costs is building the fixtures on both sides and comparing them. Building one runs the helpers it
   applies (ADR-0077), so the reading is held to the same budget a row's evaluation is.

One disagreement is reported at both of its statements, each in the file it is written in. A
diagnostic quotes one source, and the two statements need not be in one: a module's fakes are what its
attached files' rows run against and the other way round.

## Consequences

An author is told which two lines contradict, and is left to decide which one the model is to keep.
Neither is rewritten and neither is refused.

Some genuine disagreements go unreported: a `with` on a dependency that takes inputs may well
contradict a recorded row, and where the parent behavior passes a field straight through, a reader
can see which. Deriving it needs call-site or evaluation-aware analysis, which is not what this check
is. The false negative is deliberate and preferred to the alternative, because the warning cannot be
turned off: comparing every `with` against every recorded row reports a model that agrees with itself
as contradicting — two rows faking two answers for two different inputs, each right about its own —
and a warning that fires on correct code is worse than one that misses. Two things would make the
input readable and the comparison sound: a `with` that names the input it answers, or a check driven
by what the parent row's run was observed to ask for. The second is no longer a comparison of two
written statements, and would be its own diagnostic.

Making this an error would need a policy this ADR does not set: that one of the two carries the
model's contract and the other is checked against it. Until such a policy exists, a build that stopped
here would demand a fix the compiler cannot name — in a migration, the fix it would force is deleting
the harvested record ADR-0088 exists to keep.

The count is one warning per pair of contradicting statements, doubled by being said at both ends. A
fake whose default disagrees with many recorded rows produces one pair per row. If that proves too
loud, the aggregation is a change to how disagreements are projected onto diagnostics and not to what
counts as one — the comparison already yields a source-independent set that the reporting reads.

Reporting at both ends is what the current diagnostic model allows: a secondary region carries a
position and not a source, so a second caret cannot be placed in another file. If secondary regions
gain source identity, the two projections collapse into one diagnostic with a cross-source secondary,
and nothing about the comparison changes.
