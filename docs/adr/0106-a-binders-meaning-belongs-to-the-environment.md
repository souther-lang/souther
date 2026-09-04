# ADR-0106: A binder's meaning belongs to the environment, not to the reader that walks past it

Status: Accepted

## Context

The invariant-discharge check reads a body twice over, for two different questions. The region walk
asks what holds where, and the arithmetic reader asks what a value is as a linear form. Both of them
go inside `let` bindings, because a helper the check expands becomes one: `fee(x)` is inlined as a
binding holding the argument and a body written against it, so almost every binding this check meets
is one no author typed.

Each reader had its own account of what a binder meant. The region walk entered it in `Denotations`,
as what its initializer denotes — a subject, a location where there is one, and a term. The
arithmetic reader did it by substitution: read the initializer as a linear form, then answer the
binder's reads with that form.

```java
case Core.LetIn li -> {
    LinearForm<FactSubject> bound = affine(li.value(), at, leaf);
    yield bound == null ? null : affine(li.body(), at,
            n -> n instanceof Core.Read r && r.binding().equals(li.binder().id())
                    ? bound : leaf.apply(n));
}
```

The two agree on bindings holding numbers and part company everywhere else, because the second is
not an account of meaning at all — it is an account of arithmetic, standing in for one. A binding
holding a record has no form, so `bound` is null and the whole binding, body included, becomes one
opaque value.

That difference is invisible until the two readers stop overlapping, and there is one place where
they do. A reduction's step is read by the arithmetic reader alone: `Terms.recordingWalk` enters the
step's parameters and hands the body to `affineOf`, and nothing else enters anything. So inside a
step the substitution was the only account there was. Measured on five steps differing in one thing
each (#867):

| step of `Yen(List.fold(<step>, 0, xs))` | reported |
|---|---|
| `(acc, i) -> acc + i.n.value` | — |
| `(acc, i) -> { let v = i.n.value ... acc + v }` | — |
| `(acc, i) -> acc + dbl(i.n.value)` | — |
| `(acc, i) -> acc + fee(i).value` | E2011 |
| `(acc, i) -> seven(i)` | E2011 |

Rows three and four differ in the type of the helper's parameter and in nothing else. Row five's
helper body is the literal `7`, which the rule discharges when it is written at the call — so what
was reported was the binding standing in front of the body, not the step.

The naming came apart with it. What the element's type guarantees is recorded at `<element>.n`,
where `<element>` is the walk's own subject for that parameter. The substitution's reading named the
same place `let(<element>, #0.0.n)`, so the fact never reached the atom the step read.

The `leaf` parameter is where the second account lived. It had one external caller, and the only
code that ever handed in a different rule was the `LetIn` case above — an abstraction whose whole
purpose was to let one node interpret a binder for itself.

## Decision

**What a binder means is the environment's answer. A reader that walks past a binding asks for the
environment inside it; it does not work out what the binder denotes, and it does not branch on what
kind of value the initializer holds.**

`Terms.inside(Core.LetIn, Denotations)` is that answer and the only place a `let` is entered. The
region walk's `PathEngine.bindLet` calls it and adds nothing but the knowledge it already had. The
arithmetic reader's `LetIn` case reads the body under it:

```java
case Core.LetIn li -> affineOf(li.body(), inside(li, at));
```

Whether the initializer is a number is not asked. A binding denotes what it was given whatever kind
of value that is, so a helper taking a record binds a record, and the places under the binder are
the places under the record.

Reading through a binding holding arithmetic is unchanged and is not a second mechanism: `givenForm`
already answers a read of such a binder from the environment, and the substitution was doing the
same work a second way.

The affine walk takes no leaf rule. `affine(raw, at, leaf)` and `affineOf(raw, at)` are one method
under the second name, and what was handed in is `leafOf`. This is the load-bearing half of the
decision. Removing the duplicate account fixes today's defect; removing the parameter removes the
place where the next one can be written.

### What was weighed

Reading the body when the initializer has no form, without entering the binder, was the smaller
change and is not a fix. It gets past the bail-out, and a read of the binder still denotes nothing,
so the field under it is named by neither reader's name and the recorded fact still does not reach
it. Half of what went wrong here is the naming.

Entering the expansion's bindings in `recordingWalk`, before the step body is read, keeps the
substitution and adds a third account — scope walked by hand, in a class that would then have to
agree with two others about nesting and about what a binder holds.

## Consequences

All five rows above are silent, and the neighbours that should still be reported still are: the same
helper subtracted from the accumulator is owed, because reading a step is not discharging it.

This settles `let` and nothing else. A `match` handed as a value is read by neither of these two
readers and is a separate gap (#866); every binder-introducing form is a place where this decision
has to be applied rather than restated, and where it has not been applied yet the reader in question
still owns an account of its own.

### Applied to the clause readings

The readings that ask what a declaration's positions admit were such a place. They folded a clause
into one answer carried upward and had nowhere for a binding to be, so a clause under one arrived as
a shape none of them had a word for — and since a helper call is expanded as a binding, that is
every rule an author stated by naming it rather than writing it out.

The fold now hands an environment downward beside the answer it carries upward. `ClauseExpr.Scoped`
marks where that environment changes and composes nothing; `ClauseScope` answers what a binding is
entered as, and for a reading carrying `Denotations` the answer is `Terms.inside`. No evaluator sees
that a binding was there, and none of them holds an environment of its own any more: a leaf is read
at where it stands. `Predicates` reads the body of a binding under the same environment, asking the
same one place for it, though it still recognises the connectives for itself.

A helper-expanded clause is therefore read under the same denotation environment as the equivalent
inline clause. In particular, passing through a helper is no longer a way for a rule to reach an
admitted-values question without any reading recognising its positions.

This does not make every standing question attributable to a rule-level reading failure. A reading
may consume the rule completely and still be unable to construct the exact answer its rules come to
within its allowance; such a loss is about the answer rather than about any rule that paid into it,
and it remains represented separately (`RuleAccounting.Why.NothingTookItIn`, which is where a
question with no reason filed under its rule arrives). A question with neither a rule's account nor
the answer's is the accounting disagreeing with itself and is refused where it is made.

The initializer is now read where a read of the binder asks for it, rather than once before the body.
A binding the body never reads is no longer read at all, which is the intended reading: what a name
was given is part of what the name means, and a name nothing reads means nothing to this check.

Nothing here changes what the procedure may prove. The fragment is the same fragment; what changed
is which values reach it.

## References

- Issue #867 — an expansion binding a value the arithmetic cannot read is one atom
- Issue #1333 — a clause reaching its rule through a helper is read less than the same rule written
  out (this decision applied to the clause readings)
- ADR-0092 — a helper carries the variables its body leaves open (why almost every binding this
  check reads is one an expansion made)
- `[#invariant-discharge-terms]`, `[#invariant-discharge-reduction]`
