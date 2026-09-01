# ADR-0111: An environment answers with the value a name denotes, never with the form a reader makes of it

Status: Accepted

## Context

One walk reads an expression as `const + Σ coef·atom`, and two readers use it. The
invariant-discharge check reads a clause this way to discharge it, over atoms of its own; the
adequacy measure reads a rule this way to find the line it draws, over the positions of a behavior's
input. `AffineForms` is that walk, and what each reader answers for itself is what its environment
knows.

The measure's leaf asks `InputPath` which position an expression names. That question has a position
or nothing for an answer, and a name given arithmetic over a position is neither.

```souther
let f (t) = if t.value + 10 < 240 then Low else High          -- borders 3, a line at 229/230
let f (t) = { let v = t.value + 10                            -- no axis, no line, nothing said
              if v < 240 then Low else High }
```

One null leaf makes the whole form null, so the second spelling reported the newtype's own ends and
nothing else. Nor did anything say so: the walk that says which positions a rule mentions stops at a
name too, a read having no children, so the reason a rule went unread had no rule to be about. An
author is told the model draws no line there.

The check side did not have this defect, because it could reach what a name was given. `givenForm`
answered a read of such a binder from the environment and read what it found as arithmetic. So one
walk was shared, the ability to walk through a name was written into one of its two callers, and a
rule the check enforced was one the measure reported as unread — which is the failure `AffineForms`
was made to remove, one level in from where it was removed.

Putting the reading back has an obvious shape and a dangerous one, and they differ only in what a
caller is allowed to answer with. ADR-0106 removed this walk's `leaf` parameter and said that
removing the parameter, not just the duplicate account, was the load-bearing half: a caller that can
answer with a `LinearForm` can keep an account of the arithmetic beside the walk that has one, and
inside a reduction's step that weaker account was once the only account there was.

## Decision

**An environment may answer with the `Core` a name denotes. It may never answer with the
`LinearForm` a reader makes of it. Affine interpretation of that value, and the termination of
chained reads, belong to `AffineForms` alone.**

The extension point is `AffineForms.Reading.readThrough`, and its codomain is the whole of the
decision:

```java
record ReadThrough<E>(Core value, E at) {}

ReadThrough<E> readThrough(Core.Read read, E at);
```

A caller can say which value stands where a name stands. It cannot say what the arithmetic of that
value comes to, so there is nowhere for a second account of the arithmetic to be written. The walk
reads in three stages — what the language composes, then what a name denotes, then what the caller
calls the value — and the middle one is neither of its neighbours: whether a name may be read
through is the environment's answer and not a rule of the grammar, and a leaf is what is left when
nothing can be read.

The environment travels with the value. A value stands for the name in the environment the binding
was made in, which is not always the one the name was read in; answered without it, each consumer
supplies one, and two consumers that supply different ones are two accounts of what the name means.
Today the two cannot be told apart — a binding tells itself from every other and the environment only
grows on the way down — and what makes that one fact rather than a coincidence two readers rely on is
that it is settled where the name is given its meaning.

`Leaves` is `Reading`. What a caller answers has not been only what a leaf is since it began
answering what lies inside a binding.

### What the input reading answers

A name stands for one of four things, and three of them were being folded into one `null` on the way
out although the data held them apart.

| the name | what it stands for |
| --- | --- |
| a parameter, or `let v = t.value` | a position of the input |
| `let v = t.value + 10` | the expression it was given |
| `n` in `filter(n -> …, map(p -> p.age, xs))` | an element an operation handed out |
| anything else | nothing this reading knows |

These are facts about the name and not permissions. Whether the expression may stand where the name
stands is the reader's to settle from the fact: the arithmetic reader substitutes it, the reader
collecting positions walks into it, and neither is the other's rule. Both ask one place which of the
four they have, so the line a rule draws and the reason it could not be drawn come from one reading
of one name.

### What was weighed

Answering the measure's leaf directly is five lines and closes the issue. It also puts a second copy
of the read-through beside `givenForm`, which is the shape that produced the defect: the second copy
of a shared reading reads fewer shapes than the first, and nothing says when it has fallen behind.

Reading what a binding holds straight out of the environment, without asking what the name is, was
measured. `List.filter(n -> n >= 18, List.map(p -> p.age, people))` binds `n` to what the expansion
wrote for the mapped element, and following it reaches `people[*].age` — a line at a position whose
values are not the ones the rule is about, which an author cannot tell from a line their model
states. That is why the answer is what a name *is* and not what its binding *holds*.

A `boolean` on the input reading, saying whether a name may be read through, would have served both
consumers and named a conclusion of theirs rather than a fact of its own. The reading knows that a
name is an element an operation handed out; that reading through it is wrong for arithmetic is what
follows.

## Consequences

The check's policy is unchanged. What moved to the shared walk is the traversal; which names the
check treats as transparent is still `computesAsWhatItWasGiven` together with the value carrying a
number, and a name given a value written in the source is still followed by `writtenValue` wherever
the name denotes it. ADR-0106's text names `givenForm`; that method is now `Terms.readThrough` and
answers rather than reads.

Chained reads end in one place. A name is read through once on the way to a form and lifted again
once it is behind the walk, so a form adding one name to itself reads both of them and a chain that
could come round does not.

A rule an author wrote is now reported where it used to be silent. The conformance corpus's
`discount` binds `cut(item.price, rate)`, which multiplies two positions, and the guard over the name
is a rule about both of them that this does not model — two `partition_not_read` findings where there
were none. No line is drawn that was not drawn before.

Which of a position and an element wins where a name is both is one place's, and the decision above
says which place: a reader answers from what a name **is**. For a named-position reading an element
binding is interpreted through its container before any value the lowering happens to bind to the
same binding, and that route failing is a semantic "no position" rather than permission to read the
binding through what it holds.

Four models were measured here with the two swapped and none of them changed, and that was read as
there being no control to write. The measurement was right and the reading of it was wrong: none of
the four held a binding that was at once an element an operation handed out and bound to a value, so
none of them could tell the two orders apart. Joining two walks into one produces exactly that
binding — the second walk's element is bound to what the first walk's closure made — and a model
holding one distinguishes the orders. What was missing was not a control but a model with the
discriminating shape in it.

`InputPath` had not applied the decision. It read the facts itself and raced them, taking what the
binding holds first and falling back to what it is an element of, and on such a binding the race is
won by the value the rewrite left under the name. What kept the wrong road shut was the shape at the
top of it: a `let` came back as something the reading did not follow, and a fused closure body is a
`let` — as is every binding a helper expansion writes, which is why a claim written through a helper
was about a position that reading could not name. Both are gone: the environment answers what a
binding is and hands out nothing to re-order, and an expression that binds a name is read under it.

This settles the reading of a name in the affine walk. Every other reader that meets a name is a
place to apply the decision rather than restate it, and where it has not been applied the reader in
question still owns an account of its own.

## References

- Issue #933 — a name bound to arithmetic over a position names no position
- ADR-0106 — a binder's meaning belongs to the environment (what this specialises)
- Issue #836 — a body that binds its input before comparing it compares its input
- Issue #867 — an expansion binding a value the arithmetic cannot read is one atom
- Issue #1211 — the model that tells the two orders apart, and the reader that had not applied this
- `[#invariant-discharge-terms]`, `[#boundary-coordinates]`
