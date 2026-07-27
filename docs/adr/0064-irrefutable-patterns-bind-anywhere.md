# ADR-0064: An irrefutable pattern binds wherever a name binds

Status: Accepted. Supersedes the lambda-parameter consequence of ADR-0036.

## Context

Souther had three ways to open a value and no rule connecting them. `match` opened a sum's case, a newtype's constructor (ADR-0054) and a record's fields; `let (a, b) = t` opened a tuple and nothing else (ADR-0036); `.value` read one newtype layer (ADR-0014). Which one applied was a fact about the form, not about the value, and a reader had to know all three.

The gap showed when a newtype wrapped a collection (`data タグ集合 = Set<タグ>`). Naming a collection puts `.value` between every use and the collection, and the destructuring that would have removed it was available only in `match` — which needs a sum to match on, so a bare newtype had no way to be opened by a pattern at all.

The obvious alternative was to make the wrapped value reachable without opening it: accept `タグ集合` wherever `Set<タグ>` is expected, so `Set.size(tags)` would work. That was rejected. It reads as one rule and is not one: `List.filter` closes over the newtype and could return it, `List.map` changes the element type and cannot, so what survives an operation becomes a per-function fact. The invariant is worse — either it silently stops applying after the first operation, or a re-wrap runs it at points the code does not show. This is the transparent-deref direction ADR-0054 already declined, widened from operators to the whole library.

What can be said as one rule is refutability. A pattern that every value of the type satisfies can be written where exactly one arm is available, because there is nothing to fall through to. A pattern that some values fail needs the arm that catches them, which is what `match` is.

Both languages Souther grounds its surface in already draw the line there. Elm and F# both admit a single-variant constructor, a tuple and a record's fields in a `let` and in a parameter, and both require `case`/`match` for a multi-case type.

## Decision

**An irrefutable pattern — a name, a tuple, a newtype opened by its constructor, a record's fields — may be written wherever a name is bound: a block's `let`, a behavior implementation's parameter, a helper's parameter, a lambda's parameter. A refutable one — a sum's case, `Some` — stays in `match`.**

```
let タグ集合(ts) = 集合
let { 名称, 数量 } = 明細
let (k, v) = 対

let 個数 (タグ集合(ts)) = Set.size(ts)

List.map((タグ集合(ts)) -> Set.size(ts), 集合たち)
```

Refutability is judged on the resolved name, not on the spelling, since only the name's declaration says whether a value can fail to have the shape. Opening something that is not a newtype is refused, and the report points at `match`.

Outside `match` the name a constructor pattern writes is also held against the value's own type. A `match` arm's name is one of the scrutinee's cases and the exhaustiveness pass has already established that; a binding names a type on its own authority, and without the check `let Labels(xs) = t` would read `.value` off a `Tags` under the wrong nominal type.

A lambda's parameter list and a tuple keep ADR-0036's reading: `(a, b) -> e` is two parameters. A single tuple parameter is written with its own parentheses, `((a, b)) -> e`. What changes is that the parameter list is now recognised by its closing `)` being followed by `->` rather than by containing only identifiers, since a parameter is no longer only a name.

## Consequences

- The rule replaces three unrelated ones. Where a value is bound, what it is made of can be opened; where a value might be one of several things, `match` says which.
- ADR-0036's consequence that "to open a tuple inside a lambda you take one parameter and `let (a, b) = p` in the body" no longer holds — `((a, b)) -> e` opens it in the parameter.
- A helper's parameter written as a constructor pattern needs no type annotation beside it: the pattern already names the type. On a behavior's implementation the same pattern is not an annotation at all — the parameter types come from the behavior, and the name the pattern writes is held against the input the behavior declared.
- The lowering is the one `match` already does — a fresh binder plus the reads the pattern stands for. No Core node, no type-checker rule beyond the two judgements above, no codegen. The parser gains a pattern grammar, which it did not have: every pattern-ish form used to be hand-rolled inside the node that needed it.
- Recognising a parameter list by the arrow after its `)` makes a parenthesised value written immediately before an arrow ambiguous with it. That happens in one place, an example row's `with` value, where the arrow belongs to the row; the row wins. The narrower lookahead had the same hole for an all-identifier value and lost it silently.
- `.value` is still the single-layer accessor. This ADR gives it somewhere else to be written, not a replacement.

## References

- Specification: `[#blocks]`, `[#tuple]`, `[#match]`, `[#fn-declaration]`
- Related: ADR-0054 (the constructor pattern in `match`), ADR-0036 (tuples, the parameter-list reading), ADR-0014 (the newtype and its `value`), ADR-0032 (construction `X(v)`, whose inverse the pattern is)
