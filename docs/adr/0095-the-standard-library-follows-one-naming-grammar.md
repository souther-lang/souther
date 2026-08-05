# ADR-0095: The standard library follows one naming grammar

Status: Accepted

## Context

The standard library grew a module at a time, and each module took its vocabulary from whichever
language had the closest function. The result reads as four dialects rather than one library. The
sharpest case was the membership test: `List.member` (Elm) beside `Set.contains` (F#/Java) and
`String.contains` — one question, two words, and everything else in `Map` and `Set` was Elm's
`Dict`/`Set` while only that one call had defected.

(`Map.containsKey` looks like a third word for the same question and is not. On a `Map`, "does this
contain it" could ask about a key or a value, so the name has to say — the same reason `Map.map` and
`Map.filter` were wrong. It belongs to the ambiguity half of rule 1 below, not to this defect. The
first draft of this ADR listed it here, which made the document argue both that the name was an
inconsistency and that it was correct; a second draft fixed that by scoping rule 1 to containers with
one kind of element, which then made `Map.fold` the contradiction instead. Ambiguity is the test that
holds for all three.)

`List.fold` (F#) sat beside `List.foldr`
(Elm), a pair that is `foldl`/`foldr` in one language and `fold`/`foldBack` in the other and neither
here. `distinct` (F#) sat beside `allUniqueBy`, two words for one concept, in a `By` family that had
`sortBy`, `groupBy` and `indexBy` but no `distinctBy`.

ADR-0045 had already refused this shape once, for `++` and `+`: a mix matching neither language was
rejected on the grounds that a reader who knows either one is misled. The same argument applies to
every name, and applying it name by name is what produced the drift, because each decision looked
local.

Three things turned out not to be naming problems at all, and were found by asking the naming
question:

- `List.foldr` was documented as "the left fold over the reversed list", and its step was
  `(acc, elem)`. A right fold's step is `(elem, acc)`. The name was for the implementation.
- `Int.modBy(divisor, n)` took its divisor first, for the pipe; `Int.remainder(a, b)` took its
  dividend first. Two remainders in one module, opposite operand orders, and names that do not say
  which rounding each corresponds to — the thing languages actually disagree about.
- `List.range` closes at `to` and `String.substring`'s `to` is exclusive. Same parameter name, two
  conventions, nothing in either name to say which.

`foldFrom`, the recursive helper `List.fold` desugars to, was reachable as `List.foldFrom`. A name a
caller can write is public whatever it was meant to be.

## Decision

**The library follows one naming grammar, and every name that does not is changed at once.** The
grammar is nine rules:

1. A basic operation shares one name across containers: `map`, `filter`, `fold`, `contains`. Where a
   container gives an operation more than one thing it could mean, the name says which — a `Map` has
   keys, values and entries, so `containsKey`, `mapValues`, `filterEntries`. The test is ambiguity,
   not the number of parts: `Map.fold` necessarily consumes the whole entry and answers neither a key
   nor a value, so there is nothing for a reader to guess and it keeps the shared name.
2. Where a term is settled across several major ecosystems with the same meaning, that term wins:
   `flatMap`, `filterMap`.
3. A derived operation with no settled term is named so it can be predicted from the family it joins:
   `mapIndexed`, `distinctBy`.
4. Where the ordinary result differs between languages, the difference goes in the name:
   `floorMod`, `truncatingRemainder`, `rangeInclusive`, `zipShortest`.
5. Failure goes in the return type, not into a suffix like `OrAbort`.
6. A unary operation takes its subject last (the pipe convention, ADR-0034). A binary one keeps its
   operands in the order the mathematics writes them, and any policy argument follows them.
7. Extracting a range is half-open; generating a closed one says `Inclusive` in the name.
8. An implementation helper is not published.
9. A change to a name, a type and a meaning is one change, not three.

Rules 2 and 3 are ordered deliberately: the earlier draft of this grammar said "the basic operation
first, the modifier after", which produces `mapIndexed` and also produces `mapFlat`, and no one
writes that. What actually decides is whether a term is already settled. The rule is written that
way so the next name added is decided the same way, and the vocabulary it decided is listed below so
a reader can check a new name against it rather than against a rule alone.

| Word | What it means here |
| --- | --- |
| `map` | transform each element one-for-one |
| `mapIndexed` | transform using the index and the element |
| `flatMap` | transform each element to a list and flatten one level |
| `filterMap` | keep only the results that are there |
| `contains` | is this value in here — of a container with one kind of element |
| `containsKey` | is this key in here — the `Map` form, since "contains" alone could mean a value |
| `fold` | combine from the head; `List.foldRight` combines from the end |
| `XBy` | X, under a projection or key function |

### What changed

| Was | Is |
| --- | --- |
| `List.member` | `List.contains` |
| `List.indexedMap` | `List.mapIndexed` |
| `List.concatMap` | `List.flatMap` |
| `List.allUniqueBy` | `List.allDistinctBy`, beside a new `List.distinctBy` |
| `List.range` | `List.rangeInclusive` |
| `List.zip` | `List.zipShortest` |
| `List.foldr(step: ('acc, 'a) -> 'acc, …)` | `List.foldRight(step: ('a, 'acc) -> 'acc, …)` |
| `List.foldFrom` (public) | `private let foldFrom` |
| — | `List.append`, the named form of `++` |
| `Map.map` | `Map.mapValues` |
| `Map.filter` | `Map.filterEntries` |
| `Map.update` | `Map.updateIfPresent` |
| `Map.upsert` | `Map.updateOrInsert` |
| `Map.intersect` / `Set.intersect` | `Map.intersection` / `Set.intersection` |
| `Int.modBy(divisor, n)` | `Int.floorMod(dividend, divisor)` |
| `Int.remainder` | `Int.truncatingRemainder` |
| `Decimal.toInt(d, mode)` | `Decimal.toInt(mode, d)` |
| `Decimal.round(d, scale, mode)` | `Decimal.round(scale, mode, d)` |
| `String.substring` | `String.slice(fromInclusive, toExclusive, s)` |
| `String.toChars` | `String.characters` |
| `String.toCode` | `String.codePoints`, and no "first code point" at all |

`List.fold` keeps its name rather than becoming `foldLeft`. `Map` and `Set` publish no first and no
last element, so there is no left there for a right to be the counterpart of; naming List's
`foldLeft` would have made `Map.foldLeft` the consistent choice, which claims a direction the
contract does not give, and leaving `Map.fold` beside `List.foldLeft` would break rule 1 in the
direction that matters — a reader who learns one and writes the other on a set.

`List.foldRight`'s implementation did not change. It is the left fold over the reversed list with the
step's arguments swapped, which *is* the right fold: Souther is strict and lists are finite, so the
two orders of combination give the same value. Only the name, the step's type and the argument order
changed. It is O(n) time and O(n) extra space, which is stated in its doc comment because it is a
property a caller can observe.

`String.toCode` is gone rather than renamed to `firstCodePoint`. It was the only function in the
library with a sentinel return (`-1` for the empty string), and a `firstCodePoint : Int?` would have
kept "the first one" as a concept the library has an opinion about. `codePoints` is total, and a
caller who wants the first takes it with `List.get(0, …)` — the absence comes from where every other
absence in the library comes from.

### The one exception, stated as one

`Int.floorMod(dividend, divisor) : Int` aborts on a zero divisor. Rule 5 says failure goes in the
type, and this is the only place in the library it does not.

- **Why**: `floorMod` is written in invariants (`invariant Int.floorMod(value, 12) == 0`), and an
  invariant is a Bool expression that cannot take `Int | DivisionByZero` apart. A plain `Int` is what
  makes the invariant writable. The reason is the language's current expressiveness, not convenience.
- **Not a precedent**: no standard-library function added later may leave its failure out of its
  type on the grounds that `floorMod` does.
- **How it is resolved**: by a `%` operator that aborts, leaving `floorMod` to return the union
  (Souther already draws that line — `/` aborts, `Int.divide` returns the case); or by a non-zero
  divisor type the parameter can require; or by invariants being able to discharge a `DivisionByZero`
  member. Whichever arrives first, this exception is reconsidered then. A `%` operator was not added
  here because operator design is not naming, and mixing them would have made this change unreadable.

`Int.truncatingRemainder` sits beside it returning `Int | DivisionByZero`, so the rule and its
exception are visible in the same module.

### No compatibility aliases

An old name is not kept as an alias, and not kept as a rename hint in a diagnostic either. Two
spellings for one operation is the state this ADR exists to end, and a hint table is a second list of
the old vocabulary to maintain. An old name gets the ordinary "the library has no such member"
report.

### The surface is written down

`ThePublishedSurfaceIsFixedTest` holds a snapshot of every published qualified name with its
parameters and types. A rule about words is enforced by reading, and nothing reads on every commit; a
snapshot makes any addition, rename or reorder fail, and the diff is the whole surface, which is the
form in which a new name can be judged against its neighbours.

## Consequences

The change is not source-compatible, and deliberately so. Every `.sou` file in this repository and in
`souther-examples` was rewritten with it. Anyone else's code breaks at the call site with a "not a
standard-library function" error naming the call — a compile error, never a silent behaviour change,
because no old name still resolves.

Two argument-order changes are the exception to that and deserve care: `Int.floorMod` and
`Decimal.round`/`toInt` take the same types in a different order, so a call that was not updated may
still compile and mean something else. `Int.modBy(12, n)` becoming `Int.floorMod(n, 12)` is the one to
look for. The rename from `modBy` catches it — the old spelling does not compile — which is part of
why the argument-order change was made together with a name change rather than on its own.

`private` is new syntax, in the reserved namespace only. `Ast.FnDef` carries an `Ast.Modifiers`
record rather than two adjacent booleans, and `Prelude` answers "does this name exist" and "may this
name be written" separately: the checker and the backend still see `List.foldFrom`, and resolution
refuses it for every module outside `souther.*`. Refusing it at resolution rather than at the type
check is what lets the inliner keep injecting the call — the injected tree never goes through
resolution.

A rule in `InvariantChecker` and `TotalityChecker` keyed on `List.foldRight` had to move its element
parameter from index 1 to index 0, because the step's arguments swapped. The test that fires every
combinator rule caught it. That is the shape rule 9 is about: the name, the type and the meaning
moved together, and a change to one of them without the others would have left a rule reading the
accumulator as the element.
