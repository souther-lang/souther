# ADR-0098: An unmarked helper may not reach a `partial` helper

Status: Accepted. Amends ADR-0052.

## Context

ADR-0052 states the guarantee as "User recursion is total unless explicitly `partial` ... This is Souther's totality guarantee". What the compiler proves is narrower. `TotalityChecker` analyses the strongly-connected group of the recursion under test and nothing else, so a certified helper may call a `partial` one off its cycle:

```
partial let spin (n: Int): Int = spin(n)
let depth (t: Tree): Int =
    match t.child with
        | Some c -> depth(c) + spin(t.n)
        | None -> 0
```

`depth` descends structurally, is certified, and does not terminate on any tree with a child. The same gap reaches an invariant, which runs on every construction and is meant to be a computation that always finishes: inlining leaves a recursive helper standing, so a `partial` helper behind one is not visible in the clause and nothing else looks.

The word itself was ambiguous, which is why the gap was easy to leave open. The specification's own illustration of `partial` was `firstOver`, a linear search over a list written with `List.get` and `List.drop` — a function that always terminates and that `List.find` already does. What that helper disclaims is not termination; it is the proof. A recursion the size-change closure exceeds `MAX_CLOSURE` on is the same case. Read as "may loop", `partial` is wrong about both of them; read as "the compiler is not answering for this one", it covers all three.

The corpus settles the cost. `souther-examples` and the shipped core contain no `partial` declaration at all — every module that could have needed one is written the other way round, and the READMEs say so. Propagating the word costs nothing there today.

## Decision

**`partial` declares that the helper does not carry Souther's termination guarantee.** It does not assert that the helper diverges. What it disclaims is the termination guarantee and nothing else: the helper is type-checked, its `match` is checked for exhaustiveness, and its invariants hold as any other's do. Size-change termination is the method the guarantee is currently established by, not what the word means.

**A helper's totality covers everything it reaches.** An unmarked helper may not reach a `partial` one, directly or through any chain of calls; doing so is `E2001`, reported at the helper's own name and naming the path. This is Idris2's rule — a `total` function may not call a partial one — and it fits the existing asymmetry that `partial` only disclaims and nothing claims.

- Every member of a mutually-recursive group holding a `partial` member needs the word, because each reaches the others. ADR-0052's "a `partial` member opts its whole group out" stays true of the size-change analysis and is no longer an exemption from saying so.
- Reading a `let` written with no parameter list is reaching it: the value is substituted where it is named, so its body runs there.
- One report per helper, so a module needing the word in several places is told about all of them in one build.

**A behavior's implementing `let` is not a helper and publishes no termination guarantee**, so the rule is not asked of it: it may call a `partial` helper. This is not a boundary the walk stops at — it is a declaration the walk is never asked about, which is what `HelperInliner.helpersOf` already says by excluding behavior names. A helper between the behavior and the `partial` one still needs the word.

**A `partial` helper may be applied but not named where a value goes.** A function type says nothing about termination, so a `partial` helper stored in one leaves the call graph and arrives where the walk cannot see it. Colouring the function type instead — a total form and a partial form, every higher-order signature picking one — would say it precisely and is rejected here, on scope rather than on correctness: it reaches every higher-order signature, the relation between them, inference, and what a jar carries of them, for a hole the corpus closes by not writing the name. If higher-order partiality is ever a requirement, that is the design to reconsider.

**An invariant is decided by what it reaches**, not by what inlining left visible in the clause. The same walk answers both questions, so the invariant and the helper above it are reported in one build rather than one per fix.

**Across a module boundary the answer is the word on the declaration being called.** A published helper's body travels as source, but the reader does not walk it: an imported helper written without `partial` promises that nothing it reaches is `partial`, because the module that published it was held to the same rule. That promise is what `Backend.BOUNDARY_VERSION` records, moved 5 → 6; a jar built under a different one is refused rather than believed.

## Consequences

- "An unmarked helper carries the termination guarantee" holds for every helper, including across a module boundary. Before, it held only inside a recursion's own strongly-connected group.
- An invariant reaches only declarations that carry the guarantee, which is what makes it a computation that always finishes.
- `partial` becomes meaningful on a non-recursive helper, where it previously said nothing.
- The word spreads along every call chain out of a `partial` declaration, up to the behavior that calls it. That is the honest reading of what is being disclaimed. It costs nothing in the corpus, which has none; it costs a word per helper in a module that has one.
- A jar built by an earlier compiler is refused. It carries unmarked helpers that were never held to this rule, so reading the word off them would be reading a promise nobody made.

## References
- Specification: `[#fn-rules]`, `[#invariant-expressions]`, `[#e2001]`
- ADR-0052 (recursion is total by default — amended: the guarantee covers what a helper reaches)
- ADR-0072 (a published body travels as source — why the word crosses a jar)
- ADR-0076 (function types — why a `partial` helper may not be handed over as one)
- Prior art: Idris2 (`total` may not call `partial`); Dhall (total by construction, no escape)
