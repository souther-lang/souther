# ADR-0071: The departure statement is `guard` and the dependency clause is `depends on`

Status: Accepted

## Context

Two reserved words differed by one character and named nothing in common. `require <cond> else <value>` is a statement inside a `let` body that departs with a domain value (ADR-0020). `requires <name>` is a clause on a `behavior` signature listing the injected dependencies its implementation receives as trailing arguments (ADR-0016). One is about a branch, the other about wiring, and a reader had a single letter to tell them apart.

Neither word said what it meant either. `require` is Eiffel's precondition keyword and `requires` is Dafny's and JML's, and in that tradition a violated precondition is the caller's fault and the routine promises nothing. ADR-0003 decided the opposite: a precondition that can realistically fail is enumerated as ordinary domain data and returned, so it is a business case and not a contract. The keyword invited exactly the reading the language had rejected. `require` is not positional either — it may follow `let` bindings partway through a body — so it is not a precondition in the placement sense.

## Decision

`require` becomes **`guard`**. `requires` becomes **`depends on`**.

`depends on` is two words. `depends` is reserved; `on` is not. `on` is read as the second word of the keyword only in the position right after `depends`, the way the `for` of `examples for` is read after `examples` (ADR-0046), so a field, a parameter or a behavior may still be named `on`.

The rename is a hard one. There is no alias and no deprecation window.

## Rationale

`guard` is Swift's `guard … else`, and the match is exact rather than approximate: the `else` is mandatory, the failing branch departs, and a name bound on the way (`guard let x = …` there, `guard T(v) as x else …` here, ADR-0070) is in scope for the rest of the body. The word also brings no contract reading with it. It is what the compiler already called these — `InvariantChecker` refines along "each guard", and the specification's discharge section and its "guard comprehension" both use it — so the surface now agrees with the prose about it.

`depends on` names what the specification's own section is titled after, Dependencies, and what the industry calls the mechanism, dependency injection. Three shorter candidates were weighed and dropped:

- **`needs`** is already a field name, a field initialiser and an attempt binder in the CRM model (`data DiscoveredCommon = { …, needs: Needs }`), sitting inside the `Needs` / `NeedsAnalysis` / `PainPoint` vocabulary a sales methodology brings. Reserving it takes an ordinary domain noun away from every model that wants it.
- **`using`** carries the right meaning through Scala 3's context parameters, which are injected exactly as this clause's names are. It becomes a near-synonym of `with`, which supplies a fake for one of these dependencies on an example row, so the declaring end and the supplying end of one relation would read alike. C#'s `using` is also an import, and this clause sits beside `import`.
- **`uses`** collides with nothing and matches `constructs` in part of speech, but says less than it should: the clause may only name a behavior whose own requirement set is not empty, and a behavior that uses another with an empty one must not write it (E1607).

`needs` and `uses` both read as supersets of the rule, and neither says the thing that decides membership, which is that the name is supplied from outside rather than called. `depends on` says dependency, which is what the checks, the diagnostics and the JVM `bind` are all about, and it matches `constructs` in part of speech so the two clauses read in parallel in either order.

## Consequences

The clause is the first two-word keyword, so the three readers that assumed one opening token now take how many to skip: the parser's shared name list, the AST builder's name reader, and the formatter's. The AST builder is the one that mattered — left alone it would have read `on` as the first dependency and the program would still have compiled, with the wrong dependency set. `Ast.SpecBehavior.requires` is `dependsOn`, `REQUIRE_KW`/`REQUIRE_STMT` are `GUARD_KW`/`GUARD_STMT`, and `REQUIRES_KW`/`REQUIRES_CLAUSE` are `DEPENDS_KW`/`DEPENDS_CLAUSE`, so every consumer is a compile error rather than a silent survivor.

Highlighting needs one addition. `depends` is a reserved word and falls out of the lexer's list as any other does, but `on` cannot, so the TextMate grammar matches the pair with a rule of its own and the language server classifies the `on` from its position. Two lists had no guard against a rename before this: the language server's classifier and the formatter's keyword literals, which it writes back as text rather than copying tokens. Both have one now.

Every `.sou` in `souther-lang/examples` stops compiling and is migrated with this change. `souther-lang/souther-vscode` takes the regenerated grammar from a release; until then `guard` and `depends on` render unhighlighted. A project using `SoutherProcessor` sees a parse error rather than a warning, which is the cost of a hard rename.

Nothing about what the keywords mean changed. `guard` is still sugar for `if` (ADR-0020), the departure value is still an ordinary case counted by `constructs`, dependencies are still arguments fixed by partial application rather than an effect row (ADR-0016), and the term *requirement set* stays as the name of what the clause declares.

## References

- Specification: `[#reserved-words]`, `[#guard]`, `[#depends-on]`, `[#attempted-construction]`, `[#violation-destination]`
- ADR-0003 (preconditions are business cases, not contracts), ADR-0016 (requirements are arguments), ADR-0020 (`guard` is sugar for `if`), ADR-0046 (`for` after `examples` is contextual), ADR-0070 (a construction may be attempted)
- Swift: `guard … else` with a mandatory departing branch and a binding scoped to the rest of the body
- Eiffel `require`, Dafny / JML `requires`: the precondition-contract reading Souther does not take
- Scala 3 `using` clauses: context parameters, the reading `using` would have brought
