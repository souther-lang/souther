# ADR-0072: A `let` with no parameter list defines a value, substituted at its references

Status: Accepted. Amends ADR-0025 and ADR-0026.

## Context

A `let` required a parameter list, so there was no way to give a value a name. Every place that wanted one wrote the value out again: a CRM example row states a twenty-two-field `NegotiationReview` and the next row states the same one to vary a single input, and the ten imports that record carries exist for those rows alone (issue #163).

Nothing decided this. `let f (x) = e` was written with parentheses and the parentheses were made mandatory; no ADR and no line of the specification says a definition must take an argument.

F# and Elm were measured rather than recalled. Both split a value from a function by the parameter list and by nothing else: F# 10.0.302 reads `let x = 5` as a value evaluated once and `let f () = 5` as a function, and Elm 0.19.2 reads `x = 5` and `f a = a + 1` as the same kind of declaration. Both also accept a lambda bound to a name — `let addOne = fun x -> x + 1`, `addOne = \x -> x + 1` — which ADR-0026 declined as redundant.

## Decision

**A `let` written with a parameter list defines a function; a `let` written without one defines a value.** An empty `()` is a compile error, since it would be a second spelling of the value form. A helper therefore has at least one parameter, and a behavior whose type takes nothing is implemented by a value.

**A lambda on the right of `=` is the parameter-list form.** `let f = (x) -> e` and `let f (x) = e` define one thing; the parameter-list form is what the formatter writes back. Only a lambda the source wrote moves: a `.field` getter is a block too, but its parameter is synthesized, and a definition whose parameter the author never wrote is not one they can read. It stays a block, and a block is not a value. ADR-0026 declined this spelling on the ground that F#, OCaml and Haskell write the named form. That is a habit in those languages, not a rule, and with the value form present the two spellings meet in one place for the first time — so one of them has to mean something, and meaning the same thing is what costs nothing. There is no ambiguity to settle: a top-level definition's call sites are not read (ADR-0066), so both spellings take their parameter types from the body.

### A value is substituted, not held

A value is not module state. Its expression is elaborated in the module that declares it and substituted at each reference.

- **Its names are resolved once, where it is written.** ADR-0067 resolves a module's names in the module that wrote them; what is substituted is the resolved definition, not text to be read again at the reference.
- **It is evaluated at each reference, and that is not observable.** A value's body obeys a helper's rules, so it cannot call an injected behavior and is pure and total.
- **Identity is not observable.** Two references may yield distinct values; the language has no reference identity and compares structurally (ADR-0047).
- **An invariant a value breaks is reported at the value**, whether or not anything names it — which is what a construction with a constant argument already does.
- **What a value constructs belongs in the `constructs` of the behavior that names it**, transitively, exactly as a helper body's constructions do. Spreading a value builds it, so a spread contributes the same way.
- **A spread is a reference**, and carries what it resolves to. `Person { ...base, age = 21 }` reads the same in a behavior's body and in an `example` row, and a binding in force wins there as everywhere else — a parameter named `base` is what the spread copies, not a value of that name. A spread used to hold a bare `String`, which left every reader downstream to match the spelling against the module's definitions; it is an `Ast.ValueRef` now, resolved by the pass that resolves the rest (ADR-0067). A spread holds a name rather than an expression, so a value is bound ahead of the construction and the spread copies that binding — the shape a spread of a local already has.
- **A value must not reach itself**, by naming another value, spreading one, or calling a helper that does. A helper on a call cycle is lowered to a method and recurses (ADR-0038); a value has no such form. The value graph is therefore not the call graph, and a cycle through a value is refused with the path it goes round, apart from the recursion check — which would ask for a return type the author never wrote.
- **Every edge of both graphs is a resolved name.** A call, a bare name and a spread each carry what they denote, so applying a function-typed parameter is not a call to whatever else bears its spelling. The call edges were matched against the helper table by name, which made a parameter named like a value close a cycle that does not exist — and, on its own, made `let f (g: (Int) -> Int) = g(1)` recursive whenever a helper was named `g`. An expansion carries the argument's own answer into the body it substitutes it into, so a named function handed to a combinator stays the helper it is.

If a value's body ever becomes able to touch the outside world, when it is evaluated stops being unobservable and this has to be decided again.

### One name in the value namespace

A module's `let` may not be named like a data the module declares. A data is written where a value goes — a unit data is one, a newtype is applied to what it wraps, a record is constructed by its name — so the two would be one spelling with two answers, and the type won, because a name resolves to a type first.

Elm forbids the collision by capitalization (`Ready = 99` is `UNEXPECTED CAPITAL LETTER`) and F# permits it, letting the later binding shadow the union case (`let Ready = 99` compiles and the bare `Ready` is then the int). Souther writes Japanese identifiers and case carries no meaning, so neither device is available, and the collision is refused where it is declared. Before this, `data Ready` and `let Ready()` coexisted in silence.

A behavior and a same-named `let` are not a collision: they are one thing's declaration and implementation, reconciled by parameter count.

### Where typing comes from

A top-level definition takes its parameter types from its own body and its call sites are not read (ADR-0066). A binding inside a block has no declaration to read, so a lambda bound there takes its parameter types from the applications in the body that binds it (ADR-0025). The two rules are separated by where the `let` is written, not by how it is spelled: a block holds no parameter list, so the forms never meet in one place. Unifying them would need generalisation, which requires user generics — ADR-0010 declines those for the spec-DSL correspondence of ADR-0001.

## Consequences

An `example` row names a value instead of restating its input, and spreads one to vary a field. What a row may name is a property of the value graph rather than of one definition's text: a value is fixture-evaluable when its body is a literal, a construction, a spread, `Set.fromList` / `Map.fromList` over one, or a reference to another fixture-evaluable value, so a chain of values holds and a body that computes is refused. A value that reaches itself is reported as the cycle it is rather than through the recursion check, which would name a return type the author did not write.

The two `fromList` forms are admitted because a value has to be ordinary code and a row does not. A row writes a set as its elements and a map as its entry pairs, and the decoder reads that; in code a list literal is a `List` whatever the position declares, which is measured — `let s: Set<Int> = [ 1, 2 ]` is a type error. `Set.fromList` and `Map.fromList` are the forms that notation already stands for, so admitting them is what lets one record serve as both. Without it the CRM record this issue is about cannot be hoisted at all: `NegotiationReview.decisionMakers` wraps a `Set`.

The neutral form of a newtype no longer depends on how it was spelled. A value's body reaches the fixture builder already desugared, where `Amount(500)` is the record `Amount { value = 500 }` (ADR-0032) — the same value written the other way — so both now build the newtype's inner value rather than a field map.

The measured migration cost is six occurrences, all of them source written inside the compiler's own tests (`let now ()`, `let caller ()`, `let empty ()`, `let group ()`). The bundled prelude and every module of souther-lang/examples have none, and compile unchanged.

`exposing` is unaffected: a value is module-local, like any other `let`.

## References

- Specification: `[#fn-declaration]`, `[#fn-value-semantics]`, `[#fn-rules]`, `[#let]`, `[#example-evaluable]`, `[#reserved-namespace]`
- Issue #163 (a fixture cannot be named)
- ADR-0025 (functions are first-class — the spelling rule it stated is amended here), ADR-0026 (`:` for signatures, `=` for definitions — the paragraph declining the lambda spelling is amended here)
- ADR-0066 (a helper is typed by its body), ADR-0067 (a name is resolved once), ADR-0010 (no user generics), ADR-0032 (a newtype is constructed by applying its name)
