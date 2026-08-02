# ADR-0086: A function name is a value, and application is an operation on one

Status: Accepted.

## Context

Issue #261 reported that the specification writes `Map.empty` and the compiler rejects it, and that the rejection names `Map` as an unknown local and suggests a parameter called `p`. Both symptoms come from one shape in the tree:

```java
record Call(String fn, ValueName denotes, List<Expr> args, ConstructionOrigin origin, SourcePos pos)
```

What is applied is not a subexpression. It is a string beside the node, so "what does this name mean" had to be asked twice — once for a name under a call and once for a name that is not — and the two answers were reached by two different ladders.

The parser decided which ladder a name would take by looking three tokens ahead for a `(`. With one, `Map.empty` was flattened into the string `"Map.empty"`; without one, `Map` became a variable and `.empty` a field read, and no path to the library was left. `Resolve.calledName` consulted `Prelude.isQualifier` and `Resolve.valueName` did not, and the two ladders ordered types and helpers differently, so a module declaring both got different answers in the two positions. `Exposing` rewrote bare imported names into qualified ones by walking the tree with a `default -> e` catch-all: it missed `Ast.Var`, missed `Ast.IfConstructed` entirely, and never visited `examples` or `fakes`. It ran before `Resolve`, so it knew no bindings and an `import List ( map )` beat a parameter named `map`.

A standard-library function could not be handed over by name for the same reason. The specification says a named `let` may be passed by name and calls the two spellings the same thing, and the standard library's functions are `let`s in `souther/*.sou` — but their qualified form parsed as a field access and their bare form was not rewritten.

Underneath, `Prelude.BUILTINS` held signatures in Java for functions the declarations were silent about. Two of them, `Int.divide` and `Decimal.divide`, shared one arm of one switch and were told apart only by argument count, so they were interchangeable aliases: `Int.divide(a, b, 2, HALF_UP)` type-checked as the Decimal one and `Decimal.divide(a, b)` as the Int one, which made a sentence the specification had already written false.

Core already drew the distinction the AST was missing. `Core.Call` names a target and emits `invokestatic`; `Core.Apply` loads a binding and invokes it; the javadoc says they are apart "because it is a different operation". At the machine level that is true. The AST had not caught up.

## Decision

**A name that names a function is a value of function type. Applying something is an operation on the value it evaluates to.**

- `Ast.Apply(Expr function, List<Expr> args, ConstructionOrigin origin, SourcePos pos)` replaces `Ast.Call`. What is applied is an ordinary subexpression, carried by the same recursion as the arguments.
- One ladder answers a name, wherever it is written. The position contributes one bit — whether the name is applied — which decides only whether a type written as a value is a unit data's construction or a newtype taking what it wraps. Everything else is the same question with the same answer.
- `Q.m` where `Q` is unbound and is a library qualifier is a reference to that namespace's member, folded in `Resolve` with the bindings in force. Whether the namespace *has* that member is the check's to say: the library resolves its own sources while it loads, so asking during resolution would tie the answer to how far loading had got.
- An import contributes a table of names, not a rewrite of the tree. Resolution consults it last, after the bindings in force and the module's own declarations, and writes the library name it answered with into the resolved tree.
- One spelling reaches the value namespace once, whichever way it arrives — the module's own declarations, an import, or a library qualifier. A type may not be named like a qualifier, and an import that collides with a declaration is refused at the import line.
- Every standard-library function and value states its own signature in a core declaration. `Prelude.BUILTINS` is gone — not emptied, deleted, so there is nowhere for a signature to be written in Java again. What the type language cannot say — an ordering constraint, "this argument is a rounding mode" — is a side condition beside a declared signature, never in place of one.
- A named function written where a value goes is η-expanded to a function value. `String.trim` becomes `Block([$v0], Call("String.trim", [$v0]))`, which is the same `Core.Block` an anonymous lambda produces, so past the type check a named function, an anonymous block and a runtime choice among them are one kind of value.
- Application is postfix and iterated: `f(x)(y)`, `(if flag then f else g)(x)`, `f(x).field`. An argument list may not cross a line break.
- A function type is refused where the position requires an external representation — a data field, a newtype's base, a behavior's input and output — and nowhere else. It is refused because a function has no external form, not because a function is a lesser kind of value.
- A behavior's name handed over is the behavior, not the `let` that implements it. A Java implementation replaces the behavior, so a value that reached past it to the helper body would be a second answer to the same name; the emitted code goes through the behavior's class. A behavior with a requirement is a binding by the time it can be named, so nothing carries a requirement past its `depends on`.

### An argument list may not cross a line break

The plan for this change said the opposite. Souther's grammar has no newline token, and a comment in the parser says as much: a line starting with `(`, `.` or an operator continues the line above. Reading a next-line `(` as an application looked like the choice that kept postfix application from being an exception to that.

It is not implementable. `list.sou` has a block whose statements end with a call and whose result is a tuple written on the next line, and under that rule the standard library stopped loading. A block's result is written on its own line often enough that the rule would cost more than the continuation it preserves, so an argument list is tied to the line its callee ends on and a `(` that opens a line is a parenthesised expression.

## Consequences

Five passes were rebuilding an application from its name and discarding whatever else was there — `Exposing`, `AstBuilder.pipe`, `NewtypeDesugar`, `HelperInliner` in two places, and `InvariantChecker`. Under `Ast.Call` that was invisible, because there was nothing else to discard. Each now carries the callee expression through. The compiler error that surfaced them is the sealed `Expr` switch in `Ast.mapChildren` and `Ast.forEachChild`, which has no `default` arm.

`Exposing` no longer walks the tree. It validates the import lines and answers what they bring in; the catch-all that dropped `Ast.Var` and `Ast.IfConstructed` went with the walk, and example rows and fake rows are covered because `Resolve` visits them like any other expression. A parameter named `map` now wins over `import List ( map )`.

`Int.divide` and `Decimal.divide` are separate declarations taking their own arguments. The specification's sentence that `Decimal.divide(a, b)` cannot be written is true.

`Prelude.BUILTINS` is gone. A two-way test holds the correspondence in place: every kernel the backend can emit has a declaration, and every declaration has an emitter, with the branching divisions named as written-out exceptions rather than left to a subset check.

`isFunctionSelection` is `return producesFunction(e);`. The reason a block could not be a value where a function was expected was that the backend refused to emit one there; now it emits one, and what remains is the narrower truth the diagnostic already had a key for — a function whose type nothing settles.

`Core` gained no node. `Core.Apply.fn()` is still a `Core.Read`, and a callee that is not a name spills into a synthetic `let` — the same shape `emitFunctionValue` already handled for a binding that creates a capture. The callee is evaluated once and before the arguments.

`souther-fmt` reassembled a callee from the identifier tokens under the node, which is only possible while a callee is a name: it printed `adder(1)(x)` as `adder(1, x)` and a parenthesised choice as nothing. It prints the callee as a subexpression now. Nothing in the corpus exercised this, so the formatter's own suite was green while it was wrong — the pinned cases are the fix's evidence. `souther-lsp` needed no change: its semantic-token classification reads the resolved name, which is what it always read.

What is still refused, and why:

- A behavior's name bound to a `let` — `let f = twice`. Handing the same name to a combinator works and goes through the behavior's class, so this is the decision above with one position missing, not a rule. What blocks it is that η-expansion happens in the inliner, which holds the helper table and not the behavior signatures, so the arity to expand to is not in hand there (issue #271).
- The three functions taking a rounding mode, handed over by name. Their argument is an identifier read as itself rather than an expression, so an η-expansion would turn it into a binding and the side condition would reject it. When `RoundingMode` becomes an ordinary value type this restriction goes with it (issue #270).
- A function whose type nothing settles, stored in a collection. The measurement that named this is worth recording: a plain lambda and a library name are refused *identically* when stored, so the rule is about a function whose type is unknown at the point it is stored, not about recursion or about escaping. Applying one through a combinator is a separate gap that predates this change (issue #272). That gap is closed — the list above records what was still refused when this decision was taken; issue #272 was a stale binding in the inliner, not a rule.

`Core.FunctionRef` was considered and left out (issue #277). Folding a function reference into a compact IR node rather than expanding it to a `Core.Block` every time is a representation choice, not a semantic one; it belongs with the explicit closure-conversion form `Core.Block`'s javadoc is waiting for. What is permanent is that a function reference in value position becomes a function value.

Let-polymorphism is not introduced, and nothing was added to stand in for it. A name bound to a declaration is the declaration, expanded at each use — the path a helper bound to a name already took — so a polymorphic one is instantiated afresh per use and needs no representation of its own. `let r = List.reverse` applied to a `List<Int>` and a `List<String>`, and `let e = Map.empty` read at two key and value types, compile; measured. What let-polymorphism would add is a binding that generalises without being expanded, which is a different question and not one this decision answers.

## References

A name that was answered is no longer reported as an unknown one. `notAValue` said "unknown identifier" for everything that fell through its switch, so a behavior's name and a rounding mode — both resolved, both refused for a stated reason — sent the reader looking for a spelling mistake. They name what they denote.

- Specification: `[#blocks]`, `[#fn-declaration]`, `[#fn-rules]`, `[#stdlib]`, `[#reserved-namespace]`, `[#stdlib-map]`, `[#stdlib-set]`, `[#stdlib-decimal]`, `[#let]`
- Issue #261; issues #270 (a rounding mode is not a value), #271 (a behavior's name in a binding), #272 (a lambda parameter over a collection of functions), #274 (two CST nodes for an application), #275 (one prelude declaration in three maps), #276 (two copies of the signature-application typing), #277 (reifying a named function where the signatures are)
- ADR-0067 (a written name is resolved once, into the tree), ADR-0072 (a `let` with no parameter list is a value), ADR-0053 (the declaration is the single source of truth for a signature), ADR-0081 (a primitive may be a union member)
- Elm's `import List exposing (map)`, whose qualified access always works and whose import only elides the qualifier
