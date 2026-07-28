# ADR-0066: A helper's parameter types come from its body, never from its call sites

Status: Accepted. Supersedes ADR-0050.

## Context

ADR-0050 let a non-recursive helper leave a value parameter unannotated and read its type from the helper's call sites. `HelperTyping` built a scope for every top-level fn in the module to do it, so a helper's type was a function of every other definition in the module: `let double (x) = x * 2` was rejected on its own and accepted once something called it, and the same body meant `Int` or `String` depending on the caller.

That is the property behind several separate defects. A lambda passed to a helper is typed by whatever `expected` happens to flow in at the site rather than by a signature (#166). A definition cannot be type-checked alone, so nothing can be cached or asked per definition, which is why the LSP grew its own analysis engine and why incremental compilation (#35) has nothing to key on (#177).

Elm and F# were measured rather than recalled. Neither reads a definition's type from its callers. F# 10.0.302 processes the body in declaration order and reports `FS0072` for what the body leaves open, quoting "information prior to this program point", with a call three lines below that does not help. Elm 0.19.2 types the body and generalises what is left, so `lengthOf x = x.length` becomes `{ b | length : a } -> a` and is used at two types in one module. Both take the type from the body; what fills the rest is generalisation. Souther has no user generics (ADR-0011's bounded model), so it cannot generalise — and call-site inference was what stood in its place.

## Decision

A helper's parameter types come from the helper: written beside the parameter, or determined by the body. Call sites are not consulted.

- The body determines a parameter at the first position it puts the parameter in that names a type, in the order the body is written: an operand of an operator against a value of known type, an argument of a call whose parameter type is declared, the value of a field in a construction, an `if` condition, the value of a binding — including the binding a call to a helper with a declared parameter is inlined to.
- The whole body is read. Unlike F#, which reports what is not settled by "information prior to this program point", a position further down the body still determines the parameter, and so does a helper declared further down the file. Written order decides only which of several determining positions wins, so no annotation is ever required merely because of where something was written.
- A parameter the body leaves open MUST be annotated. Without generalisation there is nothing to leave it open as, and the annotation is what states the type instead. This holds a parameter read only through a field (`line.qty` names no type) and one passed only to a built-in whose signature the compiler states in code rather than in a signature table.
- A function-typed parameter MUST be written. Neither applying it nor handing it to a combinator that applies it determines its type, and the inliner needs the value/function distinction to expand the call. The rule reads the expanded body, so a parameter handed to `List.map` is reported as the function it is rather than as one nothing determined. A `let`-bound lambda is not the same case: it is applied in the body that binds it, so its parameter types are read from those applications — the binding is expanded at each of them, and there is no declaration to tell function from value before that.
- A recursive helper is unchanged: it is lowered to a method and typed on its declaration, so it writes all of its parameter types and its return type.

The rule that reads the body answers with a type or with nothing; it never reports a type error. Once the parameter has a type, the standalone check that follows is the one an annotated helper gets, so a body that disagrees with the type is reported by the elaborator at the position of the disagreement. Type errors keep coming from one implementation.

## Consequences

`let double (x) = x * 2` compiles with no call site, which ADR-0050 rejected. Reading a helper is enough to know what it means, which is what makes a per-definition question possible at all (#177 step 1).

The measured migration cost is zero lines. Of the 240 helper `let`s in the bundled prelude and every module of souther-lang/examples, 235 annotate their parameters and 5 name the type with a constructor pattern, which `[#binding-patterns]` already accepts as saying the type. Nothing in the corpus depended on call-site inference.

Where the body leaves a parameter open the report names the parameter and labels the use that named no type. The "used at conflicting types" error of ADR-0050 no longer exists: with no call sites read, there is nothing to conflict, and a body that uses the parameter at two types is an ordinary type error at the second use.

What a helper settles about itself reaches its expansion (#178). The settled type is written back onto the parameter, as a reference that carries what it denotes and no surface text at all. ADR-0067 is what makes that possible: everything downstream of `Resolve` reads what a reference denotes rather than how it was spelled, so a type with no spelling is as good as a written one, and the type-to-surface writer this looked like it needed is not needed. The inliner then carries it onto the binding the call becomes, like any written type, and a `match` on a body-determined sum sees the sum rather than the case the caller passed.

Settling happens before a helper call is expanded, which is twice: once before the data invariants are inlined, and once before the bodies are lowered. The two are separate points in the pipeline because an importer reads an included data's invariant through the symbol table and must find it already expanded. Settling is idempotent, so running it at both is running it once at each place it is needed.

The rule that reads the body is deliberately small, and every gap in it is closed by annotating. When names and types resolve through one implementation (#177 steps 2 and 4), a built-in's parameter types become readable the same way a declared one is, and the gap closes without the rule changing.

## References

- Specification: `[#fn-declaration]`, `[#binding-patterns]`
- Issue #176 (a helper has no type of its own), issue #177 (one question, several implementations)
- ADR-0050 (superseded), ADR-0011 (no user generics), ADR-0038 (helpers may recurse), ADR-0017 (declare, don't infer)
