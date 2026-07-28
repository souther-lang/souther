# ADR-0067: A written name is resolved once, into the tree

Status: Accepted.

## Context

`Ast` carried names as text. A type reference was a `String`, a sum's cases were `List<String>`, a `constructs` clause was `List<String>`, and every check that needed to know what one of them meant called `Symbols.resolve` itself — 60 such calls across the checker, the deriver, codegen and the example runner.

Because each site decided for itself, a capability reached the positions someone wired it to. `constructs` took a bare identifier while `requires` took a qualified one. E1002 and E1006 compared spellings, so a clause naming `up.Amount` and a body building an imported `Amount` disagreed about one type. A spread of a name nothing declared crashed rather than reporting. Issues #101, #113, #124, #132 and #154 are the same defect written five times, and PR #175 fixed three more instances at once.

Text also has no home. A name written inside another module's declaration means what that module says it means, so `Symbols` grew `resolveIn(inModule, written)` and 32 places threaded a `home` argument to say where the text had come from. That argument exists only because resolution happens late.

## Decision

Every written name is resolved once, by a pass that runs before anything else reads the tree, and the tree carries the answer.

- `Ast.Name(written, denotes, pos)` replaces the `String` in each of the thirteen positions that name a declared type: a sum's cases, a spread, a construction's type, `constructs`, a codec variant's case, a decoder or encoder reference, a match arm's cases, a pattern's opened layers, and a binding's opened newtype.
- `Ast.TypeRef` carries the `Type` it denotes. A written type becomes a `Type` in exactly one function, called once per reference.
- `Resolve` runs per module, in the module that wrote the names, immediately after parsing and before the deriver. A name that denotes nothing is reported there and the compile stops, so `denotes` is non-null everywhere downstream and no consumer needs a null branch.
- A pass that synthesizes a node states what its name means rather than writing a spelling for someone else to resolve. The deriver builds codec references from a field's `Type`, so it has the resolved name already.
- `written` stays on the node, for a diagnostic that quotes the source. It is not what two names are compared by.

`Type` and `TypeName` move to `souther.compiler.types`, which `ast` can depend on.

The scope is names that denote a type. A `Var` that may be a unit data's construction and a `Call` whose target may be a newtype constructor are in the value namespace, where a local binding wins over a declaration; they are left to #177 step 4.

## Consequences

`Symbols.resolveIn` and `Symbols.moduleOf` are gone, and with them the `home` argument at 32 call sites. `Symbols` answers "what does this spelling mean *here*", and here is the only place it is ever asked, because each module's names were resolved by its own pass. The 60 resolution calls are 24, and every one that remains is either the value namespace, a declaration's own name, or the one function that turns a written type into a `Type`.

Three spelling comparisons are gone rather than canonicalised. `SpecChecker` compared `constructs` against the body through a `canonicalConstruct` helper added in PR #175; both sides are resolved names now and the helper is deleted. A constructor pattern compared its inner layer against the wrapped type's simple name, so `Some(up.Amount(v))` and `up.Wrapped(up.Amount(n))` were rejected — they compile, and `casePattern` reads a dotted name like every other name position.

Names are resolved before the deriver, so a module whose name denotes nothing is reported before its codecs are derived. In the workspace path that module is skipped and its importers are skipped as before; in a compile it is the first error. That is a change in which error a broken module reports first, not in whether it is reported.

The measured migration cost is zero lines: the bundled prelude and every module of souther-lang/examples compile unchanged, and no name that resolved to nothing was being tolerated.

The two agreement tests stay. `CompilePathAgreementTest` and `DiagnosticPathAgreementTest` compare what separate entry points produce, and sharing a resolver does not merge the entry points — the single-module and linking sequences are still two sequences, and the CLI, the annotation processor and the editor still call them their own way. Retiring the tests is not what this buys.

The parser's dotted-name loop was written out six times; it is `dottedTail` once, and the lookahead that scans a dotted name is `pastDottedName` once. The three remaining dotted loops read a field-access chain, which is a different production and stays one.

## References

- Specification: `[#qualified-reference]`, `[#binding-patterns]`, `[#match]`
- Issue #177 (one question, several implementations) steps 2 and 3; issues #101, #113, #124, #132, #154
- ADR-0058 (a type is reachable through the module that declares it), ADR-0059 (construction is guarded by declaration), ADR-0066 (a helper is typed by its body)
