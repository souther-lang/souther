package souther.compiler.frontend;

import souther.compiler.ast.Ast;
import souther.compiler.cst.LineIndex;
import souther.compiler.cst.SyntaxElement;
import souther.compiler.cst.SyntaxKind;
import souther.compiler.cst.SyntaxNode;
import souther.compiler.cst.SyntaxToken;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.Region;
import souther.compiler.diag.SourcePos;

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;

/**
 * Builds the compiler's {@link Ast} from a concrete syntax tree. This is where the surface forms the
 * parser deliberately kept lossless are lowered to the desugared AST every later stage expects:
 * {@code |>} folds into a call's last argument, {@code guard} becomes an {@code if}, {@code let}
 * becomes a {@code LetIn}, {@code T?} becomes {@code Option<T>}, and the {@code let}/{@code match}
 * destructurings expand into positional reads. The CST feeds the formatter and the LSP untouched;
 * only the compiler pipeline runs through here.
 */
public final class AstBuilder {

    private final LineIndex lines;
    private String moduleName = "";
    private int matchWholeCounter = 0;
    private int tupleCounter = 0;
    private int getterCounter = 0;
    private int patternCounter = 0;
    private int spreadCounter = 0;

    private AstBuilder(String source) {
        this.lines = new LineIndex(source);
    }

    /**
     * Builds a module from a parsed source file. A header-less source is named
     * {@code defaultModuleName}; a {@code null} default makes the header required.
     *
     * <p>Requires a CST the parser accepted: every node it reads has the children the grammar gives
     * it, and a missing one is dereferenced rather than reported. {@link CstFrontend#parse} is the
     * one caller and raises the parser's first error before building — which is why this is
     * package-private, and what a second caller would have to guarantee.
     */
    static Ast.Module build(SyntaxNode sourceFile, String source, String defaultModuleName) {
        return new AstBuilder(source).module(sourceFile, defaultModuleName);
    }

    // --- module ---

    private Ast.Module module(SyntaxNode file, String defaultModuleName) {
        Optional<SyntaxNode> exampleFile = file.child(SyntaxKind.EXAMPLES_FILE_HEADER);
        if (exampleFile.isPresent()) {
            return exampleFileModule(file, exampleFile.get());
        }
        Optional<SyntaxNode> header = file.child(SyntaxKind.MODULE_HEADER);
        String name;
        SourcePos pos;
        Map<String, Ast.RetType> exposedOutputs = new HashMap<>();
        List<String> exposing = new ArrayList<>();
        if (header.isPresent()) {
            SyntaxNode h = header.get();
            name = qualifiedNameText(h.child(SyntaxKind.QUALIFIED_NAME).orElseThrow());
            pos = pos(h);
        } else if (defaultModuleName != null) {
            name = defaultModuleName;
            pos = pos(file);
        } else {
            throw error(pos(file), "parse.module", "expected `module` declaration");
        }
        moduleName = name;   // set before any type is read, so type-variable gating knows the namespace
        header.flatMap(h -> h.child(SyntaxKind.EXPOSING_CLAUSE))
                .ifPresent(c -> readExposing(c, exposing, exposedOutputs));

        List<Ast.Import> imports = new ArrayList<>();
        List<Ast.Def> defs = new ArrayList<>();
        List<Ast.BehaviorDef> behaviors = new ArrayList<>();
        List<Ast.FnDef> fns = new ArrayList<>();
        List<Ast.Example> examples = new ArrayList<>();
        List<Ast.Fake> fakes = new ArrayList<>();
        for (SyntaxNode n : file.childNodes()) {
            switch (n.kind()) {
                case IMPORT_DECL -> imports.add(importDecl(n));
                case DATA_DEF -> defs.add(dataDef(n));
                case BEHAVIOR_DEF -> behaviors.add(behaviorDef(n));
                case FN_DEF -> fns.add(fnDef(n));
                case EXAMPLE_DEF -> examples.add(example(n));
                case FAKE_DEF -> fakes.add(fake(n));
                default -> { /* MODULE_HEADER handled above; ERROR nodes are reported already */ }
            }
        }
        return new Ast.Module(name, exposing, exposedOutputs, imports, defs, behaviors, fns,
                examples, fakes, null, pos);
    }

    /**
     * An {@code examples for <module>} file: what its target module's rows are written in. It holds the
     * rows, the fakes they run against, and the values those rows name; anything else in it is E1906. The
     * returned {@link Ast.Module} carries those and its {@code exampleFileTarget}; the compiler merges it
     * into the target.
     *
     * <p>A value is a {@code let} with no parameter list, and it is here because a row that names one had
     * nowhere in this file to declare it — so the fixture went back to the model file, which is the file
     * the rows exercise rather than the one they are written in (issue #210). A {@code let} with
     * parameters is a helper, which is a method the target module emits, and a companion file does not
     * add to what the model compiles to.
     */
    private Ast.Module exampleFileModule(SyntaxNode file, SyntaxNode header) {
        String target = qualifiedNameText(header.child(SyntaxKind.QUALIFIED_NAME).orElseThrow());
        moduleName = target;
        SourcePos pos = pos(header);
        List<Ast.Example> examples = new ArrayList<>();
        List<Ast.Fake> fakes = new ArrayList<>();
        List<Ast.FnDef> values = new ArrayList<>();
        for (SyntaxNode n : file.childNodes()) {
            switch (n.kind()) {
                case EXAMPLE_DEF -> examples.add(example(n));
                case FAKE_DEF -> fakes.add(fake(n));
                case EXAMPLES_FILE_HEADER -> { /* the header itself */ }
                case FN_DEF -> {
                    Ast.FnDef fn = fnDef(n);
                    if (!fn.params().isEmpty()) {
                        throw onlyExamples(n);
                    }
                    values.add(fn);
                }
                case IMPORT_DECL, DATA_DEF, BEHAVIOR_DEF -> throw onlyExamples(n);
                default -> { /* ERROR nodes already reported */ }
            }
        }
        return new Ast.Module(target, List.of(), new HashMap<>(), List.of(), List.of(), List.of(),
                values, examples, fakes, target, pos);
    }

    private CompileException onlyExamples(SyntaxNode n) {
        return CompileException.of(
                Diagnostic.of("E1906", "check.example.file.only").title("check.example.title")
                        .at(pos(n)).build(),
                "an `examples for` file holds examples, the fakes they run against and the values they"
                        + " name; a data, a behavior, an import and a `let` with parameters belong in the"
                        + " module itself");
    }

    /** {@code example <target> | rows...}. The contextual {@code example} lexes as an identifier, so
     * the target is the second identifier token. */
    private Ast.Example example(SyntaxNode n) {
        List<SyntaxToken> idents = identTokens(n);
        String target = idents.size() >= 2 ? idents.get(1).text() : "";
        SourcePos pos = idents.size() >= 2 ? posOf(idents.get(1)) : pos(n);
        List<Ast.ExampleRow> rows = new ArrayList<>();
        for (SyntaxNode row : childNodes(n, SyntaxKind.EXAMPLE_ROW)) {
            rows.add(exampleRow(row));
        }
        return new Ast.Example(target, rows, pos);
    }

    /** {@code [ "desc" : ] ( inputs ) -> expected}. The description is a leading string token; the
     * inputs are the {@code ARG_LIST}'s expressions; the expected is the remaining expression. */
    private Ast.ExampleRow exampleRow(SyntaxNode n) {
        String description = n.token(SyntaxKind.STRING_LIT).map(t -> stringValue(t.text())).orElse(null);
        List<Ast.Expr> inputs = new ArrayList<>();
        n.child(SyntaxKind.ARG_LIST).ifPresent(list -> {
            for (SyntaxNode a : exprChildren(list)) {
                inputs.add(expr(a));
            }
        });
        List<Ast.With> withs = new ArrayList<>();
        n.child(SyntaxKind.WITH_CLAUSE).ifPresent(clause -> {
            for (SyntaxNode b : childNodes(clause, SyntaxKind.WITH_BINDING)) {
                withs.add(new Ast.With(firstIdentText(b), expr(firstExprChild(b)), pos(b)));
            }
        });
        // the expected is the row's own expr child (ARG_LIST holds the inputs; WITH_CLAUSE the fakes)
        List<SyntaxNode> expectedNodes = exprChildren(n);
        Ast.Expr expected = expectedNodes.isEmpty() ? null : expr(expectedNodes.get(0));
        return new Ast.ExampleRow(description, inputs, withs, expected, pos(n));
    }

    /** {@code fake <target> | rows}. The contextual {@code fake} lexes as an identifier, so the
     * target is the second identifier token. */
    private Ast.Fake fake(SyntaxNode n) {
        List<SyntaxToken> idents = identTokens(n);
        String target = idents.size() >= 2 ? idents.get(1).text() : "";
        SourcePos pos = idents.size() >= 2 ? posOf(idents.get(1)) : pos(n);
        List<Ast.FakeRow> rows = new ArrayList<>();
        for (SyntaxNode row : childNodes(n, SyntaxKind.FAKE_ROW)) {
            rows.add(fakeRow(row));
        }
        return new Ast.Fake(target, rows, pos);
    }

    /** {@code ( args ) -> out} or {@code _ -> out}. A row with no {@code ARG_LIST} is the default. */
    private Ast.FakeRow fakeRow(SyntaxNode n) {
        Optional<SyntaxNode> args = n.child(SyntaxKind.ARG_LIST);
        List<Ast.Expr> inputs = new ArrayList<>();
        args.ifPresent(list -> {
            for (SyntaxNode a : exprChildren(list)) {
                inputs.add(expr(a));
            }
        });
        boolean isDefault = args.isEmpty();
        List<SyntaxNode> exprs = exprChildren(n);   // the output (not inside ARG_LIST)
        Ast.Expr output = exprs.isEmpty() ? null : expr(exprs.get(0));
        return new Ast.FakeRow(isDefault ? null : inputs, output, isDefault, pos(n));
    }

    private void readExposing(SyntaxNode clause, List<String> names, Map<String, Ast.RetType> outputs) {
        for (SyntaxNode entry : childNodes(clause, SyntaxKind.EXPOSED_ENTRY)) {
            String name = qualifiedNameText(entry.child(SyntaxKind.QUALIFIED_NAME).orElseThrow());
            names.add(name);
            entry.child(SyntaxKind.RET_TYPE).ifPresent(rt -> outputs.put(name, retType(rt)));
        }
    }

    private Ast.Import importDecl(SyntaxNode n) {
        String module = qualifiedNameText(n.child(SyntaxKind.QUALIFIED_NAME).orElseThrow());
        String alias = n.child(SyntaxKind.IMPORT_ALIAS)
                .map(a -> identTokens(a).get(0).text()).orElse(null);
        List<String> names = new ArrayList<>();
        n.child(SyntaxKind.NAME_LIST).ifPresent(list -> {
            for (SyntaxToken t : identTokens(list)) {
                names.add(t.text());
            }
        });
        return new Ast.Import(module, alias, names, pos(n));
    }

    // --- data ---

    private Ast.Def dataDef(SyntaxNode n) {
        String name = firstIdentText(n);
        SourcePos pos = pos(n);
        Optional<Ast.Expr> invariant = invariant(n);

        Optional<SyntaxNode> product = n.child(SyntaxKind.PRODUCT_BODY);
        if (product.isPresent()) {
            List<Ast.Name> includes = new ArrayList<>();
            List<Ast.Field> fields = new ArrayList<>();
            for (SyntaxNode member : product.get().childNodes()) {
                if (member.kind() == SyntaxKind.SPREAD_MEMBER) {
                    SyntaxToken included = identTokens(member).get(0);
                    includes.add(Ast.Name.written(included.text(), posOf(included)));
                } else if (member.kind() == SyntaxKind.FIELD) {
                    fields.add(field(member));
                }
            }
            // `data T = { }` names a type with one value, which is what a unit data is — but it is
            // built as `T {}` where a unit is built by name, so the two spellings mean the same
            // thing and reject each other's construction. One way to write it (spec §unit-data).
            if (includes.isEmpty() && fields.isEmpty()) {
                throw CompileException.of(
                        Diagnostic.of(null, "check.data.emptybody").title("check.data.invalid.title")
                                .at(bodyRegion(product.get())).args(name)
                                .hint("check.data.emptybody.hint", name).build(),
                        "data `" + name + "` has an empty body");
            }
            return new Ast.Data(name, false, includes, fields, invariant,
                    Optional.empty(), Optional.empty(), pos);
        }
        Optional<SyntaxNode> sum = n.child(SyntaxKind.SUM_BODY);
        if (sum.isPresent()) {
            List<Ast.Name> cases = new ArrayList<>();
            for (SyntaxToken t : identTokens(sum.get())) {
                cases.add(Ast.Name.written(t.text(), posOf(t)));
            }
            return new Ast.SumData(name, cases, Optional.empty(), Optional.empty(), pos);
        }
        Optional<SyntaxNode> newtype = n.child(SyntaxKind.NEWTYPE_BODY);
        if (newtype.isPresent()) {
            SyntaxNode inner = typeChild(newtype.get());
            Ast.TypeRef innerType = typeRef(inner);
            if (newtype.get().token(SyntaxKind.QUESTION).isPresent()) {
                innerType = new Ast.TypeRef("Option", innerType, innerType.pos());   // `Y?` → Option<Y>
            }
            List<Ast.Field> fields = List.of(new Ast.Field("value", innerType, pos(inner)));
            return new Ast.Data(name, true, List.of(), fields, invariant,
                    Optional.empty(), Optional.empty(), pos);
        }
        // No body of any kind: a unit data, which has no fields for an invariant to observe (spec
        // §unit-data). The parser takes an `invariant` clause after any data, so this is where a
        // clause that has nothing to constrain is refused — reaching `Ast.UnitData`, which has no
        // slot for one, would silently drop it and with it any error inside it.
        for (SyntaxNode clause : childNodes(n, SyntaxKind.INVARIANT_CLAUSE)) {
            throw CompileException.of(
                    Diagnostic.of(null, "check.invariant.onunit").title("check.invariant.invalid.title")
                            .at(pos(clause)).args(name).build(),
                    "unit data `" + name + "` cannot carry an invariant");
        }
        return new Ast.UnitData(name, pos);
    }

    /** Conjoins every {@code invariant} clause under {@code &&}; each line must hold. */
    private Optional<Ast.Expr> invariant(SyntaxNode dataDef) {
        Optional<Ast.Expr> acc = Optional.empty();
        for (SyntaxNode clause : childNodes(dataDef, SyntaxKind.INVARIANT_CLAUSE)) {
            Ast.Expr next = expr(onlyExpr(clause));
            acc = Optional.of(acc.map(prev -> (Ast.Expr)
                            new Ast.Binary(Ast.BinOp.AND, prev, next, next.pos()))
                    .orElse(next));
        }
        return acc;
    }

    private Ast.Field field(SyntaxNode n) {
        String name = firstIdentText(n);
        Ast.TypeTerm type = typeTerm(typeChild(n));
        if (n.token(SyntaxKind.QUESTION).isPresent()) {
            type = new Ast.TypeRef("Option", type, type.pos());   // `T?` → Option<T>
        }
        return new Ast.Field(name, type, pos(n));
    }

    // --- behavior ---

    private Ast.BehaviorDef behaviorDef(SyntaxNode n) {
        String name = firstIdentText(n);
        SourcePos pos = pos(n);
        Optional<SyntaxNode> sig = n.child(SyntaxKind.BEHAVIOR_SIG);
        if (sig.isPresent()) {
            SyntaxNode s = sig.get();
            List<Ast.Param> params = new ArrayList<>();
            s.child(SyntaxKind.PARAM_LIST).ifPresent(pl -> {
                for (SyntaxNode p : childNodes(pl, SyntaxKind.PARAM)) {
                    params.add(new Ast.Param(firstIdentText(p), retType(p.child(SyntaxKind.RET_TYPE).orElseThrow()), pos(p)));
                }
            });
            Ast.RetType ret = retType(s.child(SyntaxKind.RET_TYPE).orElseThrow());
            List<Ast.Name> constructs = new ArrayList<>();
            List<Ast.ValueRef> dependsOn = new ArrayList<>();
            for (SyntaxNode clause : s.childNodes()) {
                // either clause may name through a module, so the idents of one name are joined and
                // a comma starts the next
                if (clause.kind() == SyntaxKind.CONSTRUCTS_CLAUSE) {
                    constructs.addAll(dottedNames(clause, 0));
                } else if (clause.kind() == SyntaxKind.DEPENDS_CLAUSE) {
                    // one ident past the keyword is the `on` of `depends on`, which lexes as an
                    // ordinary identifier and is no part of the list
                    for (Ast.Name dep : dottedNames(clause, 1)) {
                        dependsOn.add(Ast.ValueRef.written(dep.written(), dep.pos()));
                    }
                }
            }
            return new Ast.SpecBehavior(name, params, ret, constructs, dependsOn, pos);
        }
        SyntaxNode pipe = n.child(SyntaxKind.PIPE_BEHAVIOR).orElseThrow();
        List<Ast.ValueRef> stages = new ArrayList<>();
        for (SyntaxNode st : childNodes(pipe, SyntaxKind.STAGE)) {
            StringBuilder sb = new StringBuilder();
            for (SyntaxToken t : identTokens(st)) {
                if (sb.length() > 0) {
                    sb.append('.');
                }
                sb.append(t.text());
            }
            stages.add(Ast.ValueRef.written(sb.toString(), pos(st)));
        }
        Ast.RetType declaredOut = pipe.child(SyntaxKind.RET_TYPE).map(this::retType).orElse(null);
        return new Ast.PipeBehavior(name, stages, declaredOut, pos);
    }

    // --- fn ---

    private Ast.FnDef fnDef(SyntaxNode n) {
        String name = firstIdentText(n);
        SourcePos pos = pos(n);
        List<Ast.FnParam> params = new ArrayList<>();
        // parallel to params: the pattern a parameter was written as, or null where it was a name
        List<SyntaxNode> paramPatterns = new ArrayList<>();
        n.child(SyntaxKind.FN_PARAM_LIST).ifPresent(pl -> {
            for (SyntaxNode p : childNodes(pl, SyntaxKind.FN_PARAM)) {
                SyntaxNode pat = optionalPatternChild(p);
                paramPatterns.add(pat);
                params.add(fnParam(p, pat));
            }
        });
        Ast.RetType declaredReturn = n.child(SyntaxKind.RET_TYPE).map(this::retType).orElse(null);
        boolean partial = n.child(SyntaxKind.PARTIAL_MODIFIER).isPresent();

        Optional<SyntaxNode> intrinsic = n.child(SyntaxKind.INTRINSIC_BODY);
        if (intrinsic.isPresent()) {
            if (!isReservedNamespace(moduleName)) {
                throw error(pos, "parse.intrinsic.core",
                        "`intrinsic` is a core privilege: only a module in the reserved `souther`"
                                + " namespace may declare one (ADR-0028)");
            }
            String key = stringValue(intrinsic.get().token(SyntaxKind.STRING_LIT).orElseThrow().text());
            return new Ast.FnDef(name, params, declaredReturn, key, null, partial, pos);
        }
        SyntaxNode bodyNode = onlyExpr(n);
        Ast.Expr body = expr(bodyNode);
        // `let f = (x) -> e` is the parameter-list form written the other way round: the parameters
        // move to the left of `=` and the two spellings settle to one definition. A definition that
        // already wrote parameters keeps a lambda body as its result. Only a lambda the source wrote
        // moves — a `.field` getter is a block too, but its parameter is synthesized, and lifting it
        // would name a definition's parameter something the author never wrote.
        if (params.isEmpty() && bodyNode.kind() == SyntaxKind.LAMBDA_EXPR
                && body instanceof Ast.Block lambda) {
            for (String p : lambda.params()) {
                params.add(new Ast.FnParam(p, null, false, lambda.pos()));
            }
            body = lambda.body();
        }
        // a pattern parameter took a fresh name above; it opens itself at the top of the body, so
        // the helper still takes plain names and nothing downstream sees a pattern
        for (int i = paramPatterns.size() - 1; i >= 0; i--) {
            SyntaxNode pat = paramPatterns.get(i);
            if (pat != null) {
                // positioned on the pattern: what a complaint about it has to name is the parameter
                // the author wrote, not the definition it sits in
                SourcePos at = pos(pat);
                body = bindPattern(pat, new Ast.Var(params.get(i).name(), at), body, at);
            }
        }
        return new Ast.FnDef(name, params, declaredReturn, null, body, partial, pos);
    }

    private Ast.FnParam fnParam(SyntaxNode p, SyntaxNode pat) {
        String name = pat == null ? firstIdentText(p) : "$p" + (patternCounter++);
        Ast.RetType type = null;
        Optional<SyntaxNode> rt = p.child(SyntaxKind.RET_TYPE);
        if (rt.isPresent()) {
            type = retType(rt.get());
        }
        if (type == null && pat != null && pat.kind() == SyntaxKind.PATTERN_CTOR) {
            // `let count (Tags(xs))` says the parameter is a Tags; writing `: Tags` beside it would
            // only repeat what the pattern already named
            SourcePos at = pos(pat);
            type = new Ast.RetType(List.of(new Ast.TypeRef(qualifiedNameText(pat), null, at)), at);
            return new Ast.FnParam(name, type, true, pos(p));
        }
        return new Ast.FnParam(name, type, pos(p));
    }

    private SyntaxNode optionalPatternChild(SyntaxNode n) {
        for (SyntaxNode c : n.childNodes()) {
            if (isPatternKind(c.kind())) {
                return c;
            }
        }
        return null;
    }

    private Ast.FnType fnType(SyntaxNode n) {
        List<Ast.RetType> params = new ArrayList<>();
        Ast.RetType result = null;
        boolean afterArrow = false;
        for (SyntaxElement e : meaningful(n)) {
            if (e instanceof SyntaxToken t && t.kind() == SyntaxKind.ARROW) {
                afterArrow = true;
            } else if (e instanceof SyntaxNode c && c.kind() == SyntaxKind.RET_TYPE) {
                if (afterArrow) {
                    result = retType(c);
                } else {
                    params.add(retType(c));
                }
            }
        }
        return new Ast.FnType(params, result, pos(n));
    }

    // --- types ---

    private Ast.RetType retType(SyntaxNode n) {
        List<Ast.TypeTerm> cases = new ArrayList<>();
        for (SyntaxNode c : n.childNodes()) {
            if (isTypeTermKind(c.kind())) {
                cases.add(typeTerm(c));
            }
        }
        if (n.token(SyntaxKind.QUESTION).isPresent()) {
            cases = List.of(optional(cases, pos(n)));
        }
        return new Ast.RetType(cases, cases.get(0).pos());
    }

    private static boolean isTypeTermKind(SyntaxKind k) {
        return k == SyntaxKind.TYPE_REF || k == SyntaxKind.TUPLE_TYPE || k == SyntaxKind.FN_TYPE;
    }

    /** One term of a written type: a function type, or a reference. A parenthesised single term is
     * grouping, so {@code ((Int) -> Bool)} is the function type it wraps rather than a one-tuple. */
    private Ast.TypeTerm typeTerm(SyntaxNode n) {
        if (n.kind() == SyntaxKind.FN_TYPE) {
            return fnType(n);
        }
        if (n.kind() == SyntaxKind.TUPLE_TYPE) {
            List<SyntaxNode> elems = new ArrayList<>();
            for (SyntaxNode c : n.childNodes()) {
                if (isTypeTermKind(c.kind())) {
                    elems.add(c);
                }
            }
            if (elems.size() == 1) {
                return typeTerm(elems.get(0));
            }
        }
        return typeRef(n);
    }

    /**
     * {@code T?} in a signature — a stdlib combinator that consumes an optional says so in its own
     * type ({@code List.filterMap(f: ('a) -> 'b?, …)}). Like a type variable it is written only in the
     * shipped core: a user still writes an optional on a field and never names one anywhere else
     * (ADR-0011), so the type stays out of the surface language. A sum cannot take the mark — an
     * absent {@code A | B} has no case to be absent as.
     */
    private Ast.TypeRef optional(List<Ast.TypeTerm> cases, SourcePos pos) {
        if (!isReservedNamespace(moduleName)) {
            throw errorWithHint(pos, "parse.optional.core", "parse.optional.core.hint",
                    "an optional type `T?` may be written only on a data field, or in the core (the"
                            + " reserved `souther` namespace); a user model never names an optional"
                            + " elsewhere (ADR-0011). On the result of a helper, leave the type off and"
                            + " the optional is inferred; where the model owns the absence, answer a"
                            + " list of nought or one and use `List.concatMap`");
        }
        if (cases.size() > 1) {
            throw error(pos, "parse.optional.sum",
                    "`?` marks a single type optional, but it follows a sum of "
                            + cases.size() + " cases");
        }
        // `T?` is `Option<T>` for whatever T is: the two spellings are one type, and what may
        // stand in a position is decided by what the position requires of that type, not here
        return new Ast.TypeRef("Option", cases.get(0), cases.get(0).pos());
    }

    private Ast.TypeRef typeRef(SyntaxNode n) {
        if (n.kind() == SyntaxKind.TUPLE_TYPE) {
            List<Ast.TypeTerm> elems = new ArrayList<>();
            for (SyntaxNode c : n.childNodes()) {
                if (isTypeTermKind(c.kind())) {
                    elems.add(typeTerm(c));
                }
            }
            if (elems.size() == 1 && elems.get(0) instanceof Ast.TypeRef only) {
                return only;   // `(T)` reads as grouping
            }
            return new Ast.TypeRef(null, null, elems, pos(n));
        }
        Optional<SyntaxToken> typevar = n.token(SyntaxKind.TYPEVAR);
        if (typevar.isPresent()) {
            String v = typevar.get().text();
            if (!isReservedNamespace(moduleName)) {
                throw error(pos(n), "parse.typevar.core",
                        "type variable `" + v + "` is only allowed in the core (the reserved `souther`"
                                + " namespace); a user model stays bounded (ADR-0028)", v);
            }
            return new Ast.TypeRef(v, null, pos(n));   // name begins with `'` → Type.Var
        }
        String name = qualifiedNameText(n);   // `Amount`, or `example.billing.Amount` / `B.Amount`
        Optional<SyntaxNode> args = n.child(SyntaxKind.TYPE_ARGS);
        if (args.isEmpty()) {
            return new Ast.TypeRef(name, null, pos(n));
        }
        List<Ast.TypeTerm> typeArgs = new ArrayList<>();
        for (SyntaxNode c : args.get().childNodes()) {
            if (isTypeTermKind(c.kind())) {
                typeArgs.add(typeTerm(c));
            }
        }
        if (typeArgs.isEmpty()) {
            return new Ast.TypeRef(name, null, pos(n));   // the missing argument is reported by name
        }
        if (name.equals("Map")) {
            // carry the value in `arg` and the key in `tupleElems` (ADR-0040)
            Ast.TypeTerm key = typeArgs.get(0);
            Ast.TypeTerm value = typeArgs.get(typeArgs.size() - 1);
            return new Ast.TypeRef("Map", value, List.of(key), pos(n));
        }
        return new Ast.TypeRef(name, typeArgs.get(0), pos(n));   // List<T> / Set<T> / Option<T>
    }

    // --- expressions ---

    private Ast.Expr expr(SyntaxNode n) {
        return switch (n.kind()) {
            case LITERAL_EXPR -> literal(n);
            case VAR_EXPR -> new Ast.Var(firstIdentText(n), pos(n));
            case FIELD_ACCESS -> fieldAccess(n);
            case CALL_EXPR -> call(n);
            case BINARY_EXPR -> binary(n);
            case UNARY_EXPR -> new Ast.Neg(expr(onlyExpr(n)), pos(n));
            case PIPE_EXPR -> pipe(n);
            case PAREN_EXPR -> expr(onlyExpr(n));
            case TUPLE_EXPR -> new Ast.Tuple(exprList(n), pos(n));
            case LIST_EXPR -> new Ast.ListLit(exprList(n), pos(n));
            case LIST_COMP -> listComp(n);
            case IF_EXPR -> ifExpr(n);
            case MATCH_EXPR -> matchExpr(n);
            case LAMBDA_EXPR -> lambda(n);
            case FIELD_GETTER -> fieldGetter(n);
            case NEW_DATA_EXPR -> newData(n);
            case BLOCK_EXPR -> block(n);
            default -> throw error(pos(n), "parse.expr", "expected an expression");
        };
    }

    private Ast.Expr literal(SyntaxNode n) {
        SyntaxToken t = firstMeaningfulToken(n);
        SourcePos pos = posOf(t);
        return switch (t.kind()) {
            case INT_LIT -> new Ast.IntLit(Long.parseLong(t.text()), pos);
            case DECIMAL_LIT -> new Ast.DecimalLit(new BigDecimal(stripDecimalSuffix(t.text())), pos);
            case STRING_LIT -> new Ast.StringLit(stringValue(t.text()), pos);
            case TRUE_KW -> new Ast.BoolLit(true, pos);
            case FALSE_KW -> new Ast.BoolLit(false, pos);
            default -> throw error(pos, "parse.expr", "expected a literal");
        };
    }

    private Ast.Expr fieldAccess(SyntaxNode n) {
        Ast.Expr target = expr(firstExprChild(n));
        SyntaxToken field = lastIdentToken(n);
        return new Ast.FieldAccess(target, field.text(), posOf(field));
    }

    private Ast.Expr call(SyntaxNode n) {
        StringBuilder fn = new StringBuilder();
        SyntaxToken first = null;
        for (SyntaxElement e : meaningful(n)) {
            if (e instanceof SyntaxToken t && t.kind() == SyntaxKind.IDENT) {
                if (fn.length() > 0) {
                    fn.append('.');
                }
                fn.append(t.text());
                if (first == null) {
                    first = t;
                }
            }
        }
        List<Ast.Expr> args = new ArrayList<>();
        n.child(SyntaxKind.ARG_LIST).ifPresent(list -> {
            for (SyntaxNode a : exprChildren(list)) {
                args.add(expr(a));
            }
        });
        return new Ast.Call(fn.toString(), args, posOf(first));
    }

    private Ast.Expr binary(SyntaxNode n) {
        List<SyntaxNode> operands = exprChildren(n);
        SyntaxToken op = operatorToken(n);
        return new Ast.Binary(binOp(op.kind()), expr(operands.get(0)), expr(operands.get(1)), posOf(op));
    }

    private static Ast.BinOp binOp(SyntaxKind k) {
        return switch (k) {
            case EQ -> Ast.BinOp.EQ;
            case NE -> Ast.BinOp.NE;
            case LT -> Ast.BinOp.LT;
            case LE -> Ast.BinOp.LE;
            case GT -> Ast.BinOp.GT;
            case GE -> Ast.BinOp.GE;
            case AND -> Ast.BinOp.AND;
            case OR -> Ast.BinOp.OR;
            case PLUS -> Ast.BinOp.ADD;
            case MINUS -> Ast.BinOp.SUB;
            case STAR -> Ast.BinOp.MUL;
            case SLASH -> Ast.BinOp.DIV;
            case PLUSPLUS -> Ast.BinOp.CONCAT;
            default -> throw new IllegalStateException("not a binary operator: " + k);
        };
    }

    /** {@code e |> f(a)} → {@code f(a, e)}; {@code e |> f} → {@code f(e)}; {@code e |> Mod.name}
     * → {@code Mod.name(e)} (spec §pipe). */
    private Ast.Expr pipe(SyntaxNode n) {
        List<SyntaxNode> operands = exprChildren(n);
        Ast.Expr left = expr(operands.get(0));
        Ast.Expr right = expr(operands.get(1));
        if (right instanceof Ast.Call c) {
            List<Ast.Expr> args = new ArrayList<>(c.args());
            args.add(left);
            return new Ast.Call(c.fn(), args, c.pos());
        }
        if (right instanceof Ast.Var v) {
            return new Ast.Call(v.name(), List.of(left), v.pos());
        }
        if (right instanceof Ast.FieldAccess fa && fa.target() instanceof Ast.Var base) {
            return new Ast.Call(base.name() + "." + fa.field(), List.of(left), fa.pos());
        }
        throw CompileException.of(
                Diagnostic.of(null, "parse.vpipe.right").title("parse.title").at(right.pos()).build(),
                "the right side of `|>` must be a function call or a function name");
    }

    private Ast.Expr listComp(SyntaxNode n) {
        List<SyntaxNode> exprs = exprChildren(n);
        Ast.Expr element = expr(exprs.get(0));
        List<Ast.Expr> guards = new ArrayList<>();
        for (int i = 1; i < exprs.size(); i++) {
            guards.add(expr(exprs.get(i)));
        }
        return new Ast.ListComp(element, guards, pos(n));
    }

    private Ast.Expr ifExpr(SyntaxNode n) {
        List<SyntaxNode> exprs = exprChildren(n);
        String binder = attemptBinder(n);
        return binder == null
                ? new Ast.If(expr(exprs.get(0)), expr(exprs.get(1)), expr(exprs.get(2)), pos(n))
                : new Ast.IfConstructed(expr(exprs.get(0)), binder,
                        expr(exprs.get(1)), expr(exprs.get(2)), pos(n));
    }

    /** The {@code x} of an attempted construction's {@code as x}, or {@code null} where none was
     * written. The binder is the identifier following {@code as} among the form's own tokens; the
     * condition is a child node, so its identifiers are not among them. */
    private static String attemptBinder(SyntaxNode n) {
        boolean afterAs = false;
        for (SyntaxElement e : n.children()) {
            if (!(e instanceof SyntaxToken t)) continue;
            if (t.kind() == SyntaxKind.AS_KW) {
                afterAs = true;
            } else if (afterAs && t.kind() == SyntaxKind.IDENT) {
                return t.text();
            }
        }
        return null;
    }

    /** {@code (p, ...) -> body}. A parameter that is more than a name takes a fresh one and opens
     * itself at the top of the body, so the block keeps taking plain names and nothing downstream
     * has to know a pattern was written. */
    private Ast.Expr lambda(SyntaxNode n) {
        SourcePos pos = pos(n);
        List<SyntaxNode> pats = patternChildren(n);
        List<String> params = new ArrayList<>();
        for (SyntaxNode p : pats) {
            params.add(p.kind() == SyntaxKind.PATTERN_NAME
                    ? firstIdentText(p)
                    : "$p" + (patternCounter++));
        }
        Ast.Expr body = expr(lastExprChild(n));
        for (int i = pats.size() - 1; i >= 0; i--) {
            if (pats.get(i).kind() != SyntaxKind.PATTERN_NAME) {
                SourcePos at = pos(pats.get(i));
                body = bindPattern(pats.get(i), new Ast.Var(params.get(i), at), body, at);
            }
        }
        return new Ast.Block(params, body, pos);
    }

    private Ast.Expr fieldGetter(SyntaxNode n) {
        // `.field` desugars to the getter (x) -> x.field: an ordinary single-param block. The param
        // is bound and read only inside this block, so it shadows any same-named outer name; the
        // inliner alpha-renames it on inline. The `$g` prefix + counter only keep synthesized names
        // apart from each other (the same scheme as `$m`/`$t`); `$` is a legal identifier character.
        SyntaxToken field = lastIdentToken(n);
        SourcePos pos = pos(n);
        String param = "$g" + (getterCounter++);
        Ast.Expr body = new Ast.FieldAccess(new Ast.Var(param, pos), field.text(), posOf(field));
        return new Ast.Block(List.of(param), body, pos);
    }

    private Ast.Expr newData(SyntaxNode n) {
        SyntaxToken head = identTokens(n).get(0);
        Ast.Name typeName = Ast.Name.written(head.text(), posOf(head));
        List<Ast.FieldInit> inits = new ArrayList<>();
        List<Ast.ValueRef> spreads = new ArrayList<>();
        // a spread naming a field path (`...c.address`) binds that path first, so the construction
        // itself still spreads a plain local: `let $s0 = c.address in Address { ...$s0, ... }`
        List<String> pathNames = new ArrayList<>();
        List<Ast.Expr> pathValues = new ArrayList<>();
        for (SyntaxNode c : n.childNodes()) {
            if (c.kind() == SyntaxKind.SPREAD_MEMBER) {
                List<SyntaxToken> path = identTokens(c);
                if (path.size() == 1) {
                    spreads.add(Ast.ValueRef.written(path.get(0).text(), posOf(path.get(0))));
                } else {
                    String bound = "$s" + (spreadCounter++);
                    Ast.Expr value = new Ast.Var(path.get(0).text(), posOf(path.get(0)));
                    for (int i = 1; i < path.size(); i++) {
                        value = new Ast.FieldAccess(value, path.get(i).text(), posOf(path.get(i)));
                    }
                    pathNames.add(bound);
                    pathValues.add(value);
                    // the path was bound just above, so what the construction spreads is that binding
                    spreads.add(Ast.ValueRef.local(bound, posOf(path.get(0))));
                }
            } else if (c.kind() == SyntaxKind.FIELD_INIT) {
                String field = firstIdentText(c);
                Optional<SyntaxNode> value = firstExprChildOpt(c);
                Ast.Expr v = value.isPresent()
                        ? expr(value.get())
                        : new Ast.Var(field, pos(c));   // shorthand `field` means `field = field`
                inits.add(new Ast.FieldInit(field, v, pos(c)));
            }
        }
        Ast.Expr built = new Ast.NewData(typeName, inits, spreads, null, pos(n));
        for (int i = pathNames.size() - 1; i >= 0; i--) {
            built = new Ast.LetIn(pathNames.get(i), pathValues.get(i), built, pos(n));
        }
        return built;
    }

    private Ast.Expr matchExpr(SyntaxNode n) {
        List<SyntaxNode> exprs = exprChildren(n);
        Ast.Expr scrutinee = expr(exprs.get(0));
        List<Ast.Case> cases = new ArrayList<>();
        for (SyntaxNode c : childNodes(n, SyntaxKind.MATCH_CASE)) {
            cases.add(matchCase(c));
        }
        return new Ast.Match(scrutinee, cases, pos(n));
    }

    /** A name as the source wrote it — bare, or qualified through a module or an import alias — read
     * from a run of tokens the parser did not wrap in a node. Advances {@code at} past the name, and
     * positions the name at its first identifier so a diagnostic points at the name, not the clause. */
    private Ast.Name dottedName(List<SyntaxElement> es, int[] at) {
        SyntaxElement head = es.get(at[0]++);
        StringBuilder sb = new StringBuilder(tokenText(head));
        while (at[0] + 1 < es.size() && isToken(es.get(at[0]), SyntaxKind.DOT)
                && isToken(es.get(at[0] + 1), SyntaxKind.IDENT)) {
            at[0]++;                              // .
            sb.append('.').append(tokenText(es.get(at[0]++)));
        }
        return Ast.Name.written(sb.toString(), posOf((SyntaxToken) head));
    }

    /** The comma-separated names of a {@code constructs}/{@code depends on} clause, each possibly
     * qualified by its module. {@code skipIdents} drops the identifiers that belong to the keyword
     * rather than to the list — the {@code on} of {@code depends on} lexes as one. */
    private List<Ast.Name> dottedNames(SyntaxNode clause, int skipIdents) {
        List<Ast.Name> out = new ArrayList<>();
        List<SyntaxElement> es = meaningful(clause);
        int[] at = {1 + skipIdents};              // past the clause keyword
        while (at[0] < es.size()) {
            if (isToken(es.get(at[0]), SyntaxKind.COMMA)) {
                at[0]++;
                continue;
            }
            out.add(dottedName(es, at));
        }
        return out;
    }

    private Ast.Case matchCase(SyntaxNode n) {
        List<SyntaxElement> es = meaningful(n);
        SourcePos casePos = pos(n);
        int[] at = {0};
        List<Ast.Name> caseTypes = new ArrayList<>();
        caseTypes.add(dottedName(es, at));
        while (at[0] + 1 < es.size() && isToken(es.get(at[0]), SyntaxKind.PIPE)
                && isToken(es.get(at[0] + 1), SyntaxKind.IDENT)) {
            at[0]++;                              // |
            caseTypes.add(dottedName(es, at));
        }
        int i = at[0];
        // newtype constructor destructuring `X(inner)` / nested `X(Y(s))`: the ident chain inside the
        // parens. The last ident is the bound variable; each earlier ident names a newtype layer peeled.
        List<Ast.Name> unwrapNames = new ArrayList<>();
        if (i < es.size() && isToken(es.get(i), SyntaxKind.LPAREN)) {
            int depth = 0;
            while (at[0] < es.size()) {
                SyntaxElement e = es.get(at[0]);
                if (isToken(e, SyntaxKind.LPAREN)) {
                    depth++;
                    at[0]++;
                } else if (isToken(e, SyntaxKind.RPAREN)) {
                    depth--;
                    at[0]++;
                    if (depth == 0) {
                        break;
                    }
                } else if (isToken(e, SyntaxKind.IDENT)) {
                    unwrapNames.add(dottedName(es, at));   // a layer is named like any other type
                } else {
                    break;
                }
            }
            i = at[0];
        }
        // Option's positional binding `Some v`: a bare identifier before `{` / `as` / `->`. It never
        // follows a constructor destructure, so a trailing ident after the parens is not consumed here.
        String someBinding = null;
        if (unwrapNames.isEmpty() && i < es.size() && isToken(es.get(i), SyntaxKind.IDENT)) {
            someBinding = tokenText(es.get(i++));
        }
        // field destructuring `{ field [= var], ... }`
        List<String> fieldNames = new ArrayList<>();
        List<String> fieldVars = new ArrayList<>();
        if (i < es.size() && isToken(es.get(i), SyntaxKind.LBRACE)) {
            i++;   // {
            while (i < es.size() && !isToken(es.get(i), SyntaxKind.RBRACE)) {
                String field = tokenText(es.get(i++));
                String var = field;
                if (i < es.size() && isToken(es.get(i), SyntaxKind.ASSIGN)) {
                    i++;
                    var = tokenText(es.get(i++));
                }
                fieldNames.add(field);
                fieldVars.add(var);
                if (i < es.size() && isToken(es.get(i), SyntaxKind.COMMA)) {
                    i++;
                }
            }
            if (i < es.size()) {
                i++;   // }
            }
        }
        // whole-value binding `as x`
        String asBinding = null;
        if (i < es.size() && isToken(es.get(i), SyntaxKind.AS_KW)) {
            i++;
            asBinding = tokenText(es.get(i++));
        }
        boolean isSome = caseTypes.size() == 1 && caseTypes.get(0).written().equals("Some");
        if (isSome && asBinding != null) {
            throw error(casePos, "parse.option.positional",
                    "Option's wrapped value is bound positionally: write `| Some v`, not `| Some as v`");
        }
        // `Some(a)` opens nothing (unlike `X(a)` on a user case); the whole-element spelling is `Some v`.
        // Only `Some(X(...))`, which opens a wrapped newtype, uses the paren form.
        if (isSome && unwrapNames.size() == 1) {
            throw error(casePos, "parse.option.positional",
                    "write `| Some v` to bind the whole value; `Some(...)` opens a wrapped newtype, as in `| Some(" + unwrapNames.get(0).written() + "(v))`");
        }
        // skip the arrow, then the body is the trailing expression node
        Ast.Expr body = expr(lastExprChild(n));

        String binding = someBinding != null ? someBinding : asBinding;
        if (!fieldNames.isEmpty()) {
            String whole = binding != null ? binding : "$m" + (matchWholeCounter++);
            for (int k = fieldNames.size() - 1; k >= 0; k--) {
                body = new Ast.LetIn(fieldVars.get(k),
                        new Ast.FieldAccess(new Ast.Var(whole, casePos), fieldNames.get(k), casePos),
                        body, casePos);
            }
            binding = whole;
        } else if (!unwrapNames.isEmpty()) {
            String whole = binding != null ? binding : "$m" + (matchWholeCounter++);
            // open the case's newtype (whole.value), then peel one layer per earlier name; the last
            // name binds the value reached — `アクティベート済み(メールアドレス(s))` binds s to whole.value.value.
            // Option's `Some` binds the unwrapped element already (codegen strips the wrapper), so its
            // first named layer opens that element directly — `Some(従業員ID(v))` binds v to whole.value.
            Ast.Expr target = isSome
                    ? new Ast.Var(whole, casePos)
                    : new Ast.FieldAccess(new Ast.Var(whole, casePos), "value", casePos);
            for (int k = 0; k < unwrapNames.size() - 1; k++) {
                target = new Ast.FieldAccess(target, "value", casePos);
            }
            body = new Ast.LetIn(unwrapNames.get(unwrapNames.size() - 1).written(), target, body, casePos);
            binding = whole;
        }
        // null = no constructor destructure; otherwise the inner names (before the bound variable),
        // which the type checker prepends the case type to when verifying the opened layers.
        List<Ast.Name> unwrapAsserts = unwrapNames.isEmpty()
                ? null
                : new ArrayList<>(unwrapNames.subList(0, unwrapNames.size() - 1));
        return new Ast.Case(caseTypes, binding, body, unwrapAsserts, casePos);
    }

    /** A brace block: its {@code let}/{@code guard} statements folded into the result expression. */
    private Ast.Expr block(SyntaxNode n) {
        List<SyntaxNode> stmts = new ArrayList<>();
        SyntaxNode result = null;
        for (SyntaxNode c : n.childNodes()) {
            switch (c.kind()) {
                case LET_STMT, LET_DESTRUCTURE, GUARD_STMT -> stmts.add(c);
                default -> result = c;   // the trailing result expression
            }
        }
        return foldStatements(stmts, 0, result);
    }

    private Ast.Expr foldStatements(List<SyntaxNode> stmts, int index, SyntaxNode result) {
        if (index == stmts.size()) {
            return expr(result);   // a block always ends in a result expression
        }
        SyntaxNode s = stmts.get(index);
        SourcePos pos = pos(s);
        return switch (s.kind()) {
            case LET_STMT -> {
                Ast.RetType annotation = s.child(SyntaxKind.RET_TYPE).map(this::retType).orElse(null);
                Ast.Expr value = expr(onlyExpr(s));
                Ast.Expr rest = foldStatements(stmts, index + 1, result);
                yield annotation == null
                        ? new Ast.LetIn(firstIdentText(s), value, rest, pos)
                        : Ast.LetIn.annotated(firstIdentText(s), value, annotation, rest, pos);
            }
            case GUARD_STMT -> {
                List<SyntaxNode> exprs = exprChildren(s);
                String binder = attemptBinder(s);
                Ast.Expr rest = foldStatements(stmts, index + 1, result);
                yield binder == null
                        ? new Ast.If(expr(exprs.get(0)), rest, expr(exprs.get(1)), pos)
                        : new Ast.IfConstructed(expr(exprs.get(0)), binder, rest,
                                expr(exprs.get(1)), pos);
            }
            case LET_DESTRUCTURE -> {
                SyntaxNode pat = patternChild(s);
                yield bindPattern(pat, expr(onlyExpr(s)),
                        foldStatements(stmts, index + 1, result), pos(pat));
            }
            default -> throw error(pos, "parse.expr", "unexpected statement");
        };
    }

    /**
     * A pattern binding {@code value}, with {@code rest} in its scope. Every shape lowers to the
     * ordinary reads it stands for — a tuple to indexed gets, a newtype to {@code .value}, a record
     * to field reads — so nothing past this point has to know a pattern was written. It is the same
     * lowering a {@code match} arm does; the difference is only that here there is one arm.
     */
    private Ast.Expr bindPattern(SyntaxNode pat, Ast.Expr value, Ast.Expr rest, SourcePos pos) {
        return switch (pat.kind()) {
            case PATTERN_NAME -> new Ast.LetIn(firstIdentText(pat), value, rest, pos);
            case PATTERN_TUPLE -> {
                List<SyntaxNode> elems = patternChildren(pat);
                if (elems.size() == 1) {
                    yield bindPattern(elems.get(0), value, rest, pos);   // `(p)` is grouping
                }
                String whole = "$t" + (tupleCounter++);
                Ast.Expr body = rest;
                for (int i = elems.size() - 1; i >= 0; i--) {
                    body = bindPattern(elems.get(i),
                            new Ast.TupleGet(new Ast.Var(whole, pos), i, elems.size(), pos), body, pos);
                }
                yield new Ast.LetIn(whole, value, body, pos);
            }
            case PATTERN_CTOR -> {
                String whole = "$p" + (patternCounter++);
                Ast.Expr inner = new Ast.FieldAccess(new Ast.Var(whole, pos), "value", pos);
                Ast.Expr body = bindPattern(patternChild(pat), inner, rest, pos);
                yield Ast.LetIn.opening(whole, value,
                        Ast.Name.written(qualifiedNameText(pat), pos(pat)), body, pos);
            }
            case PATTERN_RECORD -> {
                String whole = "$r" + (patternCounter++);
                Ast.Expr body = rest;
                List<SyntaxNode> fields = childNodes(pat, SyntaxKind.PATTERN_FIELD);
                for (int k = fields.size() - 1; k >= 0; k--) {
                    List<SyntaxToken> names = identTokens(fields.get(k));
                    String field = names.get(0).text();
                    String var = names.size() > 1 ? names.get(1).text() : field;
                    body = new Ast.LetIn(var,
                            new Ast.FieldAccess(new Ast.Var(whole, pos), field, pos), body, pos);
                }
                yield new Ast.LetIn(whole, value, body, pos);
            }
            default -> throw error(pos, "parse.expr", "unexpected pattern");
        };
    }

    private static boolean isPatternKind(SyntaxKind k) {
        return k == SyntaxKind.PATTERN_NAME || k == SyntaxKind.PATTERN_TUPLE
                || k == SyntaxKind.PATTERN_CTOR || k == SyntaxKind.PATTERN_RECORD;
    }

    private SyntaxNode patternChild(SyntaxNode n) {
        for (SyntaxNode c : n.childNodes()) {
            if (isPatternKind(c.kind())) {
                return c;
            }
        }
        throw new IllegalStateException("no pattern in " + n.kind());
    }

    private List<SyntaxNode> patternChildren(SyntaxNode n) {
        List<SyntaxNode> out = new ArrayList<>();
        for (SyntaxNode c : n.childNodes()) {
            if (isPatternKind(c.kind())) {
                out.add(c);
            }
        }
        return out;
    }

    // --- CST navigation helpers ---

    private List<Ast.Expr> exprList(SyntaxNode n) {
        List<Ast.Expr> out = new ArrayList<>();
        for (SyntaxNode c : exprChildren(n)) {
            out.add(expr(c));
        }
        return out;
    }

    /** The direct child nodes that are expressions, in order. */
    private List<SyntaxNode> exprChildren(SyntaxNode n) {
        List<SyntaxNode> out = new ArrayList<>();
        for (SyntaxNode c : n.childNodes()) {
            if (isExprKind(c.kind())) {
                out.add(c);
            }
        }
        return out;
    }

    private SyntaxNode firstExprChild(SyntaxNode n) {
        return exprChildren(n).get(0);
    }

    private Optional<SyntaxNode> firstExprChildOpt(SyntaxNode n) {
        List<SyntaxNode> c = exprChildren(n);
        return c.isEmpty() ? Optional.empty() : Optional.of(c.get(0));
    }

    private SyntaxNode lastExprChild(SyntaxNode n) {
        List<SyntaxNode> c = exprChildren(n);
        return c.get(c.size() - 1);
    }

    /** The single expression child of a node that wraps exactly one (a block statement, an invariant,
     * a unary/fn body). */
    private SyntaxNode onlyExpr(SyntaxNode n) {
        return firstExprChild(n);
    }

    private static boolean isExprKind(SyntaxKind k) {
        return switch (k) {
            case LITERAL_EXPR, VAR_EXPR, FIELD_ACCESS, CALL_EXPR, BINARY_EXPR, UNARY_EXPR, PIPE_EXPR,
                 PAREN_EXPR, TUPLE_EXPR, LIST_EXPR, LIST_COMP, IF_EXPR, MATCH_EXPR, LAMBDA_EXPR,
                 FIELD_GETTER, NEW_DATA_EXPR, BLOCK_EXPR -> true;
            default -> false;
        };
    }

    private List<SyntaxNode> childNodes(SyntaxNode n, SyntaxKind kind) {
        List<SyntaxNode> out = new ArrayList<>();
        for (SyntaxNode c : n.childNodes()) {
            if (c.kind() == kind) {
                out.add(c);
            }
        }
        return out;
    }

    /** The direct IDENT tokens of a node, in order (skipping keywords, punctuation, and trivia). */
    private List<SyntaxToken> identTokens(SyntaxNode n) {
        List<SyntaxToken> out = new ArrayList<>();
        for (SyntaxElement e : n.children()) {
            if (e instanceof SyntaxToken t && t.kind() == SyntaxKind.IDENT) {
                out.add(t);
            }
        }
        return out;
    }

    /** The name a top-level declaration declares: the first identifier in it. This is how the
     * builder names a {@code data}, a {@code behavior} and a {@code let}, and how the declaration's
     * source is filed under the same name when a module publishes what it declares. */
    static String firstIdentText(SyntaxNode n) {
        for (SyntaxElement e : n.children()) {
            if (e instanceof SyntaxToken t && t.kind() == SyntaxKind.IDENT) {
                return t.text();
            }
        }
        throw new IllegalStateException("no identifier in " + n.kind());
    }

    private SyntaxToken lastIdentToken(SyntaxNode n) {
        SyntaxToken last = null;
        for (SyntaxElement e : n.children()) {
            if (e instanceof SyntaxToken t && t.kind() == SyntaxKind.IDENT) {
                last = t;
            }
        }
        return last;
    }

    private SyntaxToken operatorToken(SyntaxNode n) {
        for (SyntaxElement e : n.children()) {
            if (e instanceof SyntaxToken t && !t.isTrivia() && isBinaryOperator(t.kind())) {
                return t;
            }
        }
        throw new IllegalStateException("no operator in " + n.kind());
    }

    private static boolean isBinaryOperator(SyntaxKind k) {
        return switch (k) {
            case EQ, NE, LT, LE, GT, GE, AND, OR, PLUS, MINUS, STAR, SLASH, PLUSPLUS -> true;
            default -> false;
        };
    }

    private SyntaxNode typeChild(SyntaxNode n) {
        for (SyntaxNode c : n.childNodes()) {
            if (isTypeTermKind(c.kind())) {
                return c;
            }
        }
        throw new IllegalStateException("no type in " + n.kind());
    }

    private String qualifiedNameText(SyntaxNode n) {
        StringBuilder sb = new StringBuilder();
        for (SyntaxToken t : identTokens(n)) {
            if (sb.length() > 0) {
                sb.append('.');
            }
            sb.append(t.text());
        }
        return sb.toString();
    }

    private List<SyntaxElement> meaningful(SyntaxNode n) {
        List<SyntaxElement> out = new ArrayList<>();
        for (SyntaxElement e : n.children()) {
            if (e instanceof SyntaxNode || (e instanceof SyntaxToken t && !t.isTrivia())) {
                out.add(e);
            }
        }
        return out;
    }

    private static boolean isToken(SyntaxElement e, SyntaxKind kind) {
        return e instanceof SyntaxToken t && t.kind() == kind;
    }

    private static String tokenText(SyntaxElement e) {
        return ((SyntaxToken) e).text();
    }

    private SyntaxToken firstMeaningfulToken(SyntaxNode n) {
        for (SyntaxElement e : n.children()) {
            if (e instanceof SyntaxToken t && !t.isTrivia()) {
                return t;
            }
            if (e instanceof SyntaxNode c) {
                SyntaxToken inner = firstMeaningfulTokenOrNull(c);
                if (inner != null) {
                    return inner;
                }
            }
        }
        throw new IllegalStateException("no token under " + n.kind());
    }

    private SyntaxToken firstMeaningfulTokenOrNull(SyntaxNode n) {
        for (SyntaxElement e : n.children()) {
            if (e instanceof SyntaxToken t && !t.isTrivia()) {
                return t;
            }
            if (e instanceof SyntaxNode c) {
                SyntaxToken inner = firstMeaningfulTokenOrNull(c);
                if (inner != null) {
                    return inner;
                }
            }
        }
        return null;
    }

    private SourcePos pos(SyntaxNode n) {
        return lines.posOf(firstMeaningfulToken(n).start());
    }

    private SourcePos posOf(SyntaxToken t) {
        return lines.posOf(t.start());
    }

    /** The whole `{ ... }` of a body, so an error about the body underlines both braces. */
    private Region bodyRegion(SyntaxNode body) {
        SourcePos open = pos(body);
        return body.token(SyntaxKind.RBRACE)
                .map(close -> new Region(open, lines.posOf(close.end())))
                .orElseGet(() -> Region.point(open));
    }

    // --- literal decoding ---

    private static String stripDecimalSuffix(String raw) {
        return raw.endsWith("m") ? raw.substring(0, raw.length() - 1) : raw;
    }

    /** Decodes a raw string-literal slice (quotes and escapes included) to its value. */
    private static String stringValue(String raw) {
        int from = raw.startsWith("\"") ? 1 : 0;
        int to = raw.length() >= 2 && raw.endsWith("\"") ? raw.length() - 1 : raw.length();
        StringBuilder sb = new StringBuilder();
        for (int i = from; i < to; i++) {
            char c = raw.charAt(i);
            if (c == '\\' && i + 1 < to) {
                char e = raw.charAt(++i);
                sb.append(switch (e) {
                    case 'n' -> '\n';
                    case 't' -> '\t';
                    case 'r' -> '\r';
                    case '"' -> '"';
                    case '\\' -> '\\';
                    default -> e;
                });
            } else {
                sb.append(c);
            }
        }
        return sb.toString();
    }

    private CompileException error(SourcePos pos, String messageKey, String legacyMessage, Object... args) {
        return CompileException.of(
                Diagnostic.of(null, messageKey).title("parse.title").at(pos).args(args).build(),
                legacyMessage);
    }

    /** As {@link #error}, with a hint under it naming the way out. */
    private CompileException errorWithHint(SourcePos pos, String messageKey, String hintKey,
                                           String legacyMessage, Object... args) {
        return CompileException.of(
                Diagnostic.of(null, messageKey).title("parse.title").at(pos).args(args)
                        .hint(hintKey).build(),
                legacyMessage);
    }

    /** Whether {@code name} sits in the compiler-shipped {@code souther} namespace (ADR-0028); only
     * those modules may write type variables and {@code intrinsic} bodies. */
    private static boolean isReservedNamespace(String name) {
        return name.equals("souther") || name.startsWith("souther.");
    }
}
