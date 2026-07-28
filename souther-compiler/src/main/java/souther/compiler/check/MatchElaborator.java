package souther.compiler.check;

import souther.compiler.ast.Ast;
import souther.compiler.core.Core;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.SourcePos;
import souther.compiler.types.Type;
import souther.compiler.types.TypeName;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Typing a `match`: over a sum's cases, over an `Option`, and over a newtype's layers, plus the
 * exhaustiveness and unwrap checks each form is subject to.
 */
public final class MatchElaborator {

    private MatchElaborator() {}

    static Core elaborateMatch(Ast.Match m, Map<String, Type> env, CheckContext ctx,
                                       Type expected) {
        Core scrutinee = Elaborator.elaborate(m.scrutinee(), env, ctx);
        Type st = scrutinee.type();
        if (st instanceof Type.OptionOf oo) {
            return elaborateOptionMatch(m, scrutinee, oo.element(), env, ctx, expected);
        }
        if (st instanceof Type.Union union) {
            return elaborateCasesMatch(m, scrutinee, union.members(), "union `" + Type.show(union) + "`",
                    st, env, ctx, expected);
        }
        if (!(st instanceof Type.Ref ref) || !(ctx.symbols().get(ref.name()) instanceof Ast.SumData sum)) {
            throw CompileException.of(
                    Diagnostic.of(null, "check.match.notsum").title("check.match.title")
                            .at(m.pos(), 5).args(Type.show(st)).build(),
                    "match requires a sum-typed value, got " + st);
        }
        return elaborateCasesMatch(m, scrutinee, new HashSet<>(TypeOps.caseNames(sum)),
                "data `" + sum.name() + "`", st, env, ctx, expected);
    }

    /**
     * An arm names something that is not a case of what is being matched. When that name is a case of
     * another sum, say which — the author wrote an arm for a different match. The layout rule
     * (<<match>>) settles that by column, except where both matches are on one line: there the inner
     * match takes every `|` after it, so an arm meant for the outer one lands here, and the report
     * says how to end the inner match.
     */
    static CompileException notCase(Ast.Name written, String what, Ast.Case c, Ast.Match m,
                                            Set<TypeName> cases, Symbols symbols) {
        String caseName = written.written();
        String otherSum = null;
        for (TypeName name : symbols.visibleNames()) {
            if (!(symbols.get(name) instanceof Ast.SumData sum)) {
                continue;
            }
            List<TypeName> others = TypeOps.caseNames(sum);
            if (others.contains(written.denotes()) && !cases.containsAll(others)) {
                otherSum = sum.name();
                break;
            }
        }
        Diagnostic.Builder d = Diagnostic.of(null, "check.match.notcase").title("check.match.title")
                .at(c.pos()).args(caseName, what);
        if (otherSum != null) {
            d = d.hint("check.match.notcase.other", caseName, otherSum);
            if (c.pos().line() == m.pos().line()) {
                d = d.hint("check.match.notcase.online");
            }
        }
        return CompileException.of(d.build(), "`" + caseName + "` is not a case of " + what
                + (otherSum == null ? "" : " (it is a case of `" + otherSum + "`)"));
    }

    /** Match over a fixed set of data cases (a named sum's cases, or an anonymous union's members).
     * A single-case case binds that case's type; an or-pattern ({@code A | B}) binds {@code scrutinee}
     * (the sum type), since no one case type fits all its alternatives. Every case must be covered
     * exactly once (E1201; a second cover is an overlap error). */
    static Core elaborateCasesMatch(Ast.Match m, Core scrutineeCore, Set<TypeName> cases,
                                        String what, Type scrutinee,
                                        Map<String, Type> env, CheckContext ctx, Type expected) {
        Set<TypeName> covered = new HashSet<>();
        List<Core.Case> arms = new ArrayList<>();
        Type branchType = null;
        for (Ast.Case c : m.cases()) {
            for (Ast.Name written : c.caseTypes()) {
                TypeName caseName = written.denotes();
                if (!cases.contains(caseName)) {
                    throw notCase(written, what, c, m, cases, ctx.symbols());
                }
                if (!covered.add(caseName)) {
                    throw CompileException.of(
                            Diagnostic.of(null, "check.match.overlap").title("check.match.title")
                                    .at(c.pos()).args(written.written()).build(),
                            "`" + written.written() + "` is matched by more than one case");
                }
            }
            Type bindType = c.caseTypes().size() == 1
                    ? caseBindType(c.caseTypes().get(0).denotes()) : scrutinee;
            if (c.unwrapAsserts() != null) {
                if (c.caseTypes().size() != 1) {
                    throw CompileException.of(
                            Diagnostic.of(null, "check.match.newtype.orpattern").title("check.match.title")
                                    .at(c.pos()).build(),
                            "a constructor destructuring opens a single case, not an or-pattern");
                }
                checkUnwrapAsserts(c, ctx.symbols());
            }
            Core body = Elaborator.liftIntoOption(
                    Elaborator.elaborate(c.body(), bound(env, c.binding(), bindType), ctx, expected),
                    expected, ctx.symbols());
            arms.add(new Core.Case(denoted(c.caseTypes()), c.binding(), body, bindType, c.pos()));
            branchType = mergeBranch(m, branchType, body.type(), c);
        }
        List<String> missing = new ArrayList<>();
        for (TypeName caseName : cases) {
            if (!covered.contains(caseName)) {
                missing.add(caseName.name());
            }
        }
        if (!missing.isEmpty()) {
            missing.sort(null);
            throw nonExhaustive(m.pos(), what, missing);
        }
        if (branchType == null) {
            throw CompileException.of(
                    Diagnostic.of(null, "check.match.nocases").title("check.match.title")
                            .at(m.pos(), 5).build(),
                    "match has no cases");
        }
        return new Core.Match(scrutineeCore, arms, branchType, m.pos());
    }

    /** Match over {@code Option<element>}: cases are {@code Some} (binds the element) and
     * {@code None}; both must be present (spec 16.3). */
    static Core elaborateOptionMatch(Ast.Match m, Core scrutineeCore, Type element,
                                          Map<String, Type> env, CheckContext ctx, Type expected) {
        Set<TypeName> covered = new HashSet<>();
        List<Core.Case> arms = new ArrayList<>();
        Type branchType = null;
        for (Ast.Case c : m.cases()) {
            if (c.caseTypes().size() != 1) {
                throw CompileException.of(
                        Diagnostic.of(null, "check.match.option.orpattern").title("check.match.title")
                                .at(c.pos()).build(),
                        "or-patterns are not allowed in an Option match; use separate Some and None cases");
            }
            Ast.Name arm = c.caseTypes().get(0);
            String caseType = arm.written();
            Type bind;
            if (TypeName.SOME.equals(arm.denotes())) {
                bind = element;
            } else if (TypeName.NONE.equals(arm.denotes())) {
                bind = null;
            } else {
                throw CompileException.of(
                        Diagnostic.of(null, "check.match.option.notcase").title("check.match.title")
                                .at(c.pos()).args(caseType).build(),
                        "`" + caseType + "` is not a case of Option; use Some or None");
            }
            if (c.unwrapAsserts() != null) {
                if (!TypeName.SOME.equals(arm.denotes())) {
                    throw CompileException.of(
                            Diagnostic.of(null, "check.match.option.nopayload").title("check.match.title")
                                    .at(c.pos()).args(caseType).build(),
                            "`" + caseType + "` has no value, so it cannot be opened with `" + caseType + "(...)`");
                }
                checkOptionUnwrapAsserts(c, element, ctx.symbols());
            }
            if (!covered.add(arm.denotes())) {
                throw CompileException.of(
                        Diagnostic.of(null, "check.match.overlap").title("check.match.title")
                                .at(c.pos()).args(caseType).build(),
                        "`" + caseType + "` is matched by more than one case");
            }
            Core body = Elaborator.liftIntoOption(
                    Elaborator.elaborate(c.body(), bound(env, c.binding(), bind), ctx, expected),
                    expected, ctx.symbols());
            arms.add(new Core.Case(denoted(c.caseTypes()), c.binding(), body, bind, c.pos()));
            branchType = mergeBranch(m, branchType, body.type(), c);
        }
        List<String> missing = new ArrayList<>();
        for (TypeName caseName : List.of(TypeName.SOME, TypeName.NONE)) {
            if (!covered.contains(caseName)) {
                missing.add(caseName.name());
            }
        }
        if (!missing.isEmpty()) {
            throw nonExhaustive(m.pos(), "Option", missing);
        }
        return new Core.Match(scrutineeCore, arms, branchType, m.pos());
    }

    /** What each arm name denotes — what a {@code Core} arm dispatches on. */
    static List<TypeName> denoted(List<Ast.Name> names) {
        List<TypeName> out = new ArrayList<>();
        for (Ast.Name n : names) {
            out.add(n.denotes());
        }
        return out;
    }

    /** The type a match case binds. A primitive-named case (e.g. {@code Int} in {@code Int |
     * DivisionByZero}) binds that primitive; a data-named case binds its data type. Option's own
     * cases bind nothing readable here — an Option match binds the element, which
     * {@link #elaborateOptionMatch} knows and this does not. */
    public static Type caseBindType(TypeName caseName) {
        if (!caseName.isPrimitive()) {
            return Type.ref(caseName);
        }
        return switch (caseName.name()) {
            case "Int" -> Type.INT;
            case "String" -> Type.STRING;
            case "Bool" -> Type.BOOL;
            case "Decimal" -> Type.DECIMAL;
            case "Date" -> Type.DATE;
            case "DateTime" -> Type.DATETIME;
            default -> null;
        };
    }

    /** A constructor-destructuring pattern {@code X(Y(s))} opens one newtype per layer: {@code X}
     * (the matched case) then each written inner name. Every opened layer MUST be a newtype, and each
     * inner name MUST equal the newtype the previous layer wraps, or it is a compile error (Elm/F#
     * parity — the constructor in the pattern is type-checked, and a non-newtype cannot be opened). */
    static void checkUnwrapAsserts(Ast.Case c, Symbols symbols) {
        List<Ast.Name> opened = new ArrayList<>();
        opened.add(c.caseTypes().get(0));
        opened.addAll(c.unwrapAsserts());
        checkOpenedLayers(c, opened, symbols, true);
    }

    /** {@code Some(X(v))} opens the Option's element in the pattern. Unlike a user case, {@code Some}
     * is not itself a newtype — codegen has already unwrapped it — so the first written layer opens the
     * element directly and MUST name the element type; the rest is the same layer check as a user case. */
    static void checkOptionUnwrapAsserts(Ast.Case c, Type element, Symbols symbols) {
        List<Ast.Name> layers = c.unwrapAsserts();
        if (layers.isEmpty()) {
            return;   // `Some(v)` binds the whole element, opening nothing
        }
        Ast.Name first = layers.get(0);
        // the layer is compared as a type: `Some(billing.金額(v))` opens the same newtype an
        // imported bare `金額` names
        if (!(element instanceof Type.Ref r) || !r.name().equals(first.denotes())) {
            String elementName = element instanceof Type.Ref r2 ? r2.name().name() : Type.show(element);
            throw CompileException.of(
                    Diagnostic.of(null, "check.match.newtype.mismatch").title("check.match.title")
                            .at(c.pos()).args("Some", elementName, first.written()).build(),
                    "`Some` wraps `" + elementName + "`, not `" + first.written() + "`");
        }
        checkOpenedLayers(c, layers, symbols, false);
    }

    /** {@code firstOpensTheCase} says the first opened name is the arm's own case, which is where
     * {@code | X as v} is the spelling to reach for when X turns out not to be a newtype. An inner
     * layer (and Option's element) is reached through the case, so no such binding replaces it. */
    static void checkOpenedLayers(Ast.Case c, List<Ast.Name> opened, Symbols symbols,
                                  boolean firstOpensTheCase) {
        for (int i = 0; i < opened.size(); i++) {
            String name = opened.get(i).written();
            TypeName layer = opened.get(i).denotes();
            Type inner = TypeOps.newtypeInner(layer, symbols);
            if (inner == null) {
                Diagnostic.Builder d =
                        Diagnostic.of(null, "check.match.newtype.notnewtype").title("check.match.title")
                                .at(c.pos()).args(name);
                if (i == 0 && firstOpensTheCase) {
                    d = d.hint("check.match.newtype.notnewtype.hint");
                }
                throw CompileException.of(d.build(),
                        "`" + name + "` is not a newtype, so it cannot be opened with `" + name + "(...)`");
            }
            if (i + 1 < opened.size()) {
                Ast.Name next = opened.get(i + 1);
                // the layer a pattern claims is compared as a type, so an inner newtype named
                // through its module opens the same one an imported bare name does
                if (!(inner instanceof Type.Ref ir) || !ir.name().equals(next.denotes())) {
                    String innerName = inner instanceof Type.Ref r ? r.name().name() : Type.show(inner);
                    throw CompileException.of(
                            Diagnostic.of(null, "check.match.newtype.mismatch").title("check.match.title")
                                    .at(c.pos()).args(name, innerName, next.written()).build(),
                            "`" + name + "` wraps `" + innerName + "`, not `" + next.written() + "`");
                }
            }
        }
    }

    /** Extends {@code env} with {@code name -> type} when both are present; otherwise returns it as is. */
    static Map<String, Type> bound(Map<String, Type> env, String name, Type type) {
        if (name == null || type == null) {
            return env;
        }
        Map<String, Type> benv = new HashMap<>(env);
        benv.put(name, type);
        return benv;
    }

    static Type mergeBranch(Ast.Match m, Type branchType, Type bt, Ast.Case c) {
        if (branchType == null) {
            return bt;
        }
        // arms merge by the join `if` branches use — equal types collapse, data-like ones widen to
        // their union, and both hold under a collection or a tuple as well (spec 16.2)
        Type joined = TypeOps.join(branchType, bt);
        if (joined != null) {
            return joined;
        }
        throw CompileException.of(
                Diagnostic.of(null, "check.match.branchtypes").title("check.match.title")
                        .at(c.pos()).args(Type.show(branchType), Type.show(bt))
                        .diff(Type.show(bt, branchType), Type.show(branchType, bt)).build(),
                "match branches disagree: " + branchType + " vs " + bt);
    }

    /** A non-exhaustive-match error (E1201) listing every missing case. The legacy message names the
     * first missing case, as it did before, so callers reading the text are unchanged. */
    static CompileException nonExhaustive(SourcePos pos, String what, List<String> missing) {
        return CompileException.of(
                Diagnostic.of("E1201", "e1201.msg")
                        .at(pos, 5)
                        .args(what)
                        .hint("e1201.hint", String.join(", ", missing))
                        .build(),
                "Non-exhaustive match for " + what + ". Missing case: " + missing.get(0));
    }
}
