package souther.compiler.check;

import souther.compiler.ast.Ast;
import souther.compiler.core.Core;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.SourcePos;

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
        return elaborateCasesMatch(m, scrutinee, new HashSet<>(sum.cases()), "data `" + sum.name() + "`",
                st, env, ctx, expected);
    }

    /**
     * An arm names something that is not a case of what is being matched. When that name is a case of
     * another sum, say which — the author wrote an arm for a different match. The layout rule
     * (<<match>>) settles that by column, except where both matches are on one line: there the inner
     * match takes every `|` after it, so an arm meant for the outer one lands here, and the report
     * says how to end the inner match.
     */
    static CompileException notCase(String caseName, String what, Ast.Case c, Ast.Match m,
                                            Set<String> cases, Map<String, Ast.Def> symbols) {
        String otherSum = null;
        for (Ast.Def def : symbols.values()) {
            if (def instanceof Ast.SumData sum && sum.cases().contains(caseName)
                    && !cases.containsAll(sum.cases())) {
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
    static Core elaborateCasesMatch(Ast.Match m, Core scrutineeCore, Set<String> cases,
                                        String what, Type scrutinee,
                                        Map<String, Type> env, CheckContext ctx, Type expected) {
        Set<String> covered = new HashSet<>();
        List<Core.Case> arms = new ArrayList<>();
        Type branchType = null;
        for (Ast.Case c : m.cases()) {
            for (String caseName : c.caseTypes()) {
                if (!cases.contains(caseName)) {
                    throw notCase(caseName, what, c, m, cases, ctx.symbols());
                }
                if (!covered.add(caseName)) {
                    throw CompileException.of(
                            Diagnostic.of(null, "check.match.overlap").title("check.match.title")
                                    .at(c.pos()).args(caseName).build(),
                            "`" + caseName + "` is matched by more than one case");
                }
            }
            Type bindType = c.caseTypes().size() == 1 ? caseBindType(c.caseTypes().get(0)) : scrutinee;
            if (c.unwrapAsserts() != null) {
                if (c.caseTypes().size() != 1) {
                    throw CompileException.of(
                            Diagnostic.of(null, "check.match.newtype.orpattern").title("check.match.title")
                                    .at(c.pos()).build(),
                            "a constructor destructuring opens a single case, not an or-pattern");
                }
                checkUnwrapAsserts(c, ctx.symbols());
            }
            Core body = Elaborator.elaborate(c.body(), bound(env, c.binding(), bindType), ctx, expected);
            arms.add(new Core.Case(c.caseTypes(), c.binding(), body, bindType, c.pos()));
            branchType = mergeBranch(m, branchType, body.type(), c);
        }
        List<String> missing = new ArrayList<>();
        for (String caseName : cases) {
            if (!covered.contains(caseName)) {
                missing.add(caseName);
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
        Set<String> covered = new HashSet<>();
        List<Core.Case> arms = new ArrayList<>();
        Type branchType = null;
        for (Ast.Case c : m.cases()) {
            if (c.caseTypes().size() != 1) {
                throw CompileException.of(
                        Diagnostic.of(null, "check.match.option.orpattern").title("check.match.title")
                                .at(c.pos()).build(),
                        "or-patterns are not allowed in an Option match; use separate Some and None cases");
            }
            String caseType = c.caseTypes().get(0);
            Type bind = switch (caseType) {
                case "Some" -> element;
                case "None" -> null;
                default -> throw CompileException.of(
                        Diagnostic.of(null, "check.match.option.notcase").title("check.match.title")
                                .at(c.pos()).args(caseType).build(),
                        "`" + caseType + "` is not a case of Option; use Some or None");
            };
            if (c.unwrapAsserts() != null) {
                if (!caseType.equals("Some")) {
                    throw CompileException.of(
                            Diagnostic.of(null, "check.match.option.nopayload").title("check.match.title")
                                    .at(c.pos()).args(caseType).build(),
                            "`" + caseType + "` has no value, so it cannot be opened with `" + caseType + "(...)`");
                }
                checkOptionUnwrapAsserts(c, element, ctx.symbols());
            }
            if (!covered.add(caseType)) {
                throw CompileException.of(
                        Diagnostic.of(null, "check.match.overlap").title("check.match.title")
                                .at(c.pos()).args(caseType).build(),
                        "`" + caseType + "` is matched by more than one case");
            }
            Core body = Elaborator.elaborate(c.body(), bound(env, c.binding(), bind), ctx, expected);
            arms.add(new Core.Case(c.caseTypes(), c.binding(), body, bind, c.pos()));
            branchType = mergeBranch(m, branchType, body.type(), c);
        }
        List<String> missing = new ArrayList<>();
        for (String caseName : List.of("Some", "None")) {
            if (!covered.contains(caseName)) {
                missing.add(caseName);
            }
        }
        if (!missing.isEmpty()) {
            throw nonExhaustive(m.pos(), "Option", missing);
        }
        return new Core.Match(scrutineeCore, arms, branchType, m.pos());
    }

    /** The type a match case binds. A primitive-named case (e.g. {@code Int} in {@code Int |
     * DivisionByZero}) binds that primitive; a data-named case binds its data type. */
    public static Type caseBindType(String caseName) {
        return switch (caseName) {
            case "Int" -> Type.INT;
            case "String" -> Type.STRING;
            case "Bool" -> Type.BOOL;
            case "Decimal" -> Type.DECIMAL;
            case "Date" -> Type.DATE;
            case "DateTime" -> Type.DATETIME;
            default -> Type.ref(caseName);
        };
    }

    /** A constructor-destructuring pattern {@code X(Y(s))} opens one newtype per layer: {@code X}
     * (the matched case) then each written inner name. Every opened layer MUST be a newtype, and each
     * inner name MUST equal the newtype the previous layer wraps, or it is a compile error (Elm/F#
     * parity — the constructor in the pattern is type-checked, and a non-newtype cannot be opened). */
    static void checkUnwrapAsserts(Ast.Case c, Map<String, Ast.Def> symbols) {
        List<String> opened = new ArrayList<>();
        opened.add(c.caseTypes().get(0));
        opened.addAll(c.unwrapAsserts());
        checkOpenedLayers(c, opened, symbols);
    }

    /** {@code Some(X(v))} opens the Option's element in the pattern. Unlike a user case, {@code Some}
     * is not itself a newtype — codegen has already unwrapped it — so the first written layer opens the
     * element directly and MUST name the element type; the rest is the same layer check as a user case. */
    static void checkOptionUnwrapAsserts(Ast.Case c, Type element, Map<String, Ast.Def> symbols) {
        List<String> layers = c.unwrapAsserts();
        if (layers.isEmpty()) {
            return;   // `Some(v)` binds the whole element, opening nothing
        }
        String elementName = element instanceof Type.Ref r ? r.name() : Type.show(element);
        String first = layers.get(0);
        if (!elementName.equals(first)) {
            throw CompileException.of(
                    Diagnostic.of(null, "check.match.newtype.mismatch").title("check.match.title")
                            .at(c.pos()).args(first, elementName).build(),
                    "`Some` wraps `" + elementName + "`, not `" + first + "`");
        }
        checkOpenedLayers(c, layers, symbols);
    }

    static void checkOpenedLayers(Ast.Case c, List<String> opened, Map<String, Ast.Def> symbols) {
        for (int i = 0; i < opened.size(); i++) {
            String name = opened.get(i);
            Type inner = TypeOps.newtypeInner(name, symbols);
            if (inner == null) {
                throw CompileException.of(
                        Diagnostic.of(null, "check.match.newtype.notnewtype").title("check.match.title")
                                .at(c.pos()).args(name).build(),
                        "`" + name + "` is not a newtype, so it cannot be opened with `" + name + "(...)`");
            }
            if (i + 1 < opened.size()) {
                String next = opened.get(i + 1);
                String innerName = inner instanceof Type.Ref r ? r.name() : Type.show(inner);
                if (!innerName.equals(next)) {
                    throw CompileException.of(
                            Diagnostic.of(null, "check.match.newtype.mismatch").title("check.match.title")
                                    .at(c.pos()).args(next, innerName).build(),
                            "`" + name + "` wraps `" + innerName + "`, not `" + next + "`");
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
        if (branchType.equals(bt)) {
            return branchType;
        }
        Type empty = BottomInfer.absorbBottom(branchType, bt);   // one case may be an empty collection (ADR-0028)
        if (empty != null) {
            return empty;
        }
        // cases yielding different data types widen to their union, as `if` branches do (spec 16.2)
        if (TypeOps.isDataLike(branchType) && TypeOps.isDataLike(bt)) {
            Set<String> names = new HashSet<>(TypeOps.namesOf(branchType));
            names.addAll(TypeOps.namesOf(bt));
            return Type.union(names);
        }
        throw CompileException.of(
                Diagnostic.of(null, "check.match.branchtypes").title("check.match.title")
                        .at(c.pos()).args(Type.show(branchType), Type.show(bt))
                        .diff(Type.show(bt), Type.show(branchType)).build(),
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
