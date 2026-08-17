package souther.compiler.check;

import souther.compiler.ast.Hir;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.DiagnosticRenderer;
import souther.compiler.diag.msg.BehaviorMessage;
import souther.compiler.types.BindingId;
import souther.compiler.types.BindingOwner;
import souther.compiler.types.CaseSelector;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/** Checks and types the postconditions carried by one behavior declaration. */
final class BehaviorChecker {

    private BehaviorChecker() {}

    /**
     * Checks every rule of every clause and reports what each one was wrong about.
     *
     * <p>Rule by rule rather than clause by clause and not stopping at the first. A behavior
     * carrying two clauses that are each wrong is an author with two things to fix, and stopping at
     * the first turns one build into two. What does stop is a signature this cannot be read against
     * at all — a parameter spelled `value` leaves every rule ambiguous about what it names, so
     * reporting the rules underneath it would be reporting a mistake twice.
     */
    static void check(Hir.SpecBehavior behavior, String module, Sig sig, Symbols symbols,
                      Map<String, Type> helpers) {
        if (behavior.ensures().isEmpty()) {
            return;
        }
        for (Hir.Param param : behavior.params()) {
            if (param.name().equals("value")) {
                throw CompileException.of(Diagnostic.at(param.pos())
                        .say(new BehaviorMessage.ABehaviorWithAClauseHasAParameterNamedValue(
                                behavior.name())).build());
            }
        }
        List<Diagnostic> found = new ArrayList<>();

        ValueName.Behavior name = new ValueName.Behavior(module, behavior.name());
        BindingOwner owner = new BindingOwner.OfSignature(name);
        Map<BindingId, Scope.Binding> parameters = new LinkedHashMap<>();
        List<Type> inputTypes = sig.inputTypes();
        for (int i = 0; i < behavior.params().size(); i++) {
            parameters.put(new BindingId(owner, i),
                    new Scope.Binding(behavior.params().get(i).name(), inputTypes.get(i)));
        }

        // Which cases the answer can be, and what `value` is in each, come from the same place a
        // `match` over that answer reads them. A clause naming a case a caller could not match is a
        // clause a caller could never assume, so the two admit the same names by construction.
        CaseSpace answer = CaseSpace.of(sig.outputType(), symbols);
        boolean hasCases = !(answer instanceof CaseSpace.Plain);

        int armOrdinal = 0;
        for (Hir.EnsuresClause clause : behavior.ensures()) {
            for (Hir.EnsuresArm arm : clause.arms()) {
                int ordinal = armOrdinal++;
                collect(found, () -> checkArm(behavior, arm, answer, hasCases, sig, parameters,
                        owner, ordinal, helpers, symbols));
            }
        }
        if (found.size() == 1) {
            throw CompileException.of(found.get(0));
        }
        if (!found.isEmpty()) {
            throw CompileException.ofAll(found, DiagnosticRenderer.legacyBody(found.get(0)));
        }
    }

    /** One rule: what it may name, what its arms may be, and what its expression comes to. */
    private static void checkArm(Hir.SpecBehavior behavior, Hir.EnsuresArm arm, CaseSpace answer,
                                 boolean hasCases, Sig sig,
                                 Map<BindingId, Scope.Binding> parameters, BindingOwner owner,
                                 int armOrdinal, Map<String, Type> helpers, Symbols symbols) {
        if (hasCases && arm.cases().isEmpty()) {
            throw CompileException.of(Diagnostic.at(arm.pos())
                    .say(new BehaviorMessage.AnEnsuresClauseOverASumNamesNoArm(
                            behavior.name())).build());
        }
        if (!hasCases && !arm.cases().isEmpty()) {
            throw CompileException.of(Diagnostic.at(arm.pos())
                    .say(new BehaviorMessage.AnEnsuresClauseOverASingleTypeNamesAnArm(
                            behavior.name())).build());
        }

        if (arm.cases().isEmpty()) {
            typeArm(behavior, arm, parameters, owner, armOrdinal, sig.outputType(), helpers, symbols);
        } else {
            List<CaseSelector> selected = new ArrayList<>();
            for (Hir.Name armCase : arm.cases()) {
                if (armCase.answered() == null) {
                    // Nothing declares it, which is reported where it is written. That this is not
                    // an output case follows from it, and saying so would be the one mistake said
                    // twice — the reading is abandoned instead, as a `match` arm's is.
                    throw new Unanswerable(armCase.pos());
                }
                CaseSelector selector = answer.selector(armCase.answered().type());
                if (selector == null) {
                    throw CompileException.of(Diagnostic.at(armCase.pos())
                            .say(new BehaviorMessage.AnEnsuresArmIsNotAnOutputCase(
                                    armCase.written(), behavior.name())).build());
                }
                selected.add(selector);
            }
            // The expression is elaborated once for every named case, `value` being read as what
            // that case holds and the cases holding different things.
            for (CaseSelector selector : selected) {
                typeArm(behavior, arm, parameters, owner, armOrdinal, selector.bound(),
                        helpers, symbols);
            }
        }
        requireBothSides(behavior, arm, owner, armOrdinal, !arm.cases().isEmpty());
    }

    /** Runs {@code rule} and keeps what it reported, so the rules after it are read too. */
    private static void collect(List<Diagnostic> found, Runnable rule) {
        try {
            rule.run();
        } catch (CompileException e) {
            found.addAll(e.diagnostics());
        }
    }

    private static void typeArm(Hir.SpecBehavior behavior, Hir.EnsuresArm arm,
                                Map<BindingId, Scope.Binding> parameters, BindingOwner owner,
                                int armOrdinal, Type answerType, Map<String, Type> helpers,
                                Symbols symbols) {
        Map<BindingId, Scope.Binding> bindings = new LinkedHashMap<>(parameters);
        bindings.put(new BindingId(owner, behavior.params().size() + armOrdinal),
                new Scope.Binding("value", answerType));
        Type actual = Elaborator.typeOf(arm.expr(), Scope.of(bindings).reaching(helpers),
                CheckContext.of(symbols));
        if (actual != Type.BOOL) {
            throw CompileException.of(Diagnostic.at(arm.expr().pos())
                    .say(new BehaviorMessage.AnEnsuresExpressionIsNotBool(
                            behavior.name(), Type.show(actual))).build());
        }
    }

    /**
     * A rule states a relation, so it refers to both sides of one.
     *
     * <p>It refers to the answer through its arm or through {@code value}. An arm is a reference:
     * {@code Missing -> id == tag} says that where the answer is `Missing`, the inputs stood in that
     * relation, which is a statement about the answer whether or not the predicate reads it. Asking
     * for the word {@code value} instead would be reading the text for the relation rather than the
     * rule, and would refuse a rule that states one.
     *
     * <p>What it refers to and what it depends on are not the same as what it is <em>about</em>.
     * {@code value == value && id > 0} refers to the answer and says nothing about it, and an
     * answer with one case makes any arm of it vacuous. Telling those apart is a proof, and the rule
     * this holds is the one it can hold: a relation is written with both sides in it.
     */
    private static void requireBothSides(Hir.SpecBehavior behavior, Hir.EnsuresArm arm,
                                         BindingOwner owner, int armOrdinal, boolean namesAnArm) {
        Set<Integer> read = new LinkedHashSet<>();
        collectBindings(arm.expr(), owner, read);
        if (!namesAnArm && !read.contains(behavior.params().size() + armOrdinal)) {
            throw CompileException.of(Diagnostic.at(arm.pos())
                    .say(new BehaviorMessage.AnEnsuresClauseDoesNotNameTheAnswer(
                            behavior.name())).build());
        }
        boolean readsParameter = read.stream().anyMatch(i -> i < behavior.params().size());
        if (!readsParameter) {
            throw CompileException.of(Diagnostic.at(arm.pos())
                    .say(new BehaviorMessage.AnEnsuresClauseDoesNotNameAParameter(
                            behavior.name())).build());
        }
    }

    private static void collectBindings(Hir.Expr expr, BindingOwner owner, Set<Integer> out) {
        if (expr instanceof Hir.Var.Denoting var
                && var.denotes() instanceof ValueName.Local local
                && local.id().owner().equals(owner)) {
            out.add(local.id().ordinal());
        }
        TypeChecker.forEachChild(expr, child -> collectBindings(child, owner, out));
    }
}
