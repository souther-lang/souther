package souther.compiler.check;

import souther.compiler.ast.Hir;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.msg.BehaviorMessage;
import souther.compiler.types.BindingId;
import souther.compiler.types.BindingOwner;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.ValueName;

import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/** Checks and types the postconditions carried by one behavior declaration. */
final class BehaviorChecker {

    private BehaviorChecker() {}

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

        ValueName.Behavior name = new ValueName.Behavior(module, behavior.name());
        BindingOwner owner = new BindingOwner.OfSignature(name);
        Map<BindingId, Scope.Binding> parameters = new LinkedHashMap<>();
        List<Type> inputTypes = sig.inputTypes();
        for (int i = 0; i < behavior.params().size(); i++) {
            parameters.put(new BindingId(owner, i),
                    new Scope.Binding(behavior.params().get(i).name(), inputTypes.get(i)));
        }

        boolean sum = sig.outputType() instanceof Type.Union;
        Set<TypeSymbol> outputCases = new LinkedHashSet<>();
        for (Hir.TypeTerm term : behavior.ret().cases()) {
            if (term instanceof Hir.TypeRef ref && ref.denotes() instanceof Type.Ref named) {
                outputCases.add(named.name());
            }
        }

        int armOrdinal = 0;
        for (Hir.EnsuresClause clause : behavior.ensures()) {
            for (Hir.EnsuresArm arm : clause.arms()) {
                if (sum && arm.cases().isEmpty()) {
                    throw CompileException.of(Diagnostic.at(arm.pos())
                            .say(new BehaviorMessage.AnEnsuresClauseOverASumNamesNoArm(
                                    behavior.name())).build());
                }
                if (!sum && !arm.cases().isEmpty()) {
                    throw CompileException.of(Diagnostic.at(arm.pos())
                            .say(new BehaviorMessage.AnEnsuresClauseOverASingleTypeNamesAnArm(
                                    behavior.name())).build());
                }

                Type answerType = sig.outputType();
                if (!arm.cases().isEmpty()) {
                    for (Hir.Name armCase : arm.cases()) {
                        TypeSymbol denoted = armCase.answered() == null
                                ? null : armCase.answered().type();
                        if (denoted == null || !outputCases.contains(denoted)) {
                            throw CompileException.of(Diagnostic.at(armCase.pos())
                                    .say(new BehaviorMessage.AnEnsuresArmIsNotAnOutputCase(
                                            armCase.written(), behavior.name())).build());
                        }
                    }
                    // The expression is elaborated once for every named case because `value` has a
                    // different nominal type in each reading.
                    for (Hir.Name armCase : arm.cases()) {
                        typeArm(behavior, arm, parameters, owner, armOrdinal,
                                Type.ref(armCase.answered().type()), helpers, symbols);
                    }
                } else {
                    typeArm(behavior, arm, parameters, owner, armOrdinal,
                            answerType, helpers, symbols);
                }
                requireBothSides(behavior, arm, owner, armOrdinal);
                armOrdinal++;
            }
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

    private static void requireBothSides(Hir.SpecBehavior behavior, Hir.EnsuresArm arm,
                                         BindingOwner owner, int armOrdinal) {
        Set<Integer> read = new LinkedHashSet<>();
        collectBindings(arm.expr(), owner, read);
        if (!read.contains(behavior.params().size() + armOrdinal)) {
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
