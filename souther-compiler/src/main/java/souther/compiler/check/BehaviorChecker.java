package souther.compiler.check;

import souther.compiler.ast.Hir;
import souther.compiler.check.BehaviorContract.Clause;
import souther.compiler.check.BehaviorContract.ContractParam;
import souther.compiler.check.BehaviorContract.Guard;
import souther.compiler.check.BehaviorContract.Rule;
import souther.compiler.check.BehaviorContract.RuleId;
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

/**
 * Reads what a behavior declares about its answer into a {@link BehaviorContract}, and holds it to
 * the rules a declaration is subject to.
 *
 * <p>The reading and the checking are one pass because they are one question. What a rule states is
 * what case it applies to and what has to be so there, and every rule this refuses is a rule it
 * could not read that from.
 */
final class BehaviorChecker {

    private BehaviorChecker() {}

    /**
     * The contract {@code behavior} declares, or the empty one where it declares none.
     *
     * <p>Rule by rule and not stopping at the first. A behavior carrying two clauses that are each
     * wrong is an author with two things to fix, and stopping at the first turns one build into two.
     * What does stop is a signature this cannot be read against at all — a parameter spelled
     * {@code value} leaves every rule ambiguous about what it names, so reading the rules underneath
     * it would report one mistake as several.
     */
    static BehaviorContract contractOf(Hir.SpecBehavior behavior, String module, Sig sig,
                                       Symbols symbols, Map<String, Type> helpers) {
        ValueName.Behavior name = new ValueName.Behavior(module, behavior.name());
        if (sig == null) {
            // The signature could not be made, which is reported where that failed. A rule is
            // read against the parameters and the answer, so there is nothing to read one against
            // — said again here it would be that one mistake seen from another angle.
            throw new Unanswerable(behavior.pos());
        }
        for (Hir.Param param : behavior.params()) {
            if (param.name().equals("value")) {
                throw CompileException.of(Diagnostic.at(param.pos())
                        .say(new BehaviorMessage.ABehaviorWithAClauseHasAParameterNamedValue(
                                behavior.name())).build());
            }
        }

        BindingOwner owner = BehaviorContract.ownerOf(name);
        List<ContractParam> params = new ArrayList<>();
        for (int i = 0; i < behavior.params().size(); i++) {
            params.add(new ContractParam(new BindingId(owner, i), sig.inputTypes().get(i), i));
        }

        // Which cases the answer can be, and what `value` is in each, come from the same place a
        // `match` over that answer reads them. A clause naming a case a caller could not match is a
        // clause a caller could never assume, so the two admit the same names by construction.
        CaseSpace answer = CaseSpace.of(sig.outputType(), symbols);

        // Arm by arm, and an arm this cannot read leaves the rest readable. Reading and checking are
        // one pass — what a rule states is which case it applies to and what holds there, and every
        // refusal here is this not having been able to read that — so an arm that fails contributes
        // no rule and stops nothing else.
        List<Diagnostic> found = new ArrayList<>();
        List<Clause> clauses = new ArrayList<>();
        int armOrdinal = 0;
        for (int c = 0; c < behavior.ensures().size(); c++) {
            Hir.EnsuresClause written = behavior.ensures().get(c);
            List<Rule> rules = new ArrayList<>();
            for (Hir.EnsuresArm arm : written.arms()) {
                int ordinal = armOrdinal++;
                int clauseIndex = c;
                collect(found, () -> rules.addAll(
                        read(behavior, arm, answer, owner, params.size(), clauseIndex, ordinal)));
            }
            clauses.add(new Clause(written.name(), rules, written.pos(), written.region()));
        }
        BehaviorContract contract =
                new BehaviorContract(name, params, sig.outputType(), clauses);
        for (Rule rule : contract.rules()) {
            collect(found, () -> checkRule(behavior, contract, rule, helpers, symbols));
        }
        if (found.size() == 1) {
            throw CompileException.of(found.get(0));
        }
        if (!found.isEmpty()) {
            throw CompileException.ofAll(found, DiagnosticRenderer.legacyBody(found.get(0)));
        }
        return contract;
    }

    /**
     * The clauses as rules: one rule per case an arm names, or one rule over every answer where the
     * arm names none.
     *
     * <p>Specializing here rather than at each reader is what keeps {@code value}'s type from being
     * worked out again — a rule already knows which case it is about, and the cases hold different
     * things. What an arm may name is settled here too, since a rule cannot be read for a case the
     * answer does not have.
     */
    private static List<Rule> read(Hir.SpecBehavior behavior, Hir.EnsuresArm arm, CaseSpace answer,
                                   BindingOwner owner, int paramCount, int clause, int ordinal) {
        boolean hasCases = !(answer instanceof CaseSpace.Plain);
        ValueName.Behavior named = ((BindingOwner.OfSignature) owner).behavior();
        BindingId value = new BindingId(owner, paramCount + ordinal);

        // What form the arm may take is asked before what it names, so an arm written where none
        // may be is that mistake and not the one that follows from it.
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
            return List.of(new Rule(new Guard.Always(), value, arm.expr(),
                    new RuleId(named, clause, ordinal, null), arm.pos()));
        }

        List<Rule> rules = new ArrayList<>();
        Set<TypeSymbol> seen = new LinkedHashSet<>();
        for (Hir.Name armCase : arm.cases()) {
            if (armCase.answered() == null) {
                // Nothing declares it, which is reported where it is written. That this is not an
                // output case follows from it, and saying so would be the one mistake said twice —
                // the reading is abandoned instead, as a `match` arm's is.
                throw new Unanswerable(armCase.pos());
            }
            CaseSelector selector = answer.selector(armCase.answered().type());
            if (selector == null) {
                throw CompileException.of(Diagnostic.at(armCase.pos())
                        .say(new BehaviorMessage.AnEnsuresArmIsNotAnOutputCase(
                                armCase.written(), behavior.name())).build());
            }
            // A case named twice under one arrow is one rule, not two. What a clause states is a
            // conjunction — every rule whose guard holds applies — so `Found | Found -> p` states
            // `p` and `p`, which is `p`. Kept as two, they would be two rules under one
            // {@link RuleId}, and the readers that agree on a rule by its identity would each hold
            // a different number of them.
            //
            // Redundant and not ambiguous, so it is collapsed rather than refused. `Found -> p |
            // Found -> q` is another matter and is two rules: the arms differ, so the ids do.
            if (!seen.add(selector.name())) {
                continue;
            }
            rules.add(new Rule(new Guard.Case(selector), value, arm.expr(),
                    new RuleId(named, clause, ordinal, selector.name()), arm.pos()));
        }
        return rules;
    }

    /** One rule: what its expression comes to, and that it states a relation. */
    private static void checkRule(Hir.SpecBehavior behavior, BehaviorContract contract, Rule rule,
                                  Map<String, Type> helpers, Symbols symbols) {
        Map<BindingId, Scope.Binding> bindings = new LinkedHashMap<>();
        for (ContractParam param : contract.params()) {
            bindings.put(param.binding(),
                    new Scope.Binding(behavior.params().get(param.index()).name(), param.type()));
        }
        bindings.put(rule.value(),
                new Scope.Binding("value", rule.valueType(contract.output())));
        Type actual = Elaborator.typeOf(rule.statement(), Scope.of(bindings).reaching(helpers),
                CheckContext.of(symbols));
        if (actual != Type.BOOL) {
            throw CompileException.of(Diagnostic.at(rule.statement().pos())
                    .say(new BehaviorMessage.AnEnsuresExpressionIsNotBool(
                            behavior.name(), Type.show(actual))).build());
        }
        requireBothSides(behavior, contract, rule);
    }

    /**
     * A rule states a relation, so it refers to both sides of one.
     *
     * <p>It refers to the answer through its guard or through {@code value}. A guard is a reference:
     * {@code Missing -> id == tag} says that where the answer is `Missing`, the inputs stood in that
     * relation, which is a statement about the answer whether or not the expression reads it.
     * Asking for the word {@code value} instead would read the text for the relation rather than
     * the rule, and would refuse a rule that states one.
     *
     * <p>What a rule refers to is not what it is <em>about</em>. {@code value == value && id > 0}
     * refers to the answer and says nothing about it, and a guard over an answer with one case holds
     * of everything it answers. Telling those apart is a proof; what this holds is that a relation
     * is written with both of its sides in it.
     */
    private static void requireBothSides(Hir.SpecBehavior behavior, BehaviorContract contract,
                                         Rule rule) {
        Set<BindingId> read = new LinkedHashSet<>();
        collectBindings(rule.statement(), contract.behavior(), read);
        if (rule.guard() instanceof Guard.Always && !read.contains(rule.value())) {
            throw CompileException.of(Diagnostic.at(rule.pos())
                    .say(new BehaviorMessage.AnEnsuresClauseDoesNotNameTheAnswer(
                            behavior.name())).build());
        }
        boolean readsParameter = contract.params().stream()
                .anyMatch(param -> read.contains(param.binding()));
        if (!readsParameter) {
            throw CompileException.of(Diagnostic.at(rule.pos())
                    .say(new BehaviorMessage.AnEnsuresClauseDoesNotNameAParameter(
                            behavior.name())).build());
        }
    }

    /** Runs {@code rule} and keeps what it reported, so the rules after it are read too. */
    private static void collect(List<Diagnostic> found, Runnable rule) {
        try {
            rule.run();
        } catch (CompileException e) {
            found.addAll(e.diagnostics());
        }
    }

    /** Which of the behavior's own names an expression reads. */
    private static void collectBindings(Hir.Expr expr, ValueName.Behavior behavior,
                                        Set<BindingId> out) {
        if (expr instanceof Hir.Var.Denoting var
                && var.denotes() instanceof ValueName.Local local
                && local.id().owner() instanceof BindingOwner.OfSignature signature
                && signature.behavior().equals(behavior)) {
            out.add(local.id());
        }
        TypeChecker.forEachChild(expr, child -> collectBindings(child, behavior, out));
    }
}
