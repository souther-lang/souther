package souther.compiler.check;

import souther.compiler.ast.Hir;
import souther.compiler.check.BehaviorContract.Clause;
import souther.compiler.check.BehaviorContract.ContractParam;
import souther.compiler.check.BehaviorContract.Guard;
import souther.compiler.check.BehaviorContract.Rule;
import souther.compiler.core.Core;
import souther.compiler.types.BindingId;
import souther.compiler.types.BindingOwner;
import souther.compiler.types.CaseSelector;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * How much of what a behavior declares the check can read, rule by rule, and which of the answer's
 * cases nothing is said about.
 *
 * <p>The same classification a data's clause gets ({@link ClauseDischarge}), asked of the other kind
 * of clause. It is the same question: whether what is written is a relation the numeric domain
 * reasons over, a term the check can name and compare, or something it cannot represent at all. What
 * follows from the answer differs — an invariant's classification says what discharges a
 * construction, a rule's says how much of the relation is there to be read at a call — but what is
 * being asked of the expression is one thing, and asking it twice would be two answers to keep
 * agreeing.
 *
 * <p>The unit is the rule, and under it the conjunct. A rule is already specialized to one case, so
 * {@code ensures Todo | NotFound -> value.id == id} is classified once for {@code Todo} and once for
 * {@code NotFound} and the two may differ — what {@code value} is differs between them, and what the
 * check can make of a statement about it follows. A flat list per behavior would put the two under
 * one entry and leave a reader to work out which case it was looking at.
 */
public record ContractDischarge(List<RuleDischarge> rules,
                                List<TypeSymbol> casesNothingIsSaidAbout) {

    public ContractDischarge {
        rules = List.copyOf(rules);
        casesNothingIsSaidAbout = List.copyOf(casesNothingIsSaidAbout);
    }

    /** One conjunct of one rule, and what the check can make of it. */
    public record RuleDischarge(BehaviorContract.RuleId rule, ClauseDischarge capability) {}

    /**
     * What the check can read of {@code contract}, whose rules are as their author wrote them. Each
     * is expanded into the representation the check reads ({@link InliningPolicy#DISCHARGE}) as it is
     * classified, so what comes back is placed and split where it is written.
     *
     * <p>Handed a contract rather than a declaration. What a rule is about, what {@code value} is
     * there and which rule it is are the reading's answers ({@link BehaviorChecker}), and this asks
     * one question of them. The contract handed here is the same declaration that reading reads for
     * the tree that runs, so its {@link BehaviorContract.RuleId}s are the ids of the rules that run —
     * a reader holding both is not left matching them up.
     *
     * @param expansion what turns a piece of what was written into the tree the check reads. Applied
     *                  here, one conjunct at a time, rather than to the declaration before it was
     *                  read: an expansion carries the positions of the body it copies in, so a rule
     *                  expanded first would be placed inside the helper it names and split where that
     *                  helper's author split it
     * @param helpers the signatures a rule may reach without a binding, as the check that holds a
     *                rule to its declaration reads them
     */
    public static ContractDischarge of(BehaviorContract contract, HelperInliner expansion,
                                       Symbols symbols, Map<String, Type> helpers) {
        List<RuleDischarge> classified = new ArrayList<>();
        for (Clause clause : contract.clauses()) {
            for (Rule rule : clause.rules()) {
                classified.addAll(of(contract, clause, rule, expansion, symbols, helpers));
            }
        }
        return new ContractDischarge(classified, unstatedCases(contract, symbols));
    }

    /**
     * One rule, conjunct by conjunct.
     *
     * <p>Each conjunct on its own, as a data's are: what discharges one half of {@code a && b} is not
     * what discharges the other, and an author acts on the half. The name the clause was declared
     * with goes on each of them, because a violation is reported by the clause however many conjuncts
     * it was written as.
     *
     * <p>Split where the author wrote the {@code &&} and not where an expansion put one. A rule
     * naming a helper whose body is a conjunction is one thing the author wrote, so it is one answer;
     * splitting the expanded tree would hand back two answers to a rule nobody wrote as two, each
     * placed inside the helper.
     */
    private static List<RuleDischarge> of(BehaviorContract contract, Clause clause, Rule rule,
                                          HelperInliner expansion, Symbols symbols,
                                          Map<String, Type> helpers) {
        Scope scope = BehaviorChecker.scopeOf(contract, rule).reaching(helpers);
        CheckContext ctx = CheckContext.of(symbols).forDischarge();
        // The parameters and `value` stand for themselves. A caller hands one value per parameter and
        // the behavior answers one value, so a rule naming either names something wherever it is read
        // — entered as locations, and nothing is seeded of them, since what the rule states is the
        // question.
        Set<BindingId> named = new LinkedHashSet<>();
        for (ContractParam param : contract.params()) {
            named.add(param.binding());
        }
        named.add(rule.value());
        Denotations locations = Denotations.none().locations(named);

        BindingOwner owner = BehaviorContract.ownerOf(contract.behavior());
        List<RuleDischarge> out = new ArrayList<>();
        for (Hir.Expr written : ClauseHelpers.conjunctsOf(rule.statement())) {
            out.add(new RuleDischarge(rule.id(),
                    InvariantChecker.capabilityOf(
                            typed(expansion.inline(written, owner), scope, ctx),
                            ClauseHelpers.beginsAt(written), locations, symbols,
                            contract.behavior().name()).named(clause.name())));
        }
        return out;
    }

    /**
     * {@code conjunct} as the check reads it, or null where this compiler could not type it there.
     *
     * <p>Null is an answer and not a failure, as it is for a data's clause: a rule the check cannot
     * read is not a rule an author wrote wrongly, and whether it is well formed was settled where the
     * declaration was held to its rules.
     */
    private static Core typed(Hir.Expr conjunct, Scope scope, CheckContext ctx) {
        try {
            return Elaborator.elaborate(conjunct, scope, ctx, Type.BOOL);
        } catch (RuntimeException _) {
            return null;
        }
    }

    /**
     * The cases of the answer no rule names.
     *
     * <p>Nothing is stated about them, which is what the declaration says and not a mistake in it:
     * there is no wildcard arm, so a case left unnamed is a case the behavior promises nothing of.
     * Answered here rather than reported, because a correct model may say nothing about most of what
     * it answers, and a reader wanting to know asks.
     */
    private static List<TypeSymbol> unstatedCases(BehaviorContract contract, Symbols symbols) {
        Set<TypeSymbol> stated = new LinkedHashSet<>();
        for (Rule rule : contract.rules()) {
            if (rule.guard() instanceof Guard.Case(CaseSelector selector)) {
                stated.add(selector.name());
            }
        }
        List<TypeSymbol> unstated = new ArrayList<>();
        for (CaseSelector selector : CaseSpace.of(contract.output(), symbols).selectors()) {
            if (!stated.contains(selector.name())) {
                unstated.add(selector.name());
            }
        }
        return unstated;
    }
}
