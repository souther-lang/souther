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
 * of clause. It is the same question: what the clause owes, and how much of it this compiler could
 * carry into a form a guard can be held against ({@link StaticReading}). What follows from the answer
 * differs — an invariant's classification says what discharges a construction, a rule's says how much
 * of the relation is there to be read at a call — but what is being asked of the expression is one
 * thing, and asking it twice would be two answers to keep agreeing.
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
     * What the check can read of what {@code stated} states, rule by rule.
     *
     * <p>Handed the rules as the analysis holds them rather than the declaration they came from.
     * Which case a rule is about, what {@code value} is there, where each conjunct was written and
     * what it types to are all settled by the one reading ({@link StatedContract}), and this asks one
     * question of it — the same reading the check at a call takes what it may assume from, so what an
     * author is shown and what a caller is given cannot drift apart.
     *
     */
    public static ContractDischarge of(StatedContract stated, Symbols symbols,
                                       ReadingPolicy policy) {
        List<RuleDischarge> classified = new ArrayList<>();
        for (StatedContract.StatedRule rule : stated.rules()) {
            classified.addAll(of(stated, rule, symbols, policy));
        }
        return new ContractDischarge(classified, unstatedCases(stated, symbols));
    }

    /**
     * One rule, conjunct by conjunct.
     *
     * <p>Each conjunct on its own, as a data's are: what discharges one half of {@code a && b} is not
     * what discharges the other, and an author acts on the half. The name the clause was declared
     * with goes on each of them, because a violation is reported by the clause however many conjuncts
     * it was written as.
     */
    private static List<RuleDischarge> of(StatedContract contract, StatedContract.StatedRule rule,
                                          Symbols symbols, ReadingPolicy policy) {
        // The parameters and `value` stand for themselves. A caller hands one value per parameter and
        // the behavior answers one value, so a rule naming either names something wherever it is read
        // — entered as locations, and nothing is seeded of them, since what the rule states is the
        // question.
        Set<BindingId> named = new LinkedHashSet<>();
        for (ContractParam param : contract.params()) {
            named.add(param.binding());
        }
        named.add(rule.value());
        Terms naming = new Terms(symbols, policy);
        Denotations locations =
                Denotations.none().locations(named, naming::placeSubject, naming::placeTerm);

        List<RuleDischarge> out = new ArrayList<>();
        for (StatedContract.Conjunct conjunct : rule.conjuncts()) {
            out.add(new RuleDischarge(rule.id(), InvariantChecker
                    .capabilityOf(conjunct, locations, symbols, policy,
                            contract.behavior().name())
                    .named(rule.clause())));
        }
        return out;
    }

    /**
     * The cases of the answer no rule names.
     *
     * <p>Nothing is stated about them, which is what the declaration says and not a mistake in it:
     * there is no wildcard arm, so a case left unnamed is a case the behavior promises nothing of.
     * Answered here rather than reported, because a correct model may say nothing about most of what
     * it answers, and a reader wanting to know asks.
     */
    private static List<TypeSymbol> unstatedCases(StatedContract contract, Symbols symbols) {
        Set<TypeSymbol> stated = new LinkedHashSet<>();
        for (StatedContract.StatedRule rule : contract.rules()) {
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
