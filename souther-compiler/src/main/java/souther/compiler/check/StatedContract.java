package souther.compiler.check;

import souther.compiler.core.Contract.Param;
import souther.compiler.core.Contract.Guard;
import souther.compiler.check.BehaviorContract.Rule;
import souther.compiler.check.BehaviorContract.RuleId;
import souther.compiler.core.Core;
import souther.compiler.diag.SourcePos;
import souther.compiler.types.BindingId;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Optional;

/**
 * What a behavior states about its answer, read into the representation the analysis has rules
 * about and typed there.
 *
 * <p>Two readers want this and they want the same thing of it. The editor asks how much of each rule
 * the check can read; the check at a call asks what of it may be taken as holding. Both are questions
 * about the rule as a term — which case it is about, which names it reads, what it comes to — so it
 * is read once, here, and each of them takes what it needs. Read twice, the answer shown to an author
 * and the answer a caller is given would be two readings that have to be kept agreeing.
 *
 * <p>Every conjunct arrives placed and typed together ({@link Conjunct}). The rest of this package
 * has been got wrong twice by carrying those apart.
 */
public record StatedContract(ValueName.Behavior behavior, List<Param> params, Type output,
                             List<StatedRule> rules) {

    public StatedContract {
        params = List.copyOf(params);
        rules = List.copyOf(rules);
    }

    /**
     * One rule: when it applies, what {@code value} is where it does, and what it states.
     *
     * <p>The clause's name travels with it because a violation is reported by the clause, and a
     * reader of one rule has no way back to the clause it was written under.
     */
    public record StatedRule(RuleId id, Guard guard, BindingId value, Optional<String> clause,
                             List<Conjunct> conjuncts) {

        public StatedRule {
            conjuncts = List.copyOf(conjuncts);
        }
    }

    /**
     * One conjunct the author wrote: where they wrote it, and what it types to for the analysis.
     *
     * @param stated what it types to, or that typing it did not finish ({@link TypedClause})
     */
    public record Conjunct(SourcePos at, TypedClause stated) {}

    /**
     * The same contract with the places taken out of its terms — what a caller depends on, told
     * apart from where the author wrote it.
     *
     * <p>A caller substitutes its own arguments into the terms and reads what they say. It does not
     * read where they were written, and it does not read the coverage ordinals the module numbered
     * them with. Both are on the terms all the same, and both move when anything above the
     * declaration is edited, so a reader comparing the whole of this is a reader an unrelated edit
     * reaches. Nothing else about a contract carries a place: a rule is told by its
     * {@link RuleId}, a parameter by its binding, and neither is where it stands.
     */
    public StatedContract withoutItsPlace() {
        List<StatedRule> out = new ArrayList<>();
        for (StatedRule rule : rules) {
            List<Conjunct> conjuncts = new ArrayList<>();
            for (Conjunct each : rule.conjuncts()) {
                Core form = each.stated().orNull();
                conjuncts.add(new Conjunct(null, form == null ? each.stated()
                        : new TypedClause.Typed(Core.withoutItsPlace(form))));
            }
            out.add(new StatedRule(rule.id(), rule.guard(), rule.value(), rule.clause(), conjuncts));
        }
        return new StatedContract(behavior, params, output, out);
    }

    /**
     * {@code contract} read as the analysis reads it.
     *
     * <p>Types each conjunct over the behavior's own names: the parameters as the contract says they
     * are bound, and {@code value} as what the case the rule is about holds. Which is what a caller
     * substitutes into — the names are the declaration's, and the values are the call's.
     *
     * @param declaring the module's clauses as the analysis reads them, which is what turns a
     *                  conjunct into the tree that has rules about it
     * @param helpers the signatures a rule may reach without a binding
     */
    public static StatedContract of(BehaviorContract contract, ClausesForDischarge declaring,
                                    Symbols symbols, Map<String, Type> helpers) {
        CheckContext ctx = CheckContext.of(symbols).forDischarge();
        List<StatedRule> rules = new ArrayList<>();
        for (BehaviorContract.Clause clause : contract.clauses()) {
            for (Rule rule : clause.rules()) {
                Scope scope = BehaviorChecker.scopeOf(contract, rule).reaching(helpers);
                List<Conjunct> conjuncts = new ArrayList<>();
                for (ClausesForDischarge.ClauseReading written : declaring.conjunctsOf(
                        rule.statement(), BehaviorContract.ownerOf(contract.behavior()))) {
                    conjuncts.add(new Conjunct(written.at(),
                            SecondaryClauseReading.of(written.read(), written.standing(), scope,
                                    ctx, "typing " + contract.behavior().name())));
                }
                rules.add(new StatedRule(rule.id(), rule.guard(), rule.value(), clause.name(),
                        conjuncts));
            }
        }
        return new StatedContract(contract.behavior(), contract.params(), contract.output(), rules);
    }

    /** Where a rule states nothing this can read, so a reader asking what to assume has nothing to
     * take from it. */
    public boolean isEmpty() {
        return rules.isEmpty();
    }
}
