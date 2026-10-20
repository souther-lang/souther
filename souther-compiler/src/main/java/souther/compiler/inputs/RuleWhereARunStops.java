package souther.compiler.inputs;

import souther.compiler.check.RuleCitation;
import souther.compiler.check.RuleRef;
import souther.compiler.check.RuleReportAnchor;
import souther.compiler.types.ModelOccurrences;

import java.util.HashSet;
import java.util.Set;

/**
 * One rule of the model that some run reaching it stops in: an operation it is read through ends
 * the run, such as a division by nought on one of the ways it is worked out.
 *
 * <p>Said of the rule and apart from the line it draws. A rule whose ways divide by nought on some
 * of them draws its line on the others, and the ways that stop are no part of that line, so neither
 * is this a rule with no line ({@link RuleWithoutALine}) nor a reading that stopped. A rule every
 * run stops in is the first of those, said by its own reason
 * ({@link BlockReason.ComparisonAnswersNowhere}); this is the rule some runs stop in.
 *
 * <p>Only a stop some row can reach. The conditions of the ways to the rule are asked of it, and a
 * stop the ways before it rule out is no run's.
 *
 * @param rule      which rule
 * @param reachedBy every question a reader was offered for the rule, as for a rule with no line
 * @param readAt    every copy of the model's code the rule was read at here
 */
public record RuleWhereARunStops(RuleRef rule, Set<RuleReportAnchor> reachedBy,
                                 ModelOccurrences readAt) {

    public RuleWhereARunStops {
        if (rule == null || readAt == null) {
            throw new IllegalArgumentException("a run stops in some rule of the model");
        }
        reachedBy = reachedBy == null ? Set.of() : Set.copyOf(reachedBy);
        RuleCitation.requireReached(rule, reachedBy);
    }

    /** One reader's finding about a rule some run stops in. */
    public static RuleWhereARunStops of(RuleCitation cited, ModelOccurrences readAt) {
        return new RuleWhereARunStops(cited.rule(), RuleCitation.anchorOf(cited), readAt);
    }

    /** How a reader finds the rule, as for a rule with no line ({@link RuleWithoutALine#cited}). */
    public Set<RuleCitation> cited() {
        return RuleCitation.handlesFor(rule, reachedBy);
    }

    /** Both readers' findings, as one: the rule, with every place either reached it at. */
    public RuleWhereARunStops mergedWith(RuleWhereARunStops other) {
        if (!rule.equals(other.rule)) {
            throw new IllegalArgumentException("two findings put together are one rule some run"
                    + " stops in: " + rule + " and " + other.rule);
        }
        Set<RuleReportAnchor> both = new HashSet<>(reachedBy);
        both.addAll(other.reachedBy);
        return new RuleWhereARunStops(rule, both, readAt.and(other.readAt));
    }
}
