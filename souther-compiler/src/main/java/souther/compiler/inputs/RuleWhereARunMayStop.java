package souther.compiler.inputs;

import souther.compiler.check.RuleCitation;
import souther.compiler.check.RuleRef;
import souther.compiler.check.RuleReportAnchor;
import souther.compiler.types.ModelOccurrences;

import java.util.HashSet;
import java.util.Set;

/**
 * One rule of the model that a run reaching it may stop in: an operation it is read through ends
 * the run, such as a division by nought on one of the ways it is worked out.
 *
 * <p>A possibility and not a run shown to exist. The conditions of the ways to the rule are asked
 * whether they leave a row for the stop, and a stop is dropped only where they are shown to leave
 * none; where that is not shown it stays, as every other fact read off the way does.
 *
 * <p>Said of the rule and apart from the line it draws, and whatever else is said of it. A rule
 * whose ways divide by nought on some of them draws its line on the others; one where a run that
 * gets past it comes out the same for every row has no line to draw; and neither is a rule with no
 * line ({@link RuleWithoutALine}) for having a run that stops. A rule every run stops in is a rule
 * with no line, said by its own reason ({@link BlockReason.ComparisonAnswersNowhere}).
 *
 * @param rule      which rule
 * @param reachedBy every question a reader was offered for the rule, as for a rule with no line
 * @param readAt    every copy of the model's code the rule was read at here
 */
public record RuleWhereARunMayStop(RuleRef rule, Set<RuleReportAnchor> reachedBy,
                                   ModelOccurrences readAt) {

    public RuleWhereARunMayStop {
        if (rule == null || readAt == null) {
            throw new IllegalArgumentException("a run may stop in some rule of the model");
        }
        reachedBy = reachedBy == null ? Set.of() : Set.copyOf(reachedBy);
        RuleCitation.requireReached(rule, reachedBy);
    }

    /** One reader's finding about a rule a run may stop in. */
    public static RuleWhereARunMayStop of(RuleCitation cited, ModelOccurrences readAt) {
        return new RuleWhereARunMayStop(cited.rule(), RuleCitation.anchorOf(cited), readAt);
    }

    /** How a reader finds the rule, as for a rule with no line ({@link RuleWithoutALine#cited}). */
    public Set<RuleCitation> cited() {
        return RuleCitation.handlesFor(rule, reachedBy);
    }

    /** Both readers' findings, as one: the rule, with every place either reached it at. */
    public RuleWhereARunMayStop mergedWith(RuleWhereARunMayStop other) {
        if (!rule.equals(other.rule)) {
            throw new IllegalArgumentException("two findings put together are one rule a run may"
                    + " stop in: " + rule + " and " + other.rule);
        }
        Set<RuleReportAnchor> both = new HashSet<>(reachedBy);
        both.addAll(other.reachedBy);
        return new RuleWhereARunMayStop(rule, both, readAt.and(other.readAt));
    }
}
