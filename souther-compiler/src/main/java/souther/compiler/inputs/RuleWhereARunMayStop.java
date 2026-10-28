package souther.compiler.inputs;

import souther.compiler.check.RuleCitation;
import souther.compiler.check.RuleRef;
import souther.compiler.check.RuleReportAnchor;
import souther.compiler.types.ModelOccurrences;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
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
 * <p>And where it is known, at which values every run that gets to the rule stops: an operation the
 * rule is read through comes to past its type there whatever else it is over holds. Those are
 * proofs and not possibilities, and still name no row — the ways before the rule are what decide
 * whether a row gets there.
 *
 * @param rule      which rule
 * @param reachedBy every question a reader was offered for the rule, as for a rule with no line
 * @param readAt    every copy of the model's code the rule was read at here
 * @param everyRunStops the runs of the values at the rule's places at which every run getting to
 *                  it stops, each once; empty where none is known
 */
public record RuleWhereARunMayStop(RuleRef rule, Set<RuleReportAnchor> reachedBy,
                                   ModelOccurrences readAt, List<EveryRunStops> everyRunStops) {

    public RuleWhereARunMayStop {
        if (rule == null || readAt == null) {
            throw new IllegalArgumentException("a run may stop in some rule of the model");
        }
        reachedBy = reachedBy == null ? Set.of() : Set.copyOf(reachedBy);
        RuleCitation.requireReached(rule, reachedBy);
        everyRunStops = List.copyOf(new LinkedHashSet<>(everyRunStops));
    }

    /** One reader's finding about a rule a run may stop in. */
    public static RuleWhereARunMayStop of(RuleCitation cited, ModelOccurrences readAt) {
        return of(cited, readAt, List.of());
    }

    /** The same, with the values at which every run getting to the rule stops. */
    public static RuleWhereARunMayStop of(RuleCitation cited, ModelOccurrences readAt,
                                          List<EveryRunStops> everyRunStops) {
        return new RuleWhereARunMayStop(cited.rule(), RuleCitation.anchorOf(cited), readAt,
                everyRunStops);
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
        List<EveryRunStops> stops = new ArrayList<>(everyRunStops);
        stops.addAll(other.everyRunStops);
        return new RuleWhereARunMayStop(rule, both, readAt.and(other.readAt), stops);
    }
}
