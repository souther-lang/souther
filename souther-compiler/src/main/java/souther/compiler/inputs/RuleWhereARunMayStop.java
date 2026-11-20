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
 * One rule of the model that some run reaching it stops in: an operation it is read through ends
 * the run, such as a number worked out past its type.
 *
 * <p>Shown and not a possibility. Said only where a value of the input is shown to exist that gets
 * to the operation, has nothing before it end the run, and works the operation out past its ends;
 * what the ways to the rule leave a number holds rows that never arrive, and is never what shows
 * one does. Where neither a stop nor that there is none is shown, that is said apart
 * ({@link RuleWhereAStopIsNotShown}), and of the same rule as this where one operation of it is
 * shown to stop a run and another is not resolved.
 *
 * <p>Said of the rule and apart from the line it draws, and whatever else is said of it. A rule
 * some of whose runs stop draws its line on the others; one where a run that gets past it comes
 * out the same for every row has no line to draw; and neither is a rule with no line
 * ({@link RuleWithoutALine}) for having a run that stops. A rule every run stops in is a rule with
 * no line, said by its own reason ({@link BlockReason.ComparisonAnswersNowhere}).
 *
 * <p>And where it is known, at which values every run that gets to the rule stops: an operation the
 * rule is read through comes to past its type there whatever else it is over holds. Those say where
 * a run stops if one gets there, and name no row — the ways before the rule are what decide
 * whether a row gets there.
 *
 * @param rule      which rule
 * @param reachedBy every question a reader was offered for the rule, as for a rule with no line
 * @param readAt    every copy of the model's code the rule was read at here
 * @param shown     what shows a run stops in it, each once: never none, since a stop no value of
 *                  the input is shown to come to is not this
 * @param everyRunStops the runs of the values at the rule's places at which every run getting to
 *                  it stops, each once; empty where none is known
 * @param keeping   the bounds on the input that together keep every run getting to the rule from
 *                  stopping in it, each once, where every operation it may stop in stops where the
 *                  representation of its number does and is over the values of one place
 *                  ({@link ABoundThatKeepsEveryRunGoing}); empty where some stop is any other
 */
public record RuleWhereARunMayStop(RuleRef rule, Set<RuleReportAnchor> reachedBy,
                                   ModelOccurrences readAt, List<AStopShown> shown,
                                   List<EveryRunStops> everyRunStops,
                                   List<ABoundThatKeepsEveryRunGoing> keeping)
        implements WhatIsShownOfAStop {

    public RuleWhereARunMayStop {
        if (rule == null || readAt == null) {
            throw new IllegalArgumentException("a run may stop in some rule of the model");
        }
        reachedBy = reachedBy == null ? Set.of() : Set.copyOf(reachedBy);
        RuleCitation.requireReached(rule, reachedBy);
        shown = List.copyOf(new LinkedHashSet<>(shown));
        if (shown.isEmpty()) {
            throw new IllegalArgumentException("a stop said of " + rule
                    + " is shown by some value of the input");
        }
        everyRunStops = List.copyOf(new LinkedHashSet<>(everyRunStops));
        keeping = List.copyOf(new LinkedHashSet<>(keeping));
    }

    /** One reader's finding about a rule a run is shown to stop in, as {@code shown} shows it,
     *  with the values at which every run getting to the rule stops, and the bounds that keep
     *  every run from stopping in it. */
    public static RuleWhereARunMayStop of(RuleCitation cited, ModelOccurrences readAt,
                                          List<AStopShown> shown,
                                          List<EveryRunStops> everyRunStops,
                                          List<ABoundThatKeepsEveryRunGoing> keeping) {
        return new RuleWhereARunMayStop(cited.rule(), RuleCitation.anchorOf(cited), readAt,
                shown, everyRunStops, keeping);
    }

    /** How a reader finds the rule, as for a rule with no line ({@link RuleWithoutALine#cited}). */
    public Set<RuleCitation> cited() {
        return RuleCitation.handlesFor(rule, reachedBy);
    }

    /** Both readers' findings, as one: the rule, with every place either reached it at. */
    @Override
    public RuleWhereARunMayStop mergedWith(WhatIsShownOfAStop other) {
        if (!(other instanceof RuleWhereARunMayStop that) || !rule.equals(that.rule)) {
            throw new IllegalArgumentException("two findings put together are one rule a run may"
                    + " stop in: " + rule + " and " + other);
        }
        Set<RuleReportAnchor> both = new HashSet<>(reachedBy);
        both.addAll(that.reachedBy);
        List<AStopShown> shownBoth = new ArrayList<>(shown);
        shownBoth.addAll(that.shown);
        List<EveryRunStops> stops = new ArrayList<>(everyRunStops);
        stops.addAll(that.everyRunStops);
        List<ABoundThatKeepsEveryRunGoing> bounds = new ArrayList<>(keeping);
        bounds.addAll(that.keeping);
        return new RuleWhereARunMayStop(rule, both, readAt.and(that.readAt), shownBoth, stops,
                bounds);
    }
}
