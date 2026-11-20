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
 * One rule of the model where whether a run stops on its way through it is not resolved: neither
 * that one does nor that none does is shown.
 *
 * <p>Not a stop, and not that there is none. Said of the rule, apart from the line it draws and
 * from any place it is filed at, and beside a stop shown in the same rule
 * ({@link RuleWhereARunMayStop}): showing that one operation stops a run says nothing of another.
 *
 * <p>Two things leave it unresolved, and either is enough. An operation the rule works out to be
 * evaluated, of which neither is shown ({@code notShown}, which and why for each); and what a
 * construction a run works out on the way to the rule asks of the run ({@code asks}), where a run
 * that does not meet it stops before it gets to the rule, and no run is shown to be one that does
 * not. Each is said of what it is about and not of the rule as a whole.
 *
 * @param rule      which rule
 * @param reachedBy every question a reader was offered for the rule, as for a rule with no line
 * @param readAt    every copy of the model's code the rule was read at here
 * @param notShown  each operation neither is shown of, and why, each once, in the order the rule
 *                  works them out; empty where all of them are shown one way or the other
 * @param asks      what each construction on the way asks of a run, each once and as written;
 *                  empty where none asks anything
 * @param everyRunStops the values at which every run getting to the rule stops, each once, where
 *                  that is known: a proof of where a run stops if one gets there, and not that one
 *                  does, which is what is not resolved here. Never what makes this said: a stop
 *                  no run gets to is no stop left unresolved
 * @param keeping   the bounds on the input that together keep every run getting to the rule from
 *                  the stops told, each once ({@link ABoundThatKeepsEveryRunGoing}): enough to keep
 *                  a run from them whether or not one stops there now; empty where some stop is
 *                  where no such bound is said
 */
public record RuleWhereAStopIsNotShown(RuleRef rule, Set<RuleReportAnchor> reachedBy,
                                       ModelOccurrences readAt, List<AStopNotShown> notShown,
                                       List<WhatAConstructionAsks> asks,
                                       List<EveryRunStops> everyRunStops,
                                       List<ABoundThatKeepsEveryRunGoing> keeping)
        implements WhatIsShownOfAStop {

    public RuleWhereAStopIsNotShown {
        if (rule == null || readAt == null) {
            throw new IllegalArgumentException("a stop is not shown at some rule of the model");
        }
        reachedBy = reachedBy == null ? Set.of() : Set.copyOf(reachedBy);
        RuleCitation.requireReached(rule, reachedBy);
        notShown = List.copyOf(new LinkedHashSet<>(notShown));
        asks = List.copyOf(new LinkedHashSet<>(asks));
        everyRunStops = List.copyOf(new LinkedHashSet<>(everyRunStops));
        keeping = List.copyOf(new LinkedHashSet<>(keeping));
        if (notShown.isEmpty() && asks.isEmpty()) {
            throw new IllegalArgumentException("a stop is not shown for some reason: " + rule);
        }
    }

    /** One reader's finding about a rule. */
    public static RuleWhereAStopIsNotShown of(RuleCitation cited, ModelOccurrences readAt,
                                              List<AStopNotShown> notShown,
                                              List<WhatAConstructionAsks> asks,
                                              List<EveryRunStops> everyRunStops,
                                              List<ABoundThatKeepsEveryRunGoing> keeping) {
        return new RuleWhereAStopIsNotShown(cited.rule(), RuleCitation.anchorOf(cited), readAt,
                notShown, asks, everyRunStops, keeping);
    }

    /** How a reader finds the rule, as for a rule with no line ({@link RuleWithoutALine#cited}). */
    public Set<RuleCitation> cited() {
        return RuleCitation.handlesFor(rule, reachedBy);
    }

    /** Both readers' findings, as one: the rule, with every place either reached it at, every
     *  operation either left unresolved, every construction either told of and every stop either
     *  proved. */
    @Override
    public RuleWhereAStopIsNotShown mergedWith(WhatIsShownOfAStop other) {
        if (!(other instanceof RuleWhereAStopIsNotShown that) || !rule.equals(that.rule)) {
            throw new IllegalArgumentException("two findings put together are one rule whose "
                    + "stop is not shown: " + rule + " and " + other);
        }
        Set<RuleReportAnchor> both = new HashSet<>(reachedBy);
        both.addAll(that.reachedBy);
        List<AStopNotShown> open = new ArrayList<>(notShown);
        open.addAll(that.notShown);
        List<WhatAConstructionAsks> asked = new ArrayList<>(asks);
        asked.addAll(that.asks);
        List<EveryRunStops> stops = new ArrayList<>(everyRunStops);
        stops.addAll(that.everyRunStops);
        List<ABoundThatKeepsEveryRunGoing> bounds = new ArrayList<>(keeping);
        bounds.addAll(that.keeping);
        return new RuleWhereAStopIsNotShown(rule, both, readAt.and(that.readAt), open, asked,
                stops, bounds);
    }
}
