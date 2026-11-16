package souther.compiler.partition;

import souther.compiler.publish.PublicationOrders;

import java.util.Comparator;
import java.util.EnumSet;
import java.util.List;
import java.util.Set;

/**
 * What the ways a meeting is looked for at came to, where none of them made it: one answer, said
 * once over every one of them.
 *
 * <p>A meeting is looked for at each cell that states its decisions, and a row at any one of them
 * makes it. So these are alternatives for one choice, and the law for alternatives holds
 * ({@link WhatTheAlternativesCameTo}): a proof only where every way proved it, the word of the
 * first in the order a report says them among the ways that proved nothing, and what every way met
 * is every one's. Kept as the answer of the last way, a figure an earlier one stopped at is a number
 * nobody is told to raise, and a way cut short is said to have been looked along completely.
 *
 * <p>What was cut from the plan a way ran over travels the same way ({@link CameToNothing#planCut}),
 * and stays apart from what the ways met.
 */
final class WaysOfAMeeting {

    private WaysOfAMeeting() {
    }

    /** What {@code ways}, each having come to nothing, came to together; never of none. */
    static CameToNothing said(List<CameToNothing> ways) {
        if (ways.isEmpty()) {
            throw new IllegalArgumentException("a meeting nothing was looked for at has no way to"
                    + " have come to nothing");
        }
        CompositionShortfall met = ways.getFirst().met();
        Set<CompositionBudget> planCut = EnumSet.noneOf(CompositionBudget.class);
        for (CameToNothing each : ways) {
            met = met.and(each.met());
            planCut.addAll(each.planCut());
        }
        Comparator<CameToNothing> asSaid = Comparator
                .comparingInt((CameToNothing each) ->
                        PublicationOrders.positionOf(each.why().reason()))
                .thenComparing(each -> String.valueOf(each.why()));
        CameToNothing said = ways.stream().filter(each -> !each.why().reason().provesInfeasible())
                .min(asSaid).orElseGet(() -> ways.stream().min(asSaid).orElseThrow());
        return new CameToNothing(said.why(), met, planCut);
    }
}
