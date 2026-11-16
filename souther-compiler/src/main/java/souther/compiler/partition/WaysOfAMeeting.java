package souther.compiler.partition;

import souther.compiler.publish.PublicationOrders;

import java.util.Comparator;
import java.util.EnumSet;
import java.util.List;
import java.util.Optional;
import java.util.Set;

/**
 * What every search a meeting was looked for with came to, where none of them made it: one answer,
 * said once over every one of them.
 *
 * <p>A meeting is looked for at each cell that states its decisions, and at each cell by more than
 * one search — the classes, values chosen again, a row held to what the decisions state of the
 * input's numbers, along each way of holding them. A row from any one of them makes it, so these
 * are alternatives for one choice, and the law for alternatives holds
 * ({@link WhatTheAlternativesCameTo}): a proof only where every one of them proved it, the word of
 * the first in the order a report says them among those that proved nothing, and what every one met
 * is every one's. Kept as the answer of the last, a figure an earlier one stopped at is a number
 * nobody is told to raise, and one alternative's proof is said of the others.
 *
 * <p>What was cut from the plan a search ran over travels the same way
 * ({@link CameToNothing#planCut}) and stays apart from what the searches met; what an offer was
 * short of, and where runs stopped ({@link BesideTheWord}), is what every one said. Where the
 * searches met a figure, the word is the one for all of it, as it is for one search that met it
 * ({@link SearchShortfall#wordFor}).
 */
final class WaysOfAMeeting {

    private WaysOfAMeeting() {
    }

    /** What {@code ways}, each having come to nothing, came to together; never of none. */
    static CameToNothing said(List<CameToNothing> ways) {
        if (ways.isEmpty()) {
            throw new IllegalArgumentException("a meeting nothing was looked for at has no search"
                    + " to have come to nothing");
        }
        CompositionShortfall met = CompositionShortfall.NONE;
        BesideTheWord beside = BesideTheWord.NOTHING;
        Set<CompositionBudget> planCut = EnumSet.noneOf(CompositionBudget.class);
        for (CameToNothing each : ways) {
            met = met.and(each.met());
            beside = beside.and(each.why().beside());
            planCut.addAll(each.planCut());
        }
        Comparator<CameToNothing> asSaid = Comparator
                .comparingInt((CameToNothing each) ->
                        PublicationOrders.positionOf(each.why().reason()))
                .thenComparing(each -> String.valueOf(each.why()));
        CameToNothing said = ways.stream().filter(each -> !each.why().reason().provesInfeasible())
                .min(asSaid).orElseGet(() -> ways.stream().min(asSaid).orElseThrow());
        // The word for all that every way found out, which is the question of what was found out
        // and is asked of it ({@link SearchShortfall#wordFor}): a figure, a repertoire or a number
        // not held, and an offer short of a rule, each make the word one that is not a proof.
        Generator.UnresolvedCombination.Reason word = new SearchShortfall(met,
                beside.shortOf(), false, false, Optional.empty(), Optional.empty())
                .wordFor(said.why().reason());
        return new CameToNothing(new Generator.UnresolvedCombination(said.why().classes(), word,
                said.why().detail(), said.why().told(), beside), met, planCut);
    }
}
