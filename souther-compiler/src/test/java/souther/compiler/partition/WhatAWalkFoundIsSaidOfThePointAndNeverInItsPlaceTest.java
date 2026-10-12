package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import java.util.Optional;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNull;

/**
 * What the walk for a point found out is said beside the word, and the point is named by its own
 * label.
 *
 * <p>A point is its own subject. A sentence carried where the subject goes is printed as the thing
 * no row was found for — {@code no row for `nothing stands at `…` in the value built`} — and the
 * point it was about is named nowhere. So the sentence travels as what the point said, and the
 * place several combinations share stays empty.
 *
 * <p>Asked of the edge, because the edge is where the walk's answer becomes the account a report is
 * written from, and every arm of it carries the sentence in the same place.
 */
class WhatAWalkFoundIsSaidOfThePointAndNeverInItsPlaceTest {

    private static final String LABEL = "stale.daysSince[*] = staleAfter";

    private static final String FOUND = "nothing stands at `opps[*].accountId` in the value built";

    /** A walk that had everything and composed nothing, and said why. */
    @Test
    void aWalkThatComposedNothingSaysWhyBesideThePoint() {
        Generator.UnresolvedCombination why = whyOf(new TermRealizations.Realization.None(
                Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE, FOUND));

        assertEquals(LABEL, why.subject(), "the point is what no row was found for");
        assertNull(why.detail(), "and no position stands in for it");
        assertEquals(Optional.of(FOUND), why.said(), "what the walk found is what the point said");
    }

    /** A walk that wrote some of a population, and said where it was short. */
    @Test
    void aWalkThatWroteSomeOfAPopulationSaysWhereBesideThePoint() {
        Generator.UnresolvedCombination why = whyOf(new TermRealizations.Realization.Unexhausted(
                CompositionShortfall.writing(Set.of(CompositionRepertoire.WAYS_A_TOTAL_IS_SPREAD)),
                FOUND));

        assertEquals(LABEL, why.subject(), "the point is what no row was found for");
        assertNull(why.detail(), "and no position stands in for it");
        assertEquals(Optional.of(FOUND), why.said(), "what the walk found is what the point said");
    }

    /** What an edge that offered nothing comes to at {@link #LABEL}, as the account reads it. */
    private static Generator.UnresolvedCombination whyOf(TermRealizations.Realization came) {
        return assertInstanceOf(Generator.BoundaryAttempt.NoRow.class,
                new Generator.Edge(came, null, null).cameToNothing(LABEL,
                        CompositionAccount.NOTHING),
                "an edge that offered nothing builds no row").why();
    }
}
