package souther.compiler.partition;

import org.junit.jupiter.api.Test;
import souther.compiler.inputs.BlockReason;
import souther.compiler.inputs.TermPath;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.SequencedMap;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a walk over alternatives none of which was taken is said to have come to, in a vocabulary of
 * this test's own: an alternative is a word and what it found out beside it. One said for more than
 * it found out by itself is said in the word for all of it, so a test can tell the alternative
 * handed back as it was from one carrying what the others found out.
 */
class WhatTheAlternativesCameToTest {

    private record Tried(Generator.UnresolvedCombination.Reason word, SearchShortfall found) {}

    private static final WhatTheAlternativesCameTo.Vocabulary<Tried> TRIED =
            new WhatTheAlternativesCameTo.Vocabulary<>() {

                @Override
                public boolean proves(Tried one) {
                    return one.word().provesInfeasible();
                }

                @Override
                public Generator.UnresolvedCombination.Reason word(Tried one) {
                    return one.word();
                }

                @Override
                public SearchShortfall found(Tried one) {
                    return one.found();
                }

                @Override
                public Tried carrying(Tried said, SearchShortfall found) {
                    return new Tried(found.wordFor(said.word()), found);
                }
            };

    private static final CompositionShortfall ASSIGNMENTS =
            CompositionShortfall.of(Set.of(CompositionBudget.ASSIGNMENTS_A_SEARCH_COMPOSES));
    private static final CompositionShortfall WAYS =
            CompositionShortfall.of(Set.of(CompositionBudget.WAYS_UNDER_THE_CASES_TRIED));

    /** What the rules about a position's strings left out of an offer there. */
    private static final SequencedMap<TermPath, StringOfferShortfall> SHORT_AT_THE_CODE =
            offeredShortAt("t.code");

    private static SequencedMap<TermPath, StringOfferShortfall> offeredShortAt(String at) {
        SequencedMap<TermPath, StringOfferShortfall> out = new LinkedHashMap<>();
        out.put(TermPath.of(at), new StringOfferShortfall(List.of(
                new StringOfferShortfall.NotOffered(
                        new StringOfferShortfall.Subject.WhatTheyLeaveTogether(),
                        new StringOfferShortfall.Why.NotRead(
                                new BlockReason.ValueRulesNotReached())))));
        return out;
    }

    private static Tried tried(Generator.UnresolvedCombination.Reason word) {
        return new Tried(word, SearchShortfall.NONE);
    }

    private static final Tried PROOF =
            tried(Generator.UnresolvedCombination.Reason.THE_RULES_LEAVE_NOTHING_THERE);
    private static final Tried ANOTHER_PROOF =
            tried(Generator.UnresolvedCombination.Reason.ONE_POSITION_CANNOT_BE_BOTH);
    private static final Tried NOTHING_COMPOSED =
            tried(Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE);
    private static final Tried REFUSED =
            tried(Generator.UnresolvedCombination.Reason.ALL_CANDIDATES_REJECTED);
    private static final Tried REFUSED_TURNING_ONE_AWAY = new Tried(
            Generator.UnresolvedCombination.Reason.ALL_CANDIDATES_REJECTED,
            SearchShortfall.NONE.uncertifiedWhere(true));
    private static final Tried STOPPED = new Tried(
            Generator.UnresolvedCombination.Reason.wordFor(ASSIGNMENTS.figures()),
            SearchShortfall.of(ASSIGNMENTS));
    private static final Tried OFFERED_SHORT = new Tried(
            Generator.UnresolvedCombination.Reason.NOT_ALL_CANDIDATES_COULD_BE_OFFERED,
            SearchShortfall.of(CompositionShortfall.NONE, SHORT_AT_THE_CODE));

    private static WhatTheAlternativesCameTo.Came<Tried> over(List<Tried> cameToNothing,
                                                              SearchShortfall alsoFound,
                                                              boolean someUnread) {
        return WhatTheAlternativesCameTo.over(cameToNothing, null, alsoFound, someUnread, TRIED);
    }

    private static Tried said(List<Tried> cameToNothing) {
        return said(over(cameToNothing, SearchShortfall.NONE, false));
    }

    private static Tried said(WhatTheAlternativesCameTo.Came<Tried> came) {
        return ((WhatTheAlternativesCameTo.Came.Said<Tried>) came).said();
    }

    @Test
    void oneAlternativeIsWhatItCameTo() {
        assertSame(STOPPED, said(List.of(STOPPED)));
        assertSame(REFUSED_TURNING_ONE_AWAY, said(List.of(REFUSED_TURNING_ONE_AWAY)));
    }

    @Test
    void aProofIsSaidWhereEveryAlternativeThereWasProvedIt() {
        Tried came = said(List.of(PROOF, ANOTHER_PROOF));

        assertTrue(came.word().provesInfeasible());
        assertEquals(came, said(List.of(ANOTHER_PROOF, PROOF)));
    }

    @Test
    void aProofBesideSomethingElseIsNotWhatIsSaidWhicheverCameFirst() {
        assertSame(NOTHING_COMPOSED, said(List.of(PROOF, NOTHING_COMPOSED)));
        assertSame(NOTHING_COMPOSED, said(List.of(NOTHING_COMPOSED, PROOF)));
    }

    /** Two words, neither a proof: the one said is the same whichever was tried first. */
    @Test
    void theWordSaidDoesNotTurnOnTheOrderTheAlternativesWereTriedIn() {
        assertEquals(said(List.of(NOTHING_COMPOSED, REFUSED)),
                said(List.of(REFUSED, NOTHING_COMPOSED)));
    }

    /** A figure one alternative stopped at reaches the reader whichever was tried first. */
    @Test
    void aFigureOneAlternativeMetIsCarriedWhicheverCameFirst() {
        Tried first = said(List.of(NOTHING_COMPOSED, STOPPED));
        Tried last = said(List.of(STOPPED, NOTHING_COMPOSED));

        assertEquals(first, last);
        assertEquals(ASSIGNMENTS, first.found().met());
        assertEquals(Generator.UnresolvedCombination.Reason.wordFor(ASSIGNMENTS.figures()),
                first.word());
    }

    @Test
    void whatEveryAlternativeFoundOutIsCarriedTogether() {
        Tried other = new Tried(Generator.UnresolvedCombination.Reason.wordFor(WAYS.figures()),
                SearchShortfall.of(WAYS, SHORT_AT_THE_CODE));
        Tried came = said(List.of(STOPPED, other));

        assertEquals(ASSIGNMENTS.and(WAYS), came.found().met());
        assertEquals(SHORT_AT_THE_CODE, came.found().offered());
    }

    /**
     * An offer one alternative was short of is carried past another that refused everything it
     * was offered, and said in the word for an offer short of the rules: the refusals are over less
     * than there was.
     */
    @Test
    void anOfferOneAlternativeWasShortOfIsCarriedWhicheverCameFirst() {
        Tried first = said(List.of(REFUSED, OFFERED_SHORT));
        Tried last = said(List.of(OFFERED_SHORT, REFUSED));

        assertEquals(first, last);
        assertEquals(SHORT_AT_THE_CODE, first.found().offered());
        assertEquals(Generator.UnresolvedCombination.Reason.NOT_ALL_CANDIDATES_COULD_BE_OFFERED,
                first.word());
    }

    /**
     * A candidate one alternative turned away for reading back elsewhere makes the refusals of
     * every one of them a search that found what it built standing elsewhere — whichever came
     * first.
     */
    @Test
    void aCandidateOneAlternativeTurnedAwayIsCarriedWhicheverCameFirst() {
        Tried first = said(List.of(REFUSED, REFUSED_TURNING_ONE_AWAY));
        Tried last = said(List.of(REFUSED_TURNING_ONE_AWAY, REFUSED));

        assertEquals(first, last);
        assertEquals(Generator.UnresolvedCombination.Reason.NO_CERTIFIED_WITNESS, first.word());
    }

    @Test
    void proofsBesideTheRestUntriedAreNoProof() {
        Tried came = said(over(List.of(PROOF), SearchShortfall.of(WAYS), false));

        assertEquals(WAYS, came.found().met());
        assertEquals(Generator.UnresolvedCombination.Reason.wordFor(WAYS.figures()), came.word());
    }

    @Test
    void aProofBesideACandidateTurnedAwayIsNoProof() {
        Tried came = said(over(List.of(PROOF), SearchShortfall.NONE.uncertifiedWhere(true),
                false));

        assertEquals(Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE, came.word());
    }

    @Test
    void proofsBesideACaseNobodyReadLeaveNothingToSayItIn() {
        assertEquals(new WhatTheAlternativesCameTo.Came.NothingToSayItIn<Tried>(),
                over(List.of(PROOF), SearchShortfall.NONE, true));
    }

    @Test
    void noAlternativeTriedIsWhatStoppedTheWalkOrNothing() {
        assertEquals(new WhatTheAlternativesCameTo.Came.Untried<Tried>(SearchShortfall.of(WAYS)),
                over(List.of(), SearchShortfall.of(WAYS), false));
        assertEquals(new WhatTheAlternativesCameTo.Came.NothingToSayItIn<Tried>(),
                over(List.of(), SearchShortfall.NONE, false));
    }

    /**
     * Rows passed over under one alternative, and the walk stopped at its figure before the rest:
     * the rows passed over are the answer, and the figure stays with it.
     */
    @Test
    void rowsPassedOverDoNotLoseTheFigureTheWalkStoppedAt() {
        assertEquals(new WhatTheAlternativesCameTo.Came.PassedOver<Tried>(
                        SearchShortfall.of(WAYS.and(ASSIGNMENTS))),
                WhatTheAlternativesCameTo.over(List.of(STOPPED), SearchShortfall.NONE,
                        SearchShortfall.of(WAYS), false, TRIED));
    }

    /**
     * Rows passed over under one alternative, and another offered less than the rules leave: the
     * rows passed over are the answer, and the offer stays with it — the search did not have
     * everything, so no account of it may say it looked at everything.
     */
    @Test
    void rowsPassedOverDoNotLoseAnOfferAnotherAlternativeWasShortOf() {
        assertEquals(new WhatTheAlternativesCameTo.Came.PassedOver<Tried>(
                        SearchShortfall.of(CompositionShortfall.NONE, SHORT_AT_THE_CODE)),
                WhatTheAlternativesCameTo.over(List.of(OFFERED_SHORT), SearchShortfall.NONE,
                        SearchShortfall.NONE, false, TRIED));
    }
}
