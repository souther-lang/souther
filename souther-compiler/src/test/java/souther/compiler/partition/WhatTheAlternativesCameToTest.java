package souther.compiler.partition;

import org.junit.jupiter.api.Test;
import souther.compiler.inputs.TermPath;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.SequencedMap;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertSame;

/**
 * What a walk over alternatives none of which was taken is said to have come to, in a vocabulary of
 * this test's own: an alternative is a name, whether it proved nothing composes, and what of this
 * compiler's it met. One said for more than it met by itself is renamed, so a test can tell the
 * alternative handed back as it was from one carrying what the others met.
 */
class WhatTheAlternativesCameToTest {

    private record Tried(String name, boolean proof, CompositionShortfall met) {}

    private static final WhatTheAlternativesCameTo.Vocabulary<Tried> TRIED =
            new WhatTheAlternativesCameTo.Vocabulary<>() {

                @Override
                public boolean proves(Tried one) {
                    return one.proof();
                }

                @Override
                public CompositionShortfall met(Tried one) {
                    return one.met();
                }

                @Override
                public SequencedMap<TermPath, StringOfferShortfall> offered(Tried one) {
                    return new LinkedHashMap<>();
                }

                @Override
                public Tried carrying(Tried said, CompositionShortfall met,
                                      SequencedMap<TermPath, StringOfferShortfall> offered) {
                    return new Tried("carrying " + said.name(), false, met);
                }
            };

    private static final CompositionShortfall ASSIGNMENTS =
            CompositionShortfall.of(Set.of(CompositionBudget.ASSIGNMENTS_A_SEARCH_COMPOSES));
    private static final CompositionShortfall WAYS =
            CompositionShortfall.of(Set.of(CompositionBudget.WAYS_UNDER_THE_CASES_TRIED));

    private static final Tried PROOF = new Tried("proof", true, CompositionShortfall.NONE);
    private static final Tried ANOTHER_PROOF =
            new Tried("another proof", true, CompositionShortfall.NONE);
    private static final Tried NOTHING_COMPOSED =
            new Tried("nothing composed", false, CompositionShortfall.NONE);
    private static final Tried STOPPED = new Tried("stopped", false, ASSIGNMENTS);

    private static WhatTheAlternativesCameTo.Came<Tried> over(List<Tried> cameToNothing,
                                                              CompositionShortfall alsoMet,
                                                              boolean someUnread) {
        return WhatTheAlternativesCameTo.over(cameToNothing, null, alsoMet, someUnread, TRIED);
    }

    private static Tried said(WhatTheAlternativesCameTo.Came<Tried> came) {
        return ((WhatTheAlternativesCameTo.Came.Said<Tried>) came).said();
    }

    @Test
    void oneAlternativeIsWhatItCameTo() {
        assertSame(STOPPED, said(over(List.of(STOPPED), CompositionShortfall.NONE, false)));
    }

    @Test
    void aProofIsSaidWhereEveryAlternativeThereWasProvedIt() {
        assertSame(PROOF, said(over(List.of(PROOF, ANOTHER_PROOF), CompositionShortfall.NONE,
                false)));
    }

    @Test
    void aProofBesideSomethingElseIsNotWhatIsSaidWhicheverCameFirst() {
        assertSame(NOTHING_COMPOSED, said(over(List.of(PROOF, NOTHING_COMPOSED),
                CompositionShortfall.NONE, false)));
        assertSame(NOTHING_COMPOSED, said(over(List.of(NOTHING_COMPOSED, PROOF),
                CompositionShortfall.NONE, false)));
    }

    /** A figure one alternative stopped at reaches the reader whichever was tried first. */
    @Test
    void aFigureOneAlternativeMetIsCarriedWhicheverCameFirst() {
        Tried first = said(over(List.of(NOTHING_COMPOSED, STOPPED), CompositionShortfall.NONE,
                false));
        Tried last = said(over(List.of(STOPPED, NOTHING_COMPOSED), CompositionShortfall.NONE,
                false));

        assertEquals(ASSIGNMENTS, first.met());
        assertEquals(ASSIGNMENTS, last.met());
        assertEquals("carrying nothing composed", first.name());
        assertSame(STOPPED, last);
    }

    @Test
    void whatEveryAlternativeMetIsCarriedTogether() {
        Tried other = new Tried("other", false, WAYS);

        assertEquals(ASSIGNMENTS.and(WAYS), said(over(List.of(STOPPED, other),
                CompositionShortfall.NONE, false)).met());
    }

    @Test
    void proofsBesideTheRestUntriedAreNoProof() {
        Tried came = said(over(List.of(PROOF), WAYS, false));

        assertEquals("carrying proof", came.name());
        assertEquals(WAYS, came.met());
    }

    @Test
    void proofsBesideACaseNobodyReadLeaveNothingToSayItIn() {
        assertEquals(new WhatTheAlternativesCameTo.Came.NothingToSayItIn<Tried>(),
                over(List.of(PROOF), CompositionShortfall.NONE, true));
    }

    @Test
    void noAlternativeTriedIsWhatStoppedTheWalkOrNothing() {
        assertEquals(new WhatTheAlternativesCameTo.Came.Untried<Tried>(WAYS),
                over(List.of(), WAYS, false));
        assertEquals(new WhatTheAlternativesCameTo.Came.NothingToSayItIn<Tried>(),
                over(List.of(), CompositionShortfall.NONE, false));
    }

    /**
     * Rows passed over under the ways tried, and the walk stopped at its figure before the rest:
     * the rows passed over are the answer, and the figure stays with it.
     */
    @Test
    void rowsPassedOverDoNotLoseTheFigureTheWalkStoppedAt() {
        assertEquals(new WhatTheAlternativesCameTo.Came.PassedOver<Tried>(WAYS.and(ASSIGNMENTS)),
                WhatTheAlternativesCameTo.over(List.of(STOPPED), CompositionShortfall.NONE, WAYS,
                        false, TRIED));
        assertEquals(new WhatTheAlternativesCameTo.Came.PassedOver<Tried>(CompositionShortfall.NONE),
                WhatTheAlternativesCameTo.over(List.of(), CompositionShortfall.NONE,
                        CompositionShortfall.NONE, false, TRIED));
    }
}
