package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * A meeting is looked for at several cells, and what they came to is one answer: the word of the
 * ways that proved nothing, a proof only where every way proved it, and what every way met and
 * was cut short by, whichever came last.
 */
class TheWaysAMeetingIsLookedForAtAreSaidOnceOverAllOfThemTest {

    private static final Generator.UnresolvedCombination.Reason PROOF =
            Generator.UnresolvedCombination.Reason.ONE_POSITION_CANNOT_BE_BOTH;

    private static final Generator.UnresolvedCombination.Reason UNTRIED =
            Generator.UnresolvedCombination.Reason.THE_SEARCH_LEFT_SOMETHING_UNTRIED;

    private static final Generator.UnresolvedCombination.Reason UNWITNESSED =
            Generator.UnresolvedCombination.Reason.NO_CERTIFIED_WITNESS;

    private static CameToNothing came(Generator.UnresolvedCombination.Reason word,
                                      Set<CompositionBudget> met, Set<CompositionBudget> cut) {
        return new CameToNothing(new Generator.UnresolvedCombination(List.of(), word),
                CompositionShortfall.of(met), cut);
    }

    /** One way that proved nothing is enough to keep the answer from being a proof. */
    @Test
    void aProofIsSaidOnlyWhereEveryWayProvedIt() {
        CameToNothing proved = came(PROOF, Set.of(), Set.of());

        assertEquals(PROOF, WaysOfAMeeting.said(List.of(proved, proved)).why().reason());
        assertEquals(UNTRIED,
                WaysOfAMeeting.said(List.of(proved, came(UNTRIED, Set.of(), Set.of()))).why()
                        .reason());
    }

    /** The first way's figure is not lost behind the last way's. */
    @Test
    void theFiguresEveryWayMetAreMet() {
        CameToNothing first = came(UNTRIED, Set.of(CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG),
                Set.of());
        CameToNothing last = came(UNTRIED, Set.of(CompositionBudget.CHOICES_ON_A_WAY_LOOKED_AT),
                Set.of());

        assertEquals(Set.of(CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG,
                        CompositionBudget.CHOICES_ON_A_WAY_LOOKED_AT),
                Set.copyOf(WaysOfAMeeting.said(List.of(first, last)).met().figures()));
    }

    /** The first way's cut is not lost behind a later way that was looked along in full, and what
     *  was cut stays apart from what was met. */
    @Test
    void thePlanAWayWasCutShortIsCutShortInTheAnswerApartFromWhatWasMet() {
        CameToNothing cut = came(UNTRIED, Set.of(),
                Set.of(CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG));
        CameToNothing met = came(UNTRIED, Set.of(CompositionBudget.CHOICES_ON_A_WAY_LOOKED_AT),
                Set.of());

        CameToNothing said = WaysOfAMeeting.said(List.of(cut, met));

        assertEquals(Set.of(CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG), said.planCut());
        assertEquals(List.of(CompositionBudget.CHOICES_ON_A_WAY_LOOKED_AT),
                List.copyOf(said.met().figures()));
    }

    /** Two ways that say different words, in either order. */
    @Test
    void theAnswerDoesNotTurnOnTheOrderTheWaysWereTriedIn() {
        CameToNothing untried = came(UNTRIED, Set.of(), Set.of());
        CameToNothing unwitnessed = came(UNWITNESSED, Set.of(), Set.of());

        assertEquals(WaysOfAMeeting.said(List.of(untried, unwitnessed)),
                WaysOfAMeeting.said(List.of(unwitnessed, untried)));
    }

    @Test
    void aMeetingNothingWasLookedForAtHasNothingToSay() {
        assertThrows(IllegalArgumentException.class, () -> WaysOfAMeeting.said(List.of()));
    }
}
