package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.Collections;
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

    private static final Generator.UnresolvedCombination.Reason UNPROVEN =
            Generator.UnresolvedCombination.Reason.THE_SEARCH_LEFT_SOMETHING_UNTRIED;

    private static CameToNothing came(Generator.UnresolvedCombination.Reason word,
                                      Set<CompositionBudget> met, Set<CompositionBudget> cut) {
        return new CameToNothing(new Generator.UnresolvedCombination(List.of(), word),
                CompositionShortfall.of(met), cut);
    }

    @Test
    void aProofIsSaidOnlyWhereEveryWayProvedIt() {
        CameToNothing proved = came(PROOF, Set.of(), Set.of());
        CameToNothing short_ = came(UNPROVEN, Set.of(), Set.of());

        assertEquals(PROOF, WaysOfAMeeting.said(List.of(proved, proved)).why().reason());
        assertEquals(UNPROVEN, WaysOfAMeeting.said(List.of(proved, short_)).why().reason());
        assertEquals(UNPROVEN, WaysOfAMeeting.said(List.of(short_, proved)).why().reason());
    }

    @Test
    void theFiguresEveryWayMetAreMetWhicheverWordIsSaid() {
        CameToNothing first = came(UNPROVEN, Set.of(CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG),
                Set.of());
        CameToNothing second = came(UNPROVEN, Set.of(CompositionBudget.CHOICES_ON_A_WAY_LOOKED_AT),
                Set.of());

        assertEquals(Set.of(CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG,
                        CompositionBudget.CHOICES_ON_A_WAY_LOOKED_AT),
                Set.copyOf(WaysOfAMeeting.said(List.of(first, second)).met().figures()));
    }

    /** The first way's cut is not lost behind a later way that was looked along in full. */
    @Test
    void thePlanEveryWayWasCutShortIsCutShortInTheAnswer() {
        CameToNothing cut = came(UNPROVEN, Set.of(),
                Set.of(CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG));
        CameToNothing whole = came(UNPROVEN, Set.of(), Set.of());

        assertEquals(Set.of(CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG),
                WaysOfAMeeting.said(List.of(cut, whole)).planCut());
        assertEquals(Set.of(CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG),
                WaysOfAMeeting.said(List.of(whole, cut)).planCut());
    }

    @Test
    void whatWasMetAndWhatWasCutStayApart() {
        CameToNothing met = came(UNPROVEN, Set.of(CompositionBudget.CHOICES_ON_A_WAY_LOOKED_AT),
                Set.of());
        CameToNothing cut = came(UNPROVEN, Set.of(),
                Set.of(CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG));

        CameToNothing said = WaysOfAMeeting.said(List.of(met, cut));

        assertEquals(List.of(CompositionBudget.CHOICES_ON_A_WAY_LOOKED_AT),
                List.copyOf(said.met().figures()));
        assertEquals(Set.of(CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG), said.planCut());
    }

    /** Nothing here turns on the order the ways were tried in. */
    @Test
    void theAnswerIsTheSameInEveryOrder() {
        List<CameToNothing> ways = List.of(
                came(PROOF, Set.of(), Set.of()),
                came(UNPROVEN, Set.of(CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG), Set.of()),
                came(Generator.UnresolvedCombination.Reason.NO_CERTIFIED_WITNESS, Set.of(),
                        Set.of(CompositionBudget.CHOICES_ON_A_WAY_LOOKED_AT)));
        CameToNothing expected = WaysOfAMeeting.said(ways);

        for (int turn = 0; turn < 6; turn++) {
            List<CameToNothing> shuffled = new ArrayList<>(ways);
            Collections.rotate(shuffled, turn % 3);
            if (turn >= 3) {
                Collections.reverse(shuffled);
            }
            assertEquals(expected, WaysOfAMeeting.said(shuffled), () -> "in the order " + shuffled);
        }
    }

    @Test
    void aMeetingNothingWasLookedForAtHasNothingToSay() {
        assertThrows(IllegalArgumentException.class, () -> WaysOfAMeeting.said(List.of()));
    }
}
