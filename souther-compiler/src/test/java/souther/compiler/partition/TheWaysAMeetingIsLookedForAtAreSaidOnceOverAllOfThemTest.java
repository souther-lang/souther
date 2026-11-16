package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.execute.RunStop;

import java.util.List;
import java.util.Optional;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
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

    private static CameToNothing came(Generator.UnresolvedCombination.Reason word,
                                      BesideTheWord beside) {
        return new CameToNothing(new Generator.UnresolvedCombination(List.of(), word, null,
                Optional.empty(), beside), CompositionShortfall.NONE, Set.of());
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
        CameToNothing first = came(UNTRIED, Set.of(CompositionBudget.ELEMENTS_A_PROPOSAL_HOLDS),
                Set.of());
        CameToNothing last = came(UNTRIED, Set.of(CompositionBudget.PAIRINGS_BUILT_AT_ONCE),
                Set.of());

        assertEquals(Set.of(CompositionBudget.ELEMENTS_A_PROPOSAL_HOLDS,
                        CompositionBudget.PAIRINGS_BUILT_AT_ONCE),
                Set.copyOf(WaysOfAMeeting.said(List.of(first, last)).met().figures()));
    }

    /** The first way's cut is not lost behind a later way that was looked along in full, and what
     *  was cut stays apart from what was met. */
    @Test
    void thePlanAWayWasCutShortIsCutShortInTheAnswerApartFromWhatWasMet() {
        CameToNothing cut = came(UNTRIED, Set.of(),
                Set.of(CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG));
        CameToNothing met = came(UNTRIED, Set.of(CompositionBudget.PAIRINGS_BUILT_AT_ONCE),
                Set.of());

        CameToNothing said = WaysOfAMeeting.said(List.of(cut, met));

        assertEquals(Set.of(CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG), said.planCut());
        assertEquals(List.of(CompositionBudget.PAIRINGS_BUILT_AT_ONCE),
                List.copyOf(said.met().figures()));
    }

    /** A repertoire a search did not write is found out as a figure is: the word is no proof. */
    @Test
    void aRepertoireNotWrittenMakesTheWordOneThatIsNoProof() {
        Generator.UnresolvedCombination.Reason said = PROOF;
        CompositionShortfall notWritten = new CompositionShortfall(Set.of(),
                Set.of(CompositionRepertoire.WAYS_A_TOTAL_IS_SPREAD), Set.of());
        CameToNothing way = new CameToNothing(new Generator.UnresolvedCombination(List.of(), said),
                notWritten, Set.of());

        assertEquals(UNTRIED, WaysOfAMeeting.said(List.of(way)).why().reason());
    }

    /** Whichever of the two says the word, what the other said beside its own is said too. */
    @Test
    void whatEveryWayWasShortOfOrStoppedAtIsSaid() {
        WhereARunStopped here = new WhereARunStopped(new RunStop.AtAConstruction("m", "A",
                Optional.empty(), 0, Optional.empty()), Optional.empty());
        WhereARunStopped there = new WhereARunStopped(new RunStop.AtAConstruction("m", "B",
                Optional.empty(), 1, Optional.empty()), Optional.empty());

        CameToNothing said = WaysOfAMeeting.said(List.of(
                came(UNTRIED, BesideTheWord.NOTHING.stopping(List.of(here))),
                came(UNWITNESSED, BesideTheWord.NOTHING.stopping(List.of(there)))));

        assertEquals(Set.of(here, there), Set.copyOf(said.why().beside().stopped()));
    }

    /** A figure one way met is the word's, though the way that says it is the one that met none:
     *  it comes first in the order a report says them. */
    @Test
    void theWordIsTheOneForTheFiguresEveryWayMet() {
        Generator.UnresolvedCombination.Reason silentWord =
                Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE;
        Set<CompositionBudget> figures = Set.of(CompositionBudget.PAIRINGS_BUILT_AT_ONCE);
        Generator.UnresolvedCombination.Reason forTheFigures =
                Generator.UnresolvedCombination.Reason.wordFor(figures);
        assertNotEquals(silentWord, forTheFigures, "or the figure changes no word");

        CameToNothing said = WaysOfAMeeting.said(List.of(
                came(silentWord, Set.of(), Set.of()), came(UNTRIED, figures, Set.of())));

        assertEquals(forTheFigures, said.why().reason());
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
