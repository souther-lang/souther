package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.partition.CompositionAccount;
import souther.compiler.partition.CompositionBudget;
import souther.compiler.partition.Generator;

import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The pairs of numbers an answer turns on are looked over until a row is built whole and nothing
 * the judge refused: a row it refused is a row built, and the next pair may reach one it accepts.
 */
class ARowAJudgeRefusedDoesNotEndTheLookingOverPairsOfNumbersTest {

    @Test
    void aRowBuiltWholeAndAcceptedEndsTheLooking() {
        assertTrue(Adequacy.composedAgainstEverythingAsked(built(false)));
    }

    @Test
    void aRowBuiltWholeAndRefusedDoesNotEndIt() {
        assertFalse(Adequacy.composedAgainstEverythingAsked(built(true)));
    }

    /**
     * A pair with one row accepted and one that built none stands nearer than a pair of five rows
     * all refused, however many attempts each pair made.
     */
    @Test
    void aPairThatReachedARowIsNearerThanOneThatOnlyBuiltMoreRefusedRows() {
        List<Generator.BoundaryAttempt> reached = List.of(built(false), none());
        List<Generator.BoundaryAttempt> refusedOnly = List.of(built(true), built(true), built(true),
                built(true), built(true));

        assertTrue(Adequacy.Nearness.of(reached).compareTo(Adequacy.Nearness.of(refusedOnly)) > 0);
        assertTrue(Adequacy.Nearness.of(refusedOnly).compareTo(Adequacy.Nearness.of(reached)) < 0);
    }

    @Test
    void withTheSameRowsReachedTheMoreBuiltIsNearer() {
        List<Generator.BoundaryAttempt> more = List.of(built(false), built(true));
        List<Generator.BoundaryAttempt> fewer = List.of(built(false), none());

        assertTrue(Adequacy.Nearness.of(more).compareTo(Adequacy.Nearness.of(fewer)) > 0);
    }

    @Test
    void aPairWithASearchAFigureStoppedIsNearerThanOneOfRowsAllRefused() {
        List<Generator.BoundaryAttempt> stopped = List.of(none(),
                new Generator.BoundaryAttempt.Unplanned(
                        new Generator.UnresolvedCombination(List.of("a rule of the decision"),
                                Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE),
                        Set.of(CompositionBudget.WAYS_UNDER_THE_CASES_TRIED),
                        CompositionAccount.NOTHING));
        List<Generator.BoundaryAttempt> refusedOnly = List.of(built(true), built(true));

        assertTrue(Adequacy.Nearness.of(stopped).compareTo(Adequacy.Nearness.of(refusedOnly)) > 0);
    }

    private static Generator.BoundaryAttempt none() {
        return new Generator.BoundaryAttempt.Unresolved(
                new Generator.UnresolvedCombination(List.of("a rule of the decision"),
                        Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE),
                CompositionAccount.NOTHING);
    }

    private static Generator.BoundaryAttempt built(boolean refused) {
        return new Generator.BoundaryAttempt.Built(new Generator.GeneratedRow(
                new Generator.Purpose.ForAPoint("a rule of the decision"), List.of()),
                CompositionAccount.NOTHING, refused);
    }
}
