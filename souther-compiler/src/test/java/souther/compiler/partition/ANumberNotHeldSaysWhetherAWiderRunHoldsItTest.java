package souther.compiler.partition;

import org.junit.jupiter.api.Test;
import souther.compiler.observe.RunSensitivity;
import souther.compiler.query.EstablishmentGap;
import souther.exact.ExactFailures;

import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A number the exact arithmetic could not hold keeps which of the two ways it went unheld all the way
 * to what a report says about a wider run.
 *
 * <p>The arithmetic tells a run short of room from an answer with no representation, and the two
 * answer oppositely whether measuring again allowing more could settle the point. Each reader that
 * meets the failure translates it, so the translation is asked for both failures, at each place a
 * reader carries it: the reason a reading of a border came to nothing, the number a search could not
 * hold, and the gap a point is left open by. A reader that caught the failure and wrote one answer
 * for both would pass every test that asked about only one of them.
 */
class ANumberNotHeldSaysWhetherAWiderRunHoldsItTest {

    @Test
    void theTwoFailuresAreTwoAnswers() {
        assertEquals(UnheldNumber.MORE_ROOM_COULD_ANSWER, UnheldNumber.of(ExactFailures.room()));
        assertEquals(UnheldNumber.NO_REPRESENTATION_EXISTS,
                UnheldNumber.of(ExactFailures.range()));
    }

    /** At a border, where the values were read and their number was not worked out. */
    @Test
    void aReadingOfABorderSaysWhetherAWiderRunWorksItOut() {
        assertEquals(RunSensitivity.MAY_CHANGE,
                ReadingGap.of(UnheldNumber.of(ExactFailures.room())).runSensitivity());
        assertEquals(RunSensitivity.UNAFFECTED,
                ReadingGap.of(UnheldNumber.of(ExactFailures.range())).runSensitivity());
    }

    /**
     * And in the gap a point is left open by, which is what a report reads the answer off. A figure
     * beside a number no run holds does not make the gap one a wider run closes: raising the figure
     * leaves the number where it was.
     */
    @Test
    void aGapHoldingANumberNoRunHoldsIsNotClosedByAWiderRun() {
        CompositionCapacity room = new CompositionCapacity(
                CompositionCapacity.Where.PLACES_A_PAIR_IS_WALKED_TO,
                UnheldNumber.of(ExactFailures.room()));
        CompositionCapacity range = new CompositionCapacity(
                CompositionCapacity.Where.PLACES_A_PAIR_IS_WALKED_TO,
                UnheldNumber.of(ExactFailures.range()));
        Set<CompositionBudget> figure = Set.of(CompositionBudget.PLACES_A_PAIR_IS_TRIED_AT);

        assertEquals(RunSensitivity.MAY_CHANGE,
                EstablishmentGap.Composition.of(figure, List.of(), List.of(room))
                        .runSensitivity());
        assertEquals(RunSensitivity.UNAFFECTED,
                EstablishmentGap.Composition.of(figure, List.of(), List.of(range))
                        .runSensitivity());
        assertEquals(RunSensitivity.MAY_CHANGE,
                EstablishmentGap.Composition.of(figure, List.of()).runSensitivity(),
                "and a figure alone is closed by raising it, which is the control");
    }
}
