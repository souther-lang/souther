package souther.compiler.partition;

import org.junit.jupiter.api.Test;
import souther.compiler.numeric.UnheldNumber;
import souther.compiler.observe.RunSensitivity;
import souther.compiler.query.EstablishmentGap;
import souther.exact.ExactFailures;

import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;

/**
 * A wider run is this compiler on the same host with its figures widened, so a point is left open to
 * one only where nothing but figures left it open.
 *
 * <p>Three things leave a composing short, and one of them is a figure. A population this compiler
 * writes some of is reached by somebody writing the rest, and a number it could not hold is reached
 * by a host with more room or by nothing; a wider run reaches neither. So a gap that holds either of
 * them is unaffected however many figures sit beside it, and each part answers for itself rather than
 * being answered for by the gap.
 *
 * <p>Both kinds of number not held, because the arithmetic tells them apart and a reader is told
 * which. That is a difference on another axis: a host short of room is still the host, and a host is
 * not an allowance.
 */
class NothingButAFigureIsWidenedByAWiderRunTest {

    private static final Set<CompositionBudget> FIGURE =
            Set.of(CompositionBudget.PLACES_A_PAIR_IS_TRIED_AT);

    private static final Set<CompositionRepertoire> WRITES_SOME_OF =
            Set.of(CompositionRepertoire.PLACES_A_PAIR_IS_TRIED_AT_ON_A_LINE);

    /** The two failures stay two, which is what the sentence a reader is given is written from. */
    @Test
    void theTwoFailuresAreTwoAnswers() {
        assertNotEquals(UnheldNumber.of(ExactFailures.room()),
                UnheldNumber.of(ExactFailures.range()));
        assertEquals(UnheldNumber.MORE_ROOM_COULD_ANSWER, UnheldNumber.of(ExactFailures.room()));
        assertEquals(UnheldNumber.NO_REPRESENTATION_EXISTS,
                UnheldNumber.of(ExactFailures.range()));
    }

    /** At a border, where the values were read and their number was not worked out: either way,
     *  no wider run works it out. */
    @Test
    void aReadingOfABorderIsNotWidenedEitherWay() {
        assertEquals(RunSensitivity.UNAFFECTED,
                ReadingGap.of(UnheldNumber.of(ExactFailures.room())).runSensitivity());
        assertEquals(RunSensitivity.UNAFFECTED,
                ReadingGap.of(UnheldNumber.of(ExactFailures.range())).runSensitivity());
    }

    /** The rule a gap is answered by, over every way the three vocabularies meet. */
    @Test
    void aGapIsWidenedOnlyWhereFiguresAloneLeftItOpen() {
        Set<CompositionCapacity> room = Set.of(unheld(UnheldNumber.of(ExactFailures.room())));
        Set<CompositionCapacity> range = Set.of(unheld(UnheldNumber.of(ExactFailures.range())));

        assertEquals(RunSensitivity.MAY_CHANGE, sensitivity(FIGURE, Set.of(), Set.of()),
                "figures alone");
        assertEquals(RunSensitivity.UNAFFECTED, sensitivity(FIGURE, WRITES_SOME_OF, Set.of()),
                "a figure beside a population written some of");
        assertEquals(RunSensitivity.UNAFFECTED, sensitivity(FIGURE, Set.of(), room),
                "a figure beside a number the host had no room for");
        assertEquals(RunSensitivity.UNAFFECTED, sensitivity(FIGURE, Set.of(), range),
                "a figure beside a number with no representation");
        assertEquals(RunSensitivity.UNAFFECTED, sensitivity(Set.of(), WRITES_SOME_OF, Set.of()),
                "a population alone");
        assertEquals(RunSensitivity.UNAFFECTED, sensitivity(Set.of(), Set.of(), room),
                "a number not held alone");
    }

    private static CompositionCapacity unheld(UnheldNumber why) {
        return new CompositionCapacity(CompositionCapacity.Where.PLACES_A_PAIR_IS_WALKED_TO, why);
    }

    private static RunSensitivity sensitivity(Set<CompositionBudget> budgets,
                                              Set<CompositionRepertoire> repertoires,
                                              Set<CompositionCapacity> capacities) {
        return EstablishmentGap.Composition.of(budgets, repertoires, capacities).runSensitivity();
    }
}
