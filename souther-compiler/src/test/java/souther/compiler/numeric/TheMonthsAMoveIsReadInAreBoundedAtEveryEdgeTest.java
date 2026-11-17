package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import java.util.OptionalLong;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;

/**
 * A move by months is read in cases only where it is by no more months than
 * {@link MonthMoveCases#MOST_MONTHS}, at either end of what a count holds and at either edge of the
 * bound, and a chain of moves is one move only where the months of the chain are a count.
 */
class TheMonthsAMoveIsReadInAreBoundedAtEveryEdgeTest {

    /** The bound is met before what is asked of the move is, so one kind of question carries it:
     *  the day number, which is the one a move by an enormous count would go on to walk. */
    private static final MonthMoveCases.Asked ASKED = MonthMoveCases.Asked.DAY_NUMBER;

    @Test
    void aMoveByTheMostMonthsEitherWayIsReadAndOneByMoreIsNot() {
        assertNotNull(MonthMoveCases.of(MonthMoveCases.MOST_MONTHS, ASKED, false));
        assertNotNull(MonthMoveCases.of(-MonthMoveCases.MOST_MONTHS, ASKED, false));
        assertNull(MonthMoveCases.of(MonthMoveCases.MOST_MONTHS + 1, ASKED, false));
        assertNull(MonthMoveCases.of(-MonthMoveCases.MOST_MONTHS - 1, ASKED, false));
    }

    @Test
    void theEdgesOfWhatACountHoldsAreByMoreMonthsThanAreRead() {
        assertNull(MonthMoveCases.of(Long.MIN_VALUE, ASKED, false),
                "no absolute value of the least count");
        assertNull(MonthMoveCases.of(Long.MAX_VALUE, ASKED, false));
    }

    @Test
    void aChainIsTheSumOfItsMovesWhereTheSumIsACount() {
        assertEquals(OptionalLong.of(5), MonthMoveCases.chained(30, -25));
        assertEquals(OptionalLong.of(Long.MAX_VALUE), MonthMoveCases.chained(Long.MAX_VALUE, 0));
        assertEquals(OptionalLong.of(-1), MonthMoveCases.chained(Long.MAX_VALUE, Long.MIN_VALUE));
    }

    @Test
    void aChainWhoseSumIsNotACountIsNoMoveEvenWhereItWrapsIntoWhatIsRead() {
        assertEquals(OptionalLong.empty(), MonthMoveCases.chained(Long.MAX_VALUE, 1));
        assertEquals(OptionalLong.empty(), MonthMoveCases.chained(Long.MIN_VALUE, -1));
        // Long.MAX_VALUE + 25 wraps to Long.MIN_VALUE + 24, which is below the bound and no sum.
        assertEquals(OptionalLong.empty(), MonthMoveCases.chained(Long.MAX_VALUE, 25));
    }
}
