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
    void aChainIsTheSumOfItsMovesWhereEveryMoveAndTheSumAreRead() {
        assertEquals(OptionalLong.of(2), MonthMoveCases.chained(1, 1));
        assertEquals(OptionalLong.of(0), MonthMoveCases.chained(24, -24));
        assertEquals(OptionalLong.of(-24), MonthMoveCases.chained(-24, 0));
    }

    @Test
    void aChainIsNoMoveWhereOneOfItsMovesIsByMoreMonthsThanAreRead() {
        // The sum of these is nought, and the first is a move no case says anything of.
        assertEquals(OptionalLong.empty(), MonthMoveCases.chained(25, -25));
        assertEquals(OptionalLong.empty(), MonthMoveCases.chained(-25_000_000_000L, 25_000_000_000L));
    }

    @Test
    void aChainWhoseSumIsByMoreMonthsThanAreReadIsNoMoveEvenWhereItWraps() {
        assertEquals(OptionalLong.empty(), MonthMoveCases.chained(24, 1));
        // Long.MAX_VALUE + 25 wraps to Long.MIN_VALUE + 24, below the bound and no sum.
        assertEquals(OptionalLong.empty(), MonthMoveCases.chained(Long.MAX_VALUE, 25));
        assertEquals(OptionalLong.empty(), MonthMoveCases.chained(Long.MAX_VALUE, Long.MIN_VALUE));
    }
}
