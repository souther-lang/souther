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

    @Test
    void aMoveByTheMostMonthsEitherWayIsReadAndOneByMoreIsNot() {
        for (MonthMoveCases.Asked asked : MonthMoveCases.Asked.values()) {
            assertNotNull(MonthMoveCases.of(MonthMoveCases.MOST_MONTHS, asked, false), asked.name());
            assertNotNull(MonthMoveCases.of(-MonthMoveCases.MOST_MONTHS, asked, false), asked.name());
            assertNull(MonthMoveCases.of(MonthMoveCases.MOST_MONTHS + 1, asked, false), asked.name());
            assertNull(MonthMoveCases.of(-MonthMoveCases.MOST_MONTHS - 1, asked, false), asked.name());
        }
    }

    @Test
    void theEdgesOfWhatACountHoldsAreByMoreMonthsThanAreRead() {
        for (MonthMoveCases.Asked asked : MonthMoveCases.Asked.values()) {
            assertNull(MonthMoveCases.of(Long.MIN_VALUE, asked, false),
                    "no absolute value of the least count: " + asked);
            assertNull(MonthMoveCases.of(Long.MAX_VALUE, asked, false), asked.name());
        }
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
        // Long.MAX_VALUE + 25 wraps to Long.MIN_VALUE + 24, and -24 + Long.MIN_VALUE + 24 is none of
        // what a sum of these is: a wrapped sum is never a count read in cases.
        assertEquals(OptionalLong.empty(), MonthMoveCases.chained(Long.MAX_VALUE, 25));
    }
}
