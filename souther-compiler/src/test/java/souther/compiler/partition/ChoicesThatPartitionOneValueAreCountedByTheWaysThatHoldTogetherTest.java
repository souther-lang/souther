package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * A lookup of the average in a table, after an {@code if} whose condition looks the same average
 * up in the same table, is read as it is with nothing before it.
 *
 * <p>The condition is read as two choices, each asking of the average and, apart from it, of the
 * grade the row found is compared with. Both part the average by the table's lines, so they hold
 * together only where they agree on the line, and are not as many ways as the product of their
 * sizes. And between them their alternatives leave the average every value, so they come to
 * nothing for the lookup after them ({@link LookupsOfOneValue}).
 */
class ChoicesThatPartitionOneValueAreCountedByTheWaysThatHoldTogetherTest {

    @Test
    void aLookupAfterAnIfLookingTheSameValueUpIsReadAsItIsWithNothingBeforeIt() {
        String model = LookupsOfOneValue.model(LookupsOfOneValue.Body.TESTED_AGAIN, 3);
        List<String> withNothingBefore = LookupsOfOneValue.bordersOfTheLookup(
                LookupsOfOneValue.model(LookupsOfOneValue.Body.NOT_TESTED, 3));

        assertEquals(List.of(), LookupsOfOneValue.unread(model));
        assertFalse(withNothingBefore.isEmpty(), "the lookup has borders to compare");
        assertEquals(withNothingBefore, LookupsOfOneValue.bordersOfTheLookup(model));
    }

    /**
     * The same where the grade compared with is one of a grade for each row: what each row asks
     * of it is a grade two or more from the row's, which some grade is for every row, and no
     * grade is for every row at once, nor for every row above or below the one taken. So each row
     * is met by a grade of its own and by no one grade.
     */
    @Test
    void aLookupAfterAnIfOverAGradeForEachRowIsRead() {
        assertEquals(List.of(), LookupsOfOneValue.unread(LookupsOfOneValue.model(
                LookupsOfOneValue.Body.TESTED_AGAIN, LookupsOfOneValue.Grade.ONE_FOR_EACH_ROW,
                5)));
    }

    /**
     * Control: where the grade is one of three, no grade is two or more from the middle row's,
     * so no row past the {@code if} has the average in the middle row's run, and the lookup after
     * it is not read as reaching every value.
     */
    @Test
    void aLookupAfterAnIfNoGradeGetsPastForSomeRowIsNotRead() {
        assertFalse(LookupsOfOneValue.unread(LookupsOfOneValue.model(
                LookupsOfOneValue.Body.TESTED_AGAIN, LookupsOfOneValue.Grade.ONE_OF_THREE, 3))
                .isEmpty());
    }
}
