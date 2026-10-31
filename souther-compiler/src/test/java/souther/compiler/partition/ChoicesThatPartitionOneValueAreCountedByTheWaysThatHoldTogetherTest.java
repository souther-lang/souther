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
}
