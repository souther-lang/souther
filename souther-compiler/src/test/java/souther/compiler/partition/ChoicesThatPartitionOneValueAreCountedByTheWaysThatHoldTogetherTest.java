package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

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
        String model = LookupsOfOneValue.model(LookupsOfOneValue.TESTED_AGAIN, 6);

        assertEquals(List.of(), LookupsOfOneValue.unread(model));
        assertEquals(LookupsOfOneValue.aboutTheLookup(
                        LookupsOfOneValue.model(LookupsOfOneValue.NOT_TESTED, 6)),
                LookupsOfOneValue.aboutTheLookup(model));
    }
}
