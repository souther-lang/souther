package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.test.Nightly;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * The lookup of {@link ChoicesThatPartitionOneValueAreCountedByTheWaysThatHoldTogetherTest} over a
 * table of fifty grades, as long as a grade table of social insurance: the ways the two choices
 * hold together are as many at any length of the table.
 *
 * <p>Nightly, for what it costs: every comparison of the lookup is read along a way that tests the
 * grade first, and the cases of each grow with the table.
 */
@Nightly
class ChoicesThatPartitionOneValueAreCountedByTheWaysThatHoldTogetherForALongTableTest {

    @Test
    void aLookupAfterAnIfLookingTheSameValueUpInALongTableIsRead() {
        assertEquals(List.of(), LookupsOfOneValue.unread(
                LookupsOfOneValue.model(LookupsOfOneValue.TESTED_AGAIN, 50)));
    }
}
