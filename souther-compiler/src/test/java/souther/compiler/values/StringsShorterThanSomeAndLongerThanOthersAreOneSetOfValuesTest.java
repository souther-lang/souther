package souther.compiler.values;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The strings shorter than some fewest code points and those longer than some most are one set of
 * values with two runs of lengths, held as numbers whatever the lengths are; runs that touch are
 * one, and the values of two such sets together are those at the lengths both hold.
 */
class StringsShorterThanSomeAndLongerThanOthersAreOneSetOfValuesTest {

    private static final ValuesAtLengths OUTSIDE_ONE_TO_A_HUNDRED_THOUSAND =
            ValuesAtLengths.atAnyOf(ValueSet.ANY, List.of(new ValuesWithin(ValueSet.ANY, 0, 0L),
                    ValuesWithin.longerThan(ValueSet.ANY, 100_000)));

    @Test
    void aStringOfEitherRunIsOneOfThemAndOneBetweenIsNot() {
        assertTrue(OUTSIDE_ONE_TO_A_HUNDRED_THOUSAND.has(new Value.Text("")));
        assertTrue(OUTSIDE_ONE_TO_A_HUNDRED_THOUSAND.has(new Value.Text("a".repeat(100_001))));
        assertFalse(OUTSIDE_ONE_TO_A_HUNDRED_THOUSAND.has(new Value.Text("a")));
        assertTrue(OUTSIDE_ONE_TO_A_HUNDRED_THOUSAND.shownToHoldAValue());
    }

    @Test
    void runsThatTouchAreOneAndEveryLengthIsNoBound() {
        ValuesAtLengths touching = ValuesAtLengths.atAnyOf(ValueSet.ANY, List.of(
                new ValuesWithin(ValueSet.ANY, 0, 3L), ValuesWithin.longerThan(ValueSet.ANY, 3)));
        assertEquals(ValuesAtLengths.all(ValueSet.ANY), touching);
        assertFalse(touching.bounded());
    }

    @Test
    void meetingASetOfOneRunLeavesTheLengthsBothHold() {
        ValuesWithin upToTen = new ValuesWithin(ValueSet.ANY, 0, 10L);
        List<ValuesWithin> both = OUTSIDE_ONE_TO_A_HUNDRED_THOUSAND.pieces().stream()
                .map(each -> each.meeting(upToTen, ValueSet.ANY))
                .filter(each -> !each.shownToHoldNone()).toList();
        assertEquals(List.of(new ValuesWithin(ValueSet.ANY, 0, 0L)), both);
        ValuesWithin fromTwo = new ValuesWithin(ValueSet.ANY, 2, 10L);
        assertTrue(OUTSIDE_ONE_TO_A_HUNDRED_THOUSAND.pieces().stream()
                .allMatch(each -> each.meeting(fromTwo, ValueSet.ANY).shownToHoldNone()));
    }

    /** Regions of different sets at the same lengths stay apart, and each is a side of its own. */
    @Test
    void regionsOfDifferentSetsAreKeptApart() {
        ValuesAtLengths some = new ValuesAtLengths(List.of(
                new ValuesWithin(ValueSet.ANY, 0, 5L),
                ValuesWithin.longerThan(ValueSet.just(new Value.Text("a")), 5)));
        assertEquals(2, some.pieces().size());
        assertTrue(some.has(new Value.Text("ab")));
        assertFalse(some.has(new Value.Text("a".repeat(7) + "b")));
    }
}
