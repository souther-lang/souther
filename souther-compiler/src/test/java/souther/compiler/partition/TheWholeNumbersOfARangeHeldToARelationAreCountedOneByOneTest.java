package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.Rel;

import java.math.BigInteger;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * The whole numbers of a range that stand in a relation to a number are the ones counted one by
 * one, at ends and numbers that are whole and that are not: from the least of them to the greatest,
 * or none ({@link FormRange#heldTo}).
 *
 * <p>Every end and every number from minus three to three by halves, under every relation. A range
 * from {@code 0.5} to {@code 2.5} holds {@code 1} and {@code 2}, and below {@code 1.5} is up to
 * {@code 1}: an end or a number taken as if it were whole would keep a number the relation leaves
 * out, or leave out one it keeps.
 */
class TheWholeNumbersOfARangeHeldToARelationAreCountedOneByOneTest {

    @Test
    void theWholeNumbersHeldAreTheOnesCounted() {
        int asked = 0;
        for (int leastHalves = -6; leastHalves <= 6; leastHalves++) {
            for (int greatestHalves = leastHalves; greatestHalves <= 6; greatestHalves++) {
                for (int numberHalves = -7; numberHalves <= 7; numberHalves++) {
                    for (Rel rel : Rel.values()) {
                        FormRange range = new FormRange(half(leastHalves), half(greatestHalves));
                        ExactRatio number = half(numberHalves);
                        assertEquals(counted(range, rel, number), range.heldTo(rel, number),
                                () -> range + " " + rel + " " + number);
                        asked++;
                    }
                }
            }
        }
        assertEquals(13 * 14 / 2 * 15 * Rel.values().length, asked);
    }

    /** The whole numbers of {@code range} that stand in {@code rel} to {@code number}, from the
     *  least to the greatest, counted one by one; null where there are none. */
    private static FormRange counted(FormRange range, Rel rel, ExactRatio number) {
        ExactRatio least = null;
        ExactRatio greatest = null;
        for (int whole = -4; whole <= 4; whole++) {
            ExactRatio each = ExactRatio.of(BigInteger.valueOf(whole));
            if (each.compareTo(range.least()) < 0 || each.compareTo(range.greatest()) > 0
                    || !rel.holds(Integer.signum(each.compareTo(number)))) {
                continue;
            }
            least = least == null ? each : least;
            greatest = each;
        }
        return least == null ? null : new FormRange(least, greatest);
    }

    private static ExactRatio half(int halves) {
        return ExactRatio.of(BigInteger.valueOf(halves), BigInteger.TWO);
    }
}
