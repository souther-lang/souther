package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.types.BinOp;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a sum and a product of two numbers come to, from the ends each is held to, is worked out by
 * two readers: the range of a form of the input ({@link FormRange}), and the intervals the
 * region's bounds are put through ({@link Intervals}). They are one arithmetic, and over closed
 * ranges they answer with the same ends, so that a rule written into one is a rule written into
 * the other.
 */
class TheRangeOfASumAndOfAProductIsTheSameWhicheverReaderAsksTest {

    private static final long[] ENDS = {-3, -1, 0, 2, 5};

    @Test
    void aProductOfTwoClosedRangesHasTheEndsEitherReaderGives() {
        for (long[] left : ranges()) {
            for (long[] right : ranges()) {
                FormRange ofTheForms = FormRange.combined(BinOp.MUL, range(left), range(right));
                NumericDomain.Bounds ofTheBounds = souther.compiler.numeric.Intervals.product(
                        bounds(left), bounds(right));
                assertSame(ofTheForms, ofTheBounds, "product", left, right);
            }
        }
    }

    @Test
    void aSumOfTwoClosedRangesHasTheEndsEitherReaderGives() {
        LinearForm<String> sum = new LinearForm<>(ExactRatio.ZERO,
                Map.of("x", ExactRatio.ONE, "y", ExactRatio.ONE));
        for (long[] left : ranges()) {
            for (long[] right : ranges()) {
                FormRange ofTheForms = FormRange.combined(BinOp.ADD, range(left), range(right));
                NumericDomain.Bounds ofTheBounds = souther.compiler.numeric.Intervals.of(sum,
                        name -> name.equals("x") ? bounds(left) : bounds(right));
                assertSame(ofTheForms, ofTheBounds, "sum", left, right);
            }
        }
    }

    /** The form {@code 2x - y}, which weighs one number against the other and so turns a range
     *  over. */
    @Test
    void aWeightedDifferenceHasTheEndsEitherReaderGives() {
        LinearForm<String> difference = new LinearForm<>(ExactRatio.ZERO,
                Map.of("x", ExactRatio.of(BigInteger.TWO), "y", ExactRatio.of(BigInteger.ONE.negate())));
        for (long[] left : ranges()) {
            for (long[] right : ranges()) {
                FormRange twice = FormRange.combined(BinOp.ADD, range(left), range(left));
                FormRange ofTheForms = FormRange.combined(BinOp.SUB, twice, range(right));
                NumericDomain.Bounds ofTheBounds = souther.compiler.numeric.Intervals.of(difference,
                        name -> name.equals("x") ? bounds(left) : bounds(right));
                assertSame(ofTheForms, ofTheBounds, "2x - y", left, right);
            }
        }
    }

    private static void assertSame(FormRange ofTheForms, NumericDomain.Bounds ofTheBounds,
                                   String what, long[] left, long[] right) {
        String at = what + " of " + List.of(left[0], left[1]) + " and " + List.of(right[0], right[1]);
        assertTrue(ofTheForms != null, at);
        assertTrue(ofTheBounds.min() != null && ofTheBounds.max() != null, at);
        assertEquals(ofTheForms.least(), Count.number(ofTheBounds.min().at()).exactly(), at);
        assertEquals(ofTheForms.greatest(), Count.number(ofTheBounds.max().at()).exactly(), at);
    }

    private static List<long[]> ranges() {
        List<long[]> out = new ArrayList<>();
        for (long least : ENDS) {
            for (long greatest : ENDS) {
                if (least <= greatest) {
                    out.add(new long[] {least, greatest});
                }
            }
        }
        return out;
    }

    private static FormRange range(long[] ends) {
        return new FormRange(ExactRatio.of(BigInteger.valueOf(ends[0])),
                ExactRatio.of(BigInteger.valueOf(ends[1])));
    }

    private static NumericDomain.Bounds bounds(long[] ends) {
        return new NumericDomain.Bounds(Endpoint.inclusive(Count.of(ends[0])),
                Endpoint.inclusive(Count.of(ends[1])));
    }
}
