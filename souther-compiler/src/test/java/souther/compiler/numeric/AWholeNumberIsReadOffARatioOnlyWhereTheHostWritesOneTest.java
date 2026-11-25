package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import java.math.BigInteger;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A ratio read as a whole number: the number where it is one, and nothing where it is none or is
 * one whose digits the host holds no place for.
 *
 * <p>The last of the three is the one a reader building the answer out of {@link ExactRatio#floor}
 * and {@link ExactRatio#isWhole} could get wrong in either direction — taking the floor of a value
 * that is no whole number, or failing on a whole number it cannot write — so it is asked here
 * beside the two plain ones.
 */
class AWholeNumberIsReadOffARatioOnlyWhereTheHostWritesOneTest {

    @Test
    void aWholeNumberIsItself() {
        assertEquals(BigInteger.valueOf(42), ExactRatio.of(42).wholeOrNull());
        assertEquals(BigInteger.valueOf(-7), ExactRatio.of(-7).wholeOrNull());
        assertEquals(BigInteger.ZERO, ExactRatio.ZERO.wholeOrNull());
        assertEquals(BigInteger.valueOf(3000), ExactRatio.of(3).times(ExactRatio.tenTo(3))
                .orNull().wholeOrNull());
    }

    @Test
    void aWholeNumberIsTheOneItsFloorIsWhateverItsSizeAndSign() {
        for (ExactRatio whole : new ExactRatio[] {ExactRatio.tenTo(40),
                ExactRatio.tenTo(40).times(ExactRatio.of(-7)).orNull(),
                ExactRatio.of(Long.MIN_VALUE), ExactRatio.of(Long.MAX_VALUE)}) {
            assertEquals(whole.floor().orNull(), whole.wholeOrNull(), whole::toString);
        }
    }

    @Test
    void aPartOfOneIsNoWholeNumber() {
        assertNull(ExactRatio.of(1).dividedBy(ExactRatio.of(3)).orNull().wholeOrNull());
        assertNull(ExactRatio.tenTo(-1).wholeOrNull());
    }

    @Test
    void aWholeNumberNoHostWritesIsNoneToWorkWith() {
        ExactRatio unwritten = ExactRatio.tenTo(Long.MAX_VALUE);
        assertTrue(unwritten.isWhole(), "ten to the greatest long is a whole number");
        assertNull(unwritten.wholeOrNull());
    }
}
