package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Rel;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.List;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;

/**
 * The whole numbers a number may be are those its statements leave, holes and all, and the one
 * taken of them is one of those wherever one is.
 */
class AWholeNumberLeftIsOneNoStatementHoldsOutTest {

    /** {@code weight·n + constant rel 0}. */
    private static WholeNumbersLeft meeting(WholeNumbersLeft left, long weight, String constant,
                                            Rel rel) {
        return left.meeting(ExactRatio.of(weight), ExactRatio.of(new BigDecimal(constant)), rel);
    }

    /** Between the ends and not held out. */
    @Test
    void aValueIsLeftBetweenTheEndsAndNotHeldOut() {
        WholeNumbersLeft left = meeting(meeting(meeting(WholeNumbersLeft.EVERY, 1, "3", Rel.GE),
                1, "-2", Rel.LE), 1, "-1", Rel.NE);
        assertEquals(List.of(false, true, false, true, false), Stream.of(-4, -3, 1, 2, 3)
                .map(at -> left.leaves(BigInteger.valueOf(at))).toList());
    }

    @Test
    void aValueHeldOutIsPassedOverForTheNext() {
        WholeNumbersLeft notNought = meeting(WholeNumbersLeft.EVERY, 1, "0", Rel.NE);
        assertEquals(BigInteger.ONE, notNought.one());
        assertEquals(BigInteger.valueOf(-1), meeting(notNought, 1, "-1", Rel.NE).one());
        WholeNumbersLeft fromThree = meeting(WholeNumbersLeft.EVERY, 1, "-3", Rel.GE);
        assertEquals(BigInteger.valueOf(5),
                meeting(meeting(fromThree, 1, "-3", Rel.NE), 1, "-4", Rel.NE).one());
        WholeNumbersLeft upToThree = meeting(WholeNumbersLeft.EVERY, 1, "-3", Rel.LE);
        assertEquals(BigInteger.TWO, meeting(upToThree, 1, "-3", Rel.NE).one());
    }

    /** {@code -2n + 5 > 0} is {@code n} below two and a half, so two and below; held away from a
     *  value no whole number is, nothing is held out. */
    @Test
    void aStatementWeighingTheNumberBelowNoughtStandsToItTheOtherWayRound() {
        WholeNumbersLeft below = meeting(WholeNumbersLeft.EVERY, -2, "5", Rel.GT);
        assertEquals(BigInteger.TWO, below.most());
        assertEquals(BigInteger.TWO, meeting(below, 2, "-3", Rel.NE).one());
    }

    @Test
    void noneIsLeftWhereTheStatementsLeaveNoWholeNumber() {
        assertNull(meeting(WholeNumbersLeft.EVERY, 2, "-1", Rel.EQ).one(),
                "no whole number is a half");
        WholeNumbersLeft noughtToOne = meeting(meeting(WholeNumbersLeft.EVERY, 1, "0", Rel.GE),
                1, "-1", Rel.LE);
        assertNull(meeting(meeting(noughtToOne, 1, "0", Rel.NE), 1, "-1", Rel.NE).one());
        WholeNumbersLeft strictlyBetween = WholeNumbersLeft.of(new NumericDomain.Bounds(
                Endpoint.exclusive(Count.ZERO), Endpoint.exclusive(Count.of(BigDecimal.ONE))));
        assertNull(strictlyBetween.one(), "nothing whole is above nought and below one");
    }
}
