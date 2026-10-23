package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Rel;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

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

    @Test
    void aValueHeldOutIsPassedOverForTheNext() {
        WholeNumbersLeft notNought = meeting(WholeNumbersLeft.EVERY, 1, "0", Rel.NE);
        assertEquals(BigInteger.ONE, notNought.one());
        assertEquals(BigInteger.valueOf(-1), meeting(notNought, 1, "-1", Rel.NE).one());
        WholeNumbersLeft fromThree = meeting(WholeNumbersLeft.EVERY, 1, "-3", Rel.GE);
        assertEquals(BigInteger.valueOf(5),
                meeting(meeting(fromThree, 1, "-3", Rel.NE), 1, "-4", Rel.NE).one());
        WholeNumbersLeft upToMinusThree = meeting(WholeNumbersLeft.EVERY, 1, "3", Rel.LE);
        assertEquals(BigInteger.valueOf(-4), meeting(upToMinusThree, 1, "3", Rel.NE).one());
    }

    /** {@code -2n + 5 > 0} is {@code n} below two and a half, so two and below; held away from a
     *  value no whole number is, nothing is held out. */
    @Test
    void aStatementWeighingTheNumberBelowNoughtStandsToItTheOtherWayRound() {
        WholeNumbersLeft below = meeting(WholeNumbersLeft.EVERY, -2, "5", Rel.GT);
        assertEquals(BigInteger.TWO, below.most());
        assertEquals(Set.of(), meeting(below, 2, "-3", Rel.NE).holes());
    }

    /**
     * The one taken is the one nearest nought, the one above it of two as near, so one that is
     * still left after more is taken in is still the one taken. Asked of every run between two
     * ends of minus two to two, or none, with any of minus one to one held out, narrowed by every
     * other such run: an end on either side of nought and at it, and a hole at nought and beside
     * it on each side.
     */
    @Test
    void theOneTakenIsTakenStillWhereverItIsLeft() {
        List<WholeNumbersLeft> every = new ArrayList<>();
        List<BigInteger> ends = new ArrayList<>();
        ends.add(null);
        for (long at = -2; at <= 2; at++) {
            ends.add(BigInteger.valueOf(at));
        }
        for (BigInteger least : ends) {
            for (BigInteger most : ends) {
                for (int held = 0; held < 1 << 3; held++) {
                    Set<BigInteger> holes = new HashSet<>();
                    for (int bit = 0; bit < 3; bit++) {
                        if ((held & 1 << bit) != 0) {
                            holes.add(BigInteger.valueOf(bit - 1));
                        }
                    }
                    every.add(new WholeNumbersLeft(least, most, holes));
                }
            }
        }
        for (WholeNumbersLeft some : every) {
            BigInteger taken = some.one();
            if (taken != null) {
                assertTrue(holds(some, taken), some::toString);
                assertTrue(every.stream().filter(fewer -> holds(fewer, taken))
                        .noneMatch(fewer -> !taken.equals(narrowed(some, fewer).one())),
                        some::toString);
            }
            assertEquals(nearestNought(some), taken, some::toString);
        }
    }

    /** Whether {@code value} is one of {@code left}. */
    private static boolean holds(WholeNumbersLeft left, BigInteger value) {
        return (left.least() == null || value.compareTo(left.least()) >= 0)
                && (left.most() == null || value.compareTo(left.most()) <= 0)
                && !left.holes().contains(value);
    }

    /** The numbers both of {@code one} and of {@code other}. */
    private static WholeNumbersLeft narrowed(WholeNumbersLeft one, WholeNumbersLeft other) {
        BigInteger least = one.least() == null ? other.least()
                : other.least() == null ? one.least() : one.least().max(other.least());
        BigInteger most = one.most() == null ? other.most()
                : other.most() == null ? one.most() : one.most().min(other.most());
        Set<BigInteger> holes = new HashSet<>(one.holes());
        holes.addAll(other.holes());
        return new WholeNumbersLeft(least, most, holes);
    }

    /** The one of {@code left} nearest nought, the one above it of two as near, looked for among
     *  the numbers from minus ten to ten. */
    private static BigInteger nearestNought(WholeNumbersLeft left) {
        for (long away = 0; away <= 10; away++) {
            for (BigInteger value : List.of(BigInteger.valueOf(away), BigInteger.valueOf(-away))) {
                if (holds(left, value)) {
                    return value;
                }
            }
        }
        return null;
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
