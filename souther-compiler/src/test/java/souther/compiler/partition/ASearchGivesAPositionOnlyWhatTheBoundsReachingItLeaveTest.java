package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LaterNumbersEliminated;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.NumericDomain;

import java.math.BigInteger;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a boundary search takes from eliminating the bounds a region took in
 * ({@link LevelRealizer#reaching}, {@link LevelRealizer#levelsOf}, {@link LevelRealizer#endAt}):
 * only the bounds that reach its positions, a proof of nothing left only where no rational values
 * are, and ends that keep every value a bound leaves and no whole value it does not.
 */
class ASearchGivesAPositionOnlyWhatTheBoundsReachingItLeaveTest {

    /** {@code x + y <= 0} and the like: one weight per number, and the constant. */
    private static LaterNumbersEliminated.Bound<String> bound(long constant,
                                                             Map<String, Long> weights) {
        Map<String, ExactRatio> coefs = new LinkedHashMap<>();
        weights.forEach((number, weight) -> coefs.put(number, ExactRatio.of(weight)));
        return new LaterNumbersEliminated.Bound<>(
                new LinearForm<>(ExactRatio.of(constant), coefs), false);
    }

    private static ExactRatio half() {
        return ExactRatio.of(BigInteger.ONE, BigInteger.TWO);
    }

    private static ExactRatio third() {
        return ExactRatio.of(BigInteger.ONE, BigInteger.valueOf(3));
    }

    @Test
    void aBoundIsEliminatedOnlyWhereItReachesThePositions() {
        LaterNumbersEliminated.Bound<String> onY = bound(0, Map.of("y", 1L, "z", -1L));
        LaterNumbersEliminated.Bound<String> onX = bound(0, Map.of("x", 1L, "y", 1L));
        LaterNumbersEliminated.Bound<String> apart = bound(4, Map.of("u", 1L, "v", 1L));
        // y - z is listed before the bound that reaches y from x, and is reached all the same
        assertEquals(List.of(onY, onX), LevelRealizer.reaching(List.of("x"), List.of(onY, apart,
                onX)));
    }

    @Test
    void onlyNoRationalValuesIsAProofThatNothingIsLeft() {
        assertNull(LevelRealizer.levelsOf(new LaterNumbersEliminated.NoneLeft<String>(0)));
        LaterNumbersEliminated.Bound<String> onZ = bound(0, Map.of("z", 1L));
        List<List<LaterNumbersEliminated.Bound<String>>> stopped = LevelRealizer.levelsOf(
                new LaterNumbersEliminated.StoppedShort<>(2, List.of(List.of(onZ)),
                        LaterNumbersEliminated.Why.PAIRS, 0));
        assertNotNull(stopped, "an elimination stopped short proves nothing is left of nothing");
        assertEquals(List.of(List.of(), List.of(), List.of(onZ)), stopped);
    }

    @Test
    void aWholePositionStopsAtTheLastWholeValueABoundLeaves() {
        ExactRatio five = ExactRatio.of(5);
        assertEquals(5, at(LevelRealizer.endAt(five, false, true, true)));
        assertEquals(4, at(LevelRealizer.endAt(five, true, true, true)));
        assertEquals(-5, at(LevelRealizer.endAt(five.negated(), false, false, true)));
        assertEquals(-4, at(LevelRealizer.endAt(five.negated(), true, false, true)));
        assertEquals(0, at(LevelRealizer.endAt(ExactRatio.ZERO, false, false, true)));
        assertEquals(1, at(LevelRealizer.endAt(ExactRatio.ZERO, true, false, true)));
        // a half between two whole values leaves the one either side, strict or not
        assertEquals(0, at(LevelRealizer.endAt(half(), true, true, true)));
        assertEquals(-1, at(LevelRealizer.endAt(half().negated(), false, true, true)));
    }

    /** {@code x + y == 1} and {@code x == y} leave x at a half, which no whole value is. */
    @Test
    void aRationalValueIsNoWholeOne() {
        NumericDomain.Bounds x = new NumericDomain.Bounds(
                LevelRealizer.endAt(half(), false, false, true),
                LevelRealizer.endAt(half(), false, true, true));
        assertFalse(x.holdsAValue());
    }

    /** A third has no decimal: the end is written past it, and holds every value below it. */
    @Test
    void aDecimalPositionKeepsEveryValueABoundLeaves() {
        Endpoint below = LevelRealizer.endAt(third(), true, true, false);
        assertNotNull(below);
        assertTrue(exactly(below).compareTo(third()) >= 0 && below.inclusive());
        Endpoint over = LevelRealizer.endAt(third(), true, false, false);
        assertNotNull(over);
        assertTrue(exactly(over).compareTo(third()) <= 0 && over.inclusive());
        // and a decimal that is the end is the end, left out where the bound is strict
        Endpoint atHalf = LevelRealizer.endAt(half(), true, true, false);
        assertEquals(0, exactly(atHalf).compareTo(half()));
        assertFalse(atHalf.inclusive());
    }

    private static ExactRatio exactly(Endpoint end) {
        return ((Count) end.at()).exactly();
    }

    private static long at(Endpoint end) {
        return ((Count) end.at()).at().longValueExact();
    }
}
