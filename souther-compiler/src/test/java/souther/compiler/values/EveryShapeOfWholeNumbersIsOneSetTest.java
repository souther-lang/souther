package souther.compiler.values;

import org.junit.jupiter.api.Test;

import net.unit8.notation199x.pattern.Meter;
import souther.compiler.numeric.Congruences;
import souther.compiler.numeric.WholeNumberRuns;
import souther.compiler.numeric.WholeNumberSet;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Whole numbers held as runs, as progressions, as written out, and as what is left out, are one
 * set each, and every pair of them meets and joins as the numbers they hold do.
 *
 * <p>Asked over a sample of numbers and of what is no number, against what each side says of each,
 * which is what a shape added is held to ({@link EveryPairOfShapesIsOneSetTest}).
 */
class EveryShapeOfWholeNumbersIsOneSetTest {

    private static final Meter ROOM = new Meter(1000, 100_000, 10_000_000L);

    private static BigInteger n(long value) {
        return BigInteger.valueOf(value);
    }

    private static Value number(long value) {
        return Value.number(new BigDecimal(value));
    }

    private static WholeNumberSet evens() {
        return WholeNumberSet.ofClass(new Congruences(BigInteger.ZERO, n(2)));
    }

    private static WholeNumberSet from(long least) {
        return WholeNumberSet.ofRuns(WholeNumberRuns.one(n(least), null));
    }

    /** One of each shape, and more than one of the numbers'. */
    private static List<ValueSet> shapes() {
        return List.of(
                ValueSet.NONE,
                ValueSet.ANY,
                ValueSet.oneOf(Set.of(number(2), number(7))),
                ValueSet.allBut(number(4)),
                ValueSet.wholeNumbers(WholeNumberRuns.one(n(-3), n(5))),
                ValueSet.wholeNumbers(WholeNumberRuns.one(n(6), null)),
                ValueSet.wholeNumberSet(evens()),
                ValueSet.wholeNumberSet(evens().and(from(0))),
                ValueSet.wholeNumberSet(WholeNumberSet.ofClass(new Congruences(BigInteger.ONE,
                        n(3)))),
                ValueSet.wholeNumberSet(evens().and(WholeNumberSet.ofRuns(
                        WholeNumberRuns.one(n(-6), n(6))))));
    }

    private static final List<Value> SAMPLE = sample();

    private static List<Value> sample() {
        List<Value> out = new ArrayList<>();
        for (long at = -12; at <= 12; at++) {
            out.add(number(at));
        }
        out.add(Value.text("a"));
        out.add(Value.number(new BigDecimal("2.5")));
        return out;
    }

    @Test
    void aMeetHoldsWhatBothHold() {
        List<String> apart = new ArrayList<>();
        for (ValueSet one : shapes()) {
            for (ValueSet two : shapes()) {
                ValueSet met = Sets.metUnder(one, two, ROOM);
                assertNotNull(met, one + " meet " + two);
                for (Value each : SAMPLE) {
                    if (met.has(each) != (one.has(each) && two.has(each))) {
                        apart.add(one + " meet " + two + " at " + each);
                    }
                }
            }
        }
        assertEquals(List.of(), apart);
    }

    @Test
    void aJoinHoldsWhatEitherHolds() {
        List<String> apart = new ArrayList<>();
        for (ValueSet one : shapes()) {
            for (ValueSet two : shapes()) {
                ValueSet joined = Sets.joinedUnder(one, two, ROOM);
                assertNotNull(joined, one + " join " + two);
                for (Value each : SAMPLE) {
                    if (joined.has(each) != (one.has(each) || two.has(each))) {
                        apart.add(one + " join " + two + " at " + each);
                    }
                }
            }
        }
        assertEquals(List.of(), apart);
    }

    /** What is held in the type is the meet with the type's numbers, the ends of Int included. */
    @Test
    void theEndsOfIntAreMembersOfWhatTheTypeHolds() {
        ValueSet type = ValueSet.wholeNumbers(WholeNumberRuns.one(n(Integer.MIN_VALUE),
                n(Integer.MAX_VALUE)));
        ValueSet inType = Sets.metUnder(ValueSet.wholeNumberSet(evens()), type, ROOM);
        assertTrue(inType.has(number(Integer.MIN_VALUE)));
        assertFalse(inType.has(number(Integer.MAX_VALUE)));
        assertTrue(inType.has(number(Integer.MAX_VALUE - 1L)));
        assertFalse(inType.has(number(Integer.MIN_VALUE - 2L)));
        ValueSet past = ValueSet.wholeNumbers(WholeNumberRuns.one(
                n(Integer.MAX_VALUE).add(BigInteger.ONE), null));
        assertTrue(Sets.metUnder(ValueSet.wholeNumberSet(evens()), past, ROOM).has(
                number(Integer.MAX_VALUE + 1L)));
        assertTrue(Sets.metUnder(past, type, ROOM).isEmpty());
    }

    /** The two of evens and odds share nothing, and the sets say so without listing a number. */
    @Test
    void evensAndOddsShareNothing() {
        ValueSet odds = ValueSet.wholeNumberSet(WholeNumberSet.ofClass(new Congruences(
                BigInteger.ONE, n(2))));
        assertTrue(Sets.metUnder(ValueSet.wholeNumberSet(evens()), odds, ROOM).isEmpty());
        // Asked with nothing to spend, they are not shown to share nothing.
        assertTrue(ValueSet.wholeNumberSet(evens()).sharesAnythingWith(odds));
    }

    /** A meet a meter will not pay for is not built, and no smaller set stands for it. */
    @Test
    void aMeetTheMeterRefusesIsNullAndNotShortened() {
        ValueSet steps = ValueSet.wholeNumberSet(evens());
        assertNull(Sets.metUnder(steps, steps, Meter.refusing()));
        assertNull(Sets.joinedUnder(steps, ValueSet.wholeNumbers(WholeNumberRuns.one(n(0), n(9))),
                Meter.refusing()));
    }

    /** Two ways of writing one set of numbers hold the same values, and a set of one shape does
     *  not pass for the other. */
    @Test
    void progressionsThatAreRunsAreRuns() {
        assertInstanceOf(ValueSet.WholeRuns.class, ValueSet.wholeNumberSet(
                WholeNumberSet.ofRuns(WholeNumberRuns.one(n(0), n(9)))));
        assertInstanceOf(ValueSet.WholeSteps.class, ValueSet.wholeNumberSet(evens()));
        assertThrows(IllegalArgumentException.class,
                () -> new ValueSet.WholeSteps(WholeNumberSet.ofRuns(WholeNumberRuns.one(n(0),
                        n(9)))));
        ValueSet fours = ValueSet.wholeNumberSet(WholeNumberSet.ofClass(new Congruences(
                BigInteger.ZERO, n(4))));
        ValueSet evensAndFours = Sets.joinedUnder(ValueSet.wholeNumberSet(evens()), fours, ROOM);
        assertTrue(evensAndFours.holdsTheSameValuesAs(ValueSet.wholeNumberSet(evens())));
        assertFalse(fours.holdsTheSameValuesAs(ValueSet.wholeNumberSet(evens())));
    }
}
