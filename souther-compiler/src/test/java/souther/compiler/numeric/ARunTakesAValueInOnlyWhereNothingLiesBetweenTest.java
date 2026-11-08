package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A run takes a value in ({@link NumericDomain.Bounds#joining}) where the two are one run, on
 * either side of it, and stays as it was where a value lies between them.
 *
 * <p>Held against the values themselves. Over every run of whole numbers between small ends, each
 * end held or left out, and every value near them, the whole numbers the run answered holds are
 * the run's and the value's where those leave no whole number out between their least and
 * greatest, and the run's alone otherwise. Over dense values, nothing is next to a held end, so
 * only an end left out at the value takes it in.
 */
class ARunTakesAValueInOnlyWhereNothingLiesBetweenTest {

    private static final long FAR = 6;

    @Test
    void aRunOfWholeNumbersTakesAValueInWhereNoWholeNumberLiesBetween() {
        List<String> wrong = new ArrayList<>();
        for (long least = -3; least <= 3; least++) {
            for (long most = least; most <= 3; most++) {
                for (boolean lowHeld : new boolean[] {true, false}) {
                    for (boolean highHeld : new boolean[] {true, false}) {
                        NumericDomain.Bounds run = run(least, lowHeld, most, highHeld);
                        Set<Long> holds = wholeNumbersOf(run);
                        if (holds.isEmpty()) {
                            continue;
                        }
                        for (long value = -5; value <= 5; value++) {
                            Set<Long> both = new TreeSet<>(holds);
                            both.add(value);
                            Set<Long> expected = noneMissing(both) ? both : holds;
                            Set<Long> answered = wholeNumbersOf(
                                    run.joining(Count.of(value), Granularity.DISCRETE));
                            if (!expected.equals(answered)) {
                                wrong.add(run + " with " + value + ": " + answered + ", by its"
                                        + " values " + expected);
                            }
                        }
                    }
                }
            }
        }
        assertEquals(List.of(), wrong);
    }

    /** Runs with no end on a side take a value next to their other end in as well. */
    @Test
    void aRunWithNoEndOnASideTakesAValueNextToItsOtherEnd() {
        NumericDomain.Bounds fromOne = new NumericDomain.Bounds(
                Endpoint.inclusive(Count.of(1)), null);
        assertEquals(new NumericDomain.Bounds(Endpoint.inclusive(Count.ZERO), null),
                fromOne.joining(Count.ZERO, Granularity.DISCRETE));
        NumericDomain.Bounds toMinusOne = new NumericDomain.Bounds(null,
                Endpoint.inclusive(Count.of(-1)));
        assertEquals(new NumericDomain.Bounds(null, Endpoint.inclusive(Count.ZERO)),
                toMinusOne.joining(Count.ZERO, Granularity.DISCRETE));
        NumericDomain.Bounds toMinusTwo = new NumericDomain.Bounds(null,
                Endpoint.inclusive(Count.of(-2)));
        assertEquals(toMinusTwo, toMinusTwo.joining(Count.ZERO, Granularity.DISCRETE));
    }

    @Test
    void aRunOfDenseValuesTakesInOnlyAValueAnEndLeavesOut() {
        NumericDomain.Bounds belowNought = new NumericDomain.Bounds(null,
                Endpoint.exclusive(Count.ZERO));
        assertEquals(new NumericDomain.Bounds(null, Endpoint.inclusive(Count.ZERO)),
                belowNought.joining(Count.ZERO, Granularity.DENSE));
        NumericDomain.Bounds aboveNought = new NumericDomain.Bounds(
                Endpoint.exclusive(Count.ZERO), null);
        assertEquals(new NumericDomain.Bounds(Endpoint.inclusive(Count.ZERO), null),
                aboveNought.joining(Count.ZERO, Granularity.DENSE));
        NumericDomain.Bounds fromOne = new NumericDomain.Bounds(
                Endpoint.inclusive(Count.of(1)), null);
        assertEquals(fromOne, fromOne.joining(Count.ZERO, Granularity.DENSE));
        NumericDomain.Bounds toMinusOne = new NumericDomain.Bounds(null,
                Endpoint.inclusive(Count.of(-1)));
        assertEquals(toMinusOne, toMinusOne.joining(Count.ZERO, Granularity.DENSE));
    }

    private static NumericDomain.Bounds run(long least, boolean lowHeld, long most,
                                            boolean highHeld) {
        return new NumericDomain.Bounds(
                lowHeld ? Endpoint.inclusive(Count.of(least)) : Endpoint.exclusive(Count.of(least)),
                highHeld ? Endpoint.inclusive(Count.of(most)) : Endpoint.exclusive(Count.of(most)));
    }

    /** The whole numbers {@code run} holds, asked of it one at a time near its ends. */
    private static Set<Long> wholeNumbersOf(NumericDomain.Bounds run) {
        Set<Long> out = new TreeSet<>();
        for (long each = -FAR; each <= FAR; each++) {
            if (run.admits(ExactRatio.of(each))) {
                out.add(each);
            }
        }
        return out;
    }

    private static boolean noneMissing(Set<Long> values) {
        TreeSet<Long> sorted = new TreeSet<>(values);
        return sorted.last() - sorted.first() + 1 == sorted.size();
    }
}
