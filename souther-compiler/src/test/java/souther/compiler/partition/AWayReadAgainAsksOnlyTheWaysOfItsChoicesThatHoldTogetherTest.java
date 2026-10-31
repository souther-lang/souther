package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.Rel;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static souther.compiler.partition.WaysReadAgain.oneOf;
import static souther.compiler.partition.WaysReadAgain.truth;
import static souther.compiler.partition.WaysReadAgain.x;

/**
 * A way read again for a relation on {@code x} and {@code y} asks the ways of taking its choices
 * together that may hold together, and reads a choice as less only where every value of the
 * numbers a way of them leaves is one a row past them takes.
 */
class AWayReadAgainAsksOnlyTheWaysOfItsChoicesThatHoldTogetherTest {

    /** The lines both choices part {@code x} by, whose runs squared are more ways than a way is
     *  looked along with. */
    private static final int LINES = 4;

    /** A number the relation reads, bounded {@code rel threshold}. */
    private interface Bound {
        OnTheWay of(long weight, Rel rel, long threshold);
    }

    /**
     * A choice parting a number at each of {@link #LINES}, asking apart of each run that the truth
     * numbered as the run holds and the next does not, which every choice made here asks of
     * alike. No value meets what every run asks at once, so the ways of taking the choices
     * together are asked one by one.
     */
    private static OnTheWay parting(int at, Bound number) {
        List<List<OnTheWay>> runs = new ArrayList<>();
        for (int run = 0; run <= LINES; run++) {
            List<OnTheWay> asked = new ArrayList<>();
            if (run > 0) {
                asked.add(number.of(1, Rel.GE, run * 10L));
            }
            if (run < LINES) {
                asked.add(number.of(1, Rel.LT, (run + 1) * 10L));
            }
            asked.add(truth("c" + run, true));
            asked.add(truth("c" + (run + 1), false));
            runs.add(asked);
        }
        return oneOf(at, runs);
    }

    /**
     * Two choices parting {@code x} by the same lines take their runs together only where they
     * agree, so the ways of them are as many as the runs and not their square, and each is met.
     */
    @Test
    void choicesPartingOneNumberByTheSameLinesAreAskedAlongTheRunsTheyAgreeOn() {
        AWayReadForARelation.ReadAgain again = WaysReadAgain.readAgain(
                List.of(parting(1, WaysReadAgain::x), parting(2, WaysReadAgain::x)));

        assertFalse(again.stoppedAt().contains(CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG),
                () -> "the ways were not more than a way is looked along with: "
                        + again.stoppedAt());
        assertTrue(again.as().isPresent(), "and the way is read as less for the relation");
    }

    /** Control: parting {@code x} and {@code y}, every run of one holds with every run of the
     *  other, and the ways are the product, past what a way is looked along with. */
    @Test
    void choicesPartingTwoNumbersAreAskedAlongTheProductOfTheirRuns() {
        AWayReadForARelation.ReadAgain again = WaysReadAgain.readAgain(
                List.of(parting(1, WaysReadAgain::x), parting(2, WaysReadAgain::y)));

        assertTrue(again.as().isEmpty(), () -> "nothing is read as less: " + again.as());
        assertTrue(again.stoppedAt().contains(CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG),
                () -> "stopped at the ways a way is looked along with: " + again.stoppedAt());
    }

    /**
     * Under {@code (x <= 0 && t || x >= 10 && !t)} and {@code (x <= 3 && !t || x >= 7 && t)} no
     * row takes both, and the ways of them {@code x} reaches ask {@code t} both ways. Read as
     * less, the two would leave {@code x} at or below nought and at or above ten, which no row
     * holds: no way met holds those values, so neither is read as less.
     */
    @Test
    void aWayNoValueMeetsApartIsNotReadAsLessWhereNoWayMetHoldsItsValues() {
        AWayReadForARelation.ReadAgain again = WaysReadAgain.readAgain(List.of(
                oneOf(1, List.of(List.of(x(1, Rel.LE, 0), truth("t", true)),
                        List.of(x(1, Rel.GE, 10), truth("t", false)))),
                oneOf(2, List.of(List.of(x(1, Rel.LE, 3), truth("t", false)),
                        List.of(x(1, Rel.GE, 7), truth("t", true))))));

        assertTrue(again.as().isEmpty(), () -> "nothing is read as less: " + again.as());
    }

    /**
     * Under {@code (x >= 10 && t || x < 10 && u)} and
     * {@code (2 * x >= 20 && !t || 3 * x >= 30 && v || x < 10 && u)}, no value is {@code t} and
     * not, but every {@code x} at or above ten that way leaves is one a row takes with {@code v}
     * — the same bound written another way, which is the one form it is on.
     */
    @Test
    void aWayNoValueMeetsApartIsReadWhereAWayMetHoldsTheSameValuesWrittenAnotherWay() {
        AWayReadForARelation.ReadAgain again = WaysReadAgain.readAgain(List.of(
                oneOf(1, List.of(List.of(x(1, Rel.GE, 10), truth("t", true)),
                        List.of(x(1, Rel.LT, 10), truth("u", true)))),
                oneOf(2, List.of(List.of(x(2, Rel.GE, 20), truth("t", false)),
                        List.of(x(3, Rel.GE, 30), truth("v", true)),
                        List.of(x(1, Rel.LT, 10), truth("u", true))))));

        assertTrue(again.as().isPresent(), () -> "read as less: " + again.stoppedAt());
    }

    /**
     * A choice whose alternatives between them leave {@code x} every value comes to nothing for
     * the relation and is left off the way read again; one leaving the values between nought
     * and ten out stays on it, and nothing is read as less.
     */
    @Test
    void aChoiceIsLeftOffOnlyWhereItsAlternativesLeaveEveryValue() {
        AWayReadForARelation.ReadAgain every = WaysReadAgain.readAgain(List.of(
                oneOf(1, List.of(List.of(x(1, Rel.LE, 0)), List.of(x(1, Rel.GT, 0))))));
        AWayReadForARelation.ReadAgain apart = WaysReadAgain.readAgain(List.of(
                oneOf(1, List.of(List.of(x(1, Rel.LE, 0)), List.of(x(1, Rel.GE, 10))))));

        assertTrue(every.as().orElse(null) instanceof Reachability.Reaching reaching
                        && reaching.ways() instanceof Reachability.Ways.One,
                () -> "left off, the way is not split: " + every.as());
        assertEquals(Optional.empty(), apart.as(), "kept, it is read as it is");
    }
}
