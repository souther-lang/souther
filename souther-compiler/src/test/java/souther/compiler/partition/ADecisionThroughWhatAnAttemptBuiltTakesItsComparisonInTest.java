package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A rule of the decision that goes through an attempt's {@code then} takes in a comparison written
 * over what the attempt built, as a cut on the position it was built from.
 *
 * <p>The ways through a body are named by a reading of the input that has to be inside the same
 * scope the body is. Named from outside the attempt, {@code q.value} is no position and the
 * comparison on the way to both rules under {@code then} is one the reading declines — so a row
 * composed for either is composed against less than the way asks.
 *
 * <p>The attempt's own arm is declined on every way, the departure's included. Which arm an attempt
 * takes is decided by its invariant, which this reading does not read as anything about the input,
 * and a way that left the arm off would say its region is all there is to it.
 */
class ADecisionThroughWhatAnAttemptBuiltTakesItsComparisonInTest {

    private static final String MODEL = """
            module demo
            data Q = Int
                invariant value >= 0
            data Nope
            data Big
            data Small
            behavior size : (x: Int) -> Big | Small | Nope
                constructs Q
            let size (x) = if Q(x) as q then (if q.value > 10 then Big else Small) else Nope
            """;

    /** Each way under {@code then} takes the comparison in, and what any way declines is the
     *  attempt's arm and nothing else. */
    @Test
    void theComparisonUnderThenIsTakenInOnBothWays() {
        DecisionReading read = DecisionReadings.of(MODEL, "size");

        List<String> onTheWay = read.found().stream()
                .map(ruled -> ruled.states().onTheWay().stream()
                        .map(ADecisionThroughWhatAnAttemptBuiltTakesItsComparisonInTest::said)
                        .toList().toString())
                .sorted()
                .toList();

        assertEquals(List.of(
                "[Declined ForkArmNotReadAsANarrowing, TakenIn]",
                "[Declined ForkArmNotReadAsANarrowing, TakenIn]",
                "[Declined ForkArmNotReadAsANarrowing]"), onTheWay);
    }

    private static String said(OnTheWay each) {
        return each instanceof OnTheWay.Declined declined
                ? "Declined " + declined.why().getClass().getSimpleName()
                : each.getClass().getSimpleName();
    }
}
