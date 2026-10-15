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
 * <p>The attempt's own arm is taken in on every way, the departure's included: which arm an attempt
 * takes is decided by its invariant, read over what it is handed, so the success is {@code x >= 0}
 * and the departure {@code x < 0}.
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

    /** Each way under {@code then} takes the comparison in beside the attempt's arm, and nothing on
     *  any way is declined. */
    @Test
    void theComparisonUnderThenIsTakenInOnBothWays() {
        DecisionReading read = DecisionReadings.of(MODEL, "size");

        List<String> onTheWay = read.found().stream()
                .map(ruled -> ruled.states().onTheWay().stream()
                        .map(ADecisionThroughWhatAnAttemptBuiltTakesItsComparisonInTest::said)
                        .toList().toString())
                .sorted()
                .toList();

        assertEquals(List.of("[TakenIn, TakenIn]", "[TakenIn, TakenIn]", "[TakenIn]"), onTheWay);
    }

    private static String said(OnTheWay each) {
        return each instanceof OnTheWay.Declined declined
                ? "Declined " + declined.whys()
                : each.getClass().getSimpleName();
    }
}
