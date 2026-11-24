package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.function.IntFunction;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A fork on a condition of more ways than a decision is read for is not read to the end.
 *
 * <p>The ways into an arm are the ways the condition comes out that way, so where the condition has
 * more of them than the reading holds, the fork does too. Answered with the arm as its one way in,
 * the fork had two rules that were each written down whole, and the reading said every way of the
 * body was — over a condition whose ways it had stopped counting.
 *
 * <p>Asked of the condition written in the fork, and of one taken off a record it was written into,
 * which reaches the fork through the name the record is bound to: neither may leave the count
 * behind. The control is the same fork on a condition of one forked part.
 */
class AForkOnAConditionOfMoreWaysThanAreReadIsNotReadToTheEndTest {

    /** Forked parts enough that their ways are more than a decision is read for. */
    private static final int FORKED = 13;

    @Test
    void noWayForTheConditionToReachTheForkLeavesTheCountBehind() {
        String sum = IntStream.range(0, FORKED)
                .mapToObj(i -> "(if p" + i + " > 0 then 1 else 2)")
                .collect(Collectors.joining(" + "));
        String params = each(i -> "p" + i + ": Int");
        String names = each(i -> "p" + i);
        String source = """
                module wide

                data Done
                data Fresh
                data Seen = { hit: Bool, at: Int }

                behavior written : (%1$s) -> Done | Fresh
                let written (%2$s) = if %3$s > 20 then Done else Fresh

                behavior takenOff : (%1$s) -> Done | Fresh
                    constructs Seen
                let takenOff (%2$s) = {
                    let s = Seen { hit = %3$s > 20, at = 0 }
                    if s.hit then Done else Fresh
                }

                behavior fewer : (%1$s) -> Done | Fresh
                let fewer (%2$s) = if (if p0 > 0 then 1 else 2) > 1 then Done else Fresh
                """.formatted(params, names, sum);
        DecisionReadings.Compiled compiled = DecisionReadings.compiled(source);
        DecisionReading.Enumeration stopped = new DecisionReading.Enumeration.StoppedAtAFigure(
                CompositionBudget.PATHS_OF_A_DECISION_READ);
        for (String behavior : List.of("written", "takenOff")) {
            assertEquals(stopped, compiled.of(behavior).enumeration(), behavior);
        }
        assertEquals(new DecisionReading.Enumeration.Complete(),
                compiled.of("fewer").enumeration(), "the control is read to the end");
    }

    private static String each(IntFunction<String> one) {
        return IntStream.range(0, FORKED).mapToObj(one).collect(Collectors.joining(", "));
    }
}
