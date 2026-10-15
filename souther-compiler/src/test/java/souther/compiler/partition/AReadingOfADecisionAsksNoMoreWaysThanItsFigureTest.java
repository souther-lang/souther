package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;

import java.util.Map;
import java.util.Optional;
import java.util.concurrent.atomic.AtomicInteger;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The ways one reading of a body asks whether some input takes are held to a figure in all, and a
 * way past it is answered with no proof — kept — rather than asked.
 *
 * <p>Asked of the register a reading keeps, with ways that each consult one comparison of their
 * own: every one of them is a set of conditions not asked before, which is what the figure counts.
 */
class AReadingOfADecisionAsksNoMoreWaysThanItsFigureTest {

    private static final int MOST = CompositionBudget.WAYS_A_DECISION_ASKS_AN_INPUT_TAKES.maximum();

    /** A way consulting the one comparison {@code constant >= 0}, held. */
    private static DecisionRule way(int constant) {
        DecisionCondition.AComparison compared = new DecisionCondition.AComparison(
                LinearForm.constant(ExactRatio.of(constant)), Rel.GE);
        return new DecisionRule(Map.of(compared, new DecidedCondition.Compared(compared, true)));
    }

    @Test
    void noWayPastTheFigureIsAskedAndNoneIsProvedThere() {
        WaysNoInputTakes register = new WaysNoInputTakes();
        AtomicInteger asked = new AtomicInteger();
        NoInputTakesIt proof = new NoInputTakesIt.TheConditionsClash(
                new NoInputTakesIt.Clash.TwoAtOnce(
                        new Reachability.TwoAtOnce.Counts(TermPath.of("xs"))));

        for (int each = 0; each < MOST + 3; each++) {
            Optional<NoInputTakesIt> answered = register.whyNoInputTakes(way(each), () -> {
                asked.incrementAndGet();
                return Optional.of(proof);
            });
            assertEquals(each < MOST, answered.isPresent(),
                    "way " + each + " is proved only within the figure");
        }

        assertEquals(MOST, asked.get(), "the ways asked are as many as the figure and no more");
    }

    @Test
    void aWayAskedAgainIsAnsweredWithoutAskingAndCountsOnce() {
        WaysNoInputTakes register = new WaysNoInputTakes();
        AtomicInteger asked = new AtomicInteger();

        for (int round = 0; round < 3; round++) {
            Optional<NoInputTakesIt> answered = register.whyNoInputTakes(way(7), () -> {
                asked.incrementAndGet();
                return Optional.empty();
            });
            assertTrue(answered.isEmpty());
        }
        for (int each = 0; each < MOST - 1; each++) {
            register.whyNoInputTakes(way(1000 + each), () -> {
                asked.incrementAndGet();
                return Optional.empty();
            });
        }

        assertEquals(MOST, asked.get(),
                "one way asked three times is one of the ways the figure counts");
    }
}
