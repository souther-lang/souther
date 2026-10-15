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
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The conditions one reading of a body takes in asking whether some input takes its ways are held
 * to a figure in all, and once it is reached no condition is taken in and no way is asked: a way
 * past it is answered with no proof — kept.
 *
 * <p>Asked of the register a reading keeps, with ways that each consult one comparison of their
 * own, so every one of them is a set of conditions not asked before.
 */
class AReadingOfADecisionTakesInNoMoreConditionsThanItsFigureTest {

    private static final int MOST =
            CompositionBudget.CONDITIONS_A_DECISION_TAKES_IN_TO_PROVE.maximum();

    private static final NoInputTakesIt PROOF = new NoInputTakesIt.TheConditionsClash(
            new NoInputTakesIt.Clash.TwoAtOnce(
                    new Reachability.TwoAtOnce.Counts(TermPath.of("xs"))));

    /** A way consulting the one comparison {@code constant >= 0}, held. */
    private static DecisionRule way(int constant) {
        DecisionCondition.AComparison compared = new DecisionCondition.AComparison(
                LinearForm.constant(ExactRatio.of(constant)), Rel.GE);
        return new DecisionRule(Map.of(compared, new DecidedCondition.Compared(compared, true)));
    }

    @Test
    void asManyConditionsAreTakenInAsTheFigureAndNoMore() {
        WaysNoInputTakes register = new WaysNoInputTakes();
        int taken = 0;
        for (int each = 0; each < MOST + 3; each++) {
            if (register.takesIn()) {
                taken++;
            }
        }

        assertEquals(MOST, taken, "the conditions taken in are as many as the figure");
    }

    @Test
    void noWayIsAskedOnceTheFigureIsReached() {
        WaysNoInputTakes register = new WaysNoInputTakes();
        AtomicInteger asked = new AtomicInteger();
        AtomicInteger taken = new AtomicInteger();

        Optional<NoInputTakesIt> before = register.whyNoInputTakes(way(0), () -> {
            asked.incrementAndGet();
            while (register.takesIn()) {
                taken.incrementAndGet();
            }
            return Optional.of(PROOF);
        });
        Optional<NoInputTakesIt> after = register.whyNoInputTakes(way(1), () -> {
            asked.incrementAndGet();
            return Optional.of(PROOF);
        });

        assertEquals(MOST, taken.get(), "the first way's walk took in what the figure lets");
        assertTrue(before.isPresent(), "a proof had within the figure is a proof");
        assertFalse(after.isPresent(), "a way past the figure is kept");
        assertEquals(1, asked.get(), "the way past the figure is not asked");
    }

    @Test
    void aWayAskedAgainIsAnsweredWithoutAsking() {
        WaysNoInputTakes register = new WaysNoInputTakes();
        AtomicInteger asked = new AtomicInteger();

        for (int round = 0; round < 3; round++) {
            Optional<NoInputTakesIt> answered = register.whyNoInputTakes(way(7), () -> {
                asked.incrementAndGet();
                return Optional.of(PROOF);
            });
            assertTrue(answered.isPresent());
        }

        assertEquals(1, asked.get(), "one way asked three times is asked once");
    }
}
