package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;

import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.concurrent.atomic.AtomicInteger;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * The conditions one reading of a body takes in asking whether some input takes its ways are held
 * to a figure in all, and once it is reached no condition is taken in and no way is asked: a way
 * past it is answered with no proof — kept — and said to have stopped at the figure.
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

    /** A way consulting the one comparison {@code constant >= 0}, held, through no construction. */
    private static DecisionPath.Way way(int constant) {
        DecisionCondition.AComparison compared = new DecisionCondition.AComparison(
                LinearForm.constant(ExactRatio.of(constant)), Rel.GE);
        return new DecisionPath.Way(new DecisionRule(Map.of(compared,
                new DecidedCondition.Compared(compared, true))), Set.of());
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

        WaysNoInputTakes.Asked before = register.whyNoInputTakes(way(0), () -> {
            asked.incrementAndGet();
            while (register.takesIn()) {
                taken.incrementAndGet();
            }
            return Optional.of(PROOF);
        });
        WaysNoInputTakes.Asked after = register.whyNoInputTakes(way(1), () -> {
            asked.incrementAndGet();
            return Optional.of(PROOF);
        });

        assertEquals(MOST, taken.get(), "the first way's walk took in what the figure lets");
        assertEquals(new WaysNoInputTakes.Asked.Proved(PROOF), before,
                "a proof had within the figure is a proof, though the walk was told no once");
        assertEquals(new WaysNoInputTakes.Asked.StoppedAt(
                CompositionBudget.CONDITIONS_A_DECISION_TAKES_IN_TO_PROVE.reached()), after,
                "a way past the figure is kept, and said to have stopped at it");
        assertEquals(1, asked.get(), "the way past the figure is not asked");
    }

    /** A walk told no to a condition and coming back with no proof has not shown that some input
     *  takes the way: it stopped at the figure. One told no to nothing has. */
    @Test
    void aWalkToldNoAndProvingNothingStoppedAtTheFigure() {
        WaysNoInputTakes register = new WaysNoInputTakes();

        WaysNoInputTakes.Asked whole = register.whyNoInputTakes(way(0), Optional::empty);
        AtomicInteger taken = new AtomicInteger();
        WaysNoInputTakes.Asked cut = register.whyNoInputTakes(way(1), () -> {
            while (register.takesIn()) {
                taken.incrementAndGet();
            }
            return Optional.empty();
        });

        assertEquals(MOST, taken.get(), "the walk took in what the figure lets, and was told no");
        assertEquals(new WaysNoInputTakes.Asked.NotProved(), whole);
        assertEquals(new WaysNoInputTakes.Asked.StoppedAt(
                CompositionBudget.CONDITIONS_A_DECISION_TAKES_IN_TO_PROVE.reached()), cut);
    }

    @Test
    void aWayAskedAgainIsAnsweredWithoutAsking() {
        WaysNoInputTakes register = new WaysNoInputTakes();
        AtomicInteger asked = new AtomicInteger();

        for (int round = 0; round < 3; round++) {
            WaysNoInputTakes.Asked answered = register.whyNoInputTakes(way(7), () -> {
                asked.incrementAndGet();
                return Optional.of(PROOF);
            });
            assertEquals(new WaysNoInputTakes.Asked.Proved(PROOF), answered);
        }

        assertEquals(1, asked.get(), "one way asked three times is asked once");
    }
}
