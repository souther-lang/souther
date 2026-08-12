package souther.compiler.check;

import souther.compiler.Compiler;
import souther.compiler.check.InvariantChecker.GaveUp;
import souther.compiler.check.InvariantChecker.Said;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * That the discharge analysis ran, where a test is about to hold it to what it found.
 *
 * <p>The check is fail-open: any exception out of the walk leaves the run-time invariant check as the
 * backstop, which is what stops an analysis bug from rejecting a correct program. The cost is that
 * falling over and finishing empty-handed produce the same thing — no error, no warning — so every
 * test that asserts a construction is discharged also passes when nothing was analysed at all.
 *
 * <p>How much that costs was measured rather than guessed: made to throw on every atom it looks up,
 * the analysis takes two tests in the whole compiler suite down with it. Everything else agrees that
 * silence is silence. So this is not a spare assertion beside the others — it is the only one that
 * says the instrument was switched on.
 */
class AnAnalysisThatStoppedIsNotOneThatFoundNothingTest {

    /** A guard discharging a bound, which is the shape the analysis exists for: the construction is
     * reached, a comparison narrows what is known of the value, and the clause is asked at it. */
    private static final String DISCHARGED = """
            module demo
            data Yen = Int
                invariant nonNegative = value >= 0
            behavior f : (n: Int) -> Yen constructs Yen
            let f (n) = {
                guard n >= 0 else Yen(0)
                Yen(n)
            }
            """;

    /** A relation between two whole numbers, which is the difference-bound part of the domain rather
     * than its intervals. Held here because it is the part {@code souther-examples} exercises and the
     * part a change to strictness moves. */
    private static final String RELATED = """
            module demo
            data Yen = Int
                invariant nonNegative = value >= 0
            behavior f : (a: Int, b: Int) -> Yen constructs Yen
            let f (a, b) = {
                guard a >= b else Yen(0)
                guard b >= 0 else Yen(0)
                Yen(a)
            }
            """;

    private record Ran(List<Said> said, List<GaveUp> gaveUp) {}

    private static Ran compiling(String source) {
        List<Said> said = Collections.synchronizedList(new ArrayList<>());
        List<GaveUp> gaveUp = Collections.synchronizedList(new ArrayList<>());
        InvariantChecker.WATCHING = said;
        InvariantChecker.GAVE_UP = gaveUp;
        try {
            Compiler.compileWithWarnings(source);
        } finally {
            InvariantChecker.WATCHING = null;
            InvariantChecker.GAVE_UP = null;
        }
        return new Ran(said, gaveUp);
    }

    @Test
    void aDischargedBoundWasReachedByAnAnalysisThatFinished() {
        Ran ran = compiling(DISCHARGED);

        assertTrue(ran.gaveUp().isEmpty(),
                () -> "the analysis stopped at " + ran.gaveUp().get(0).where()
                        + ", so what it did not report is not what it did not find: "
                        + ran.gaveUp().get(0).why());
        assertFalse(ran.said().isEmpty(),
                "and it reached a construction, so an empty list of what it stopped on means"
                        + " something");
    }

    @Test
    void aRelationBetweenTwoAtomsWasReachedTheSameWay() {
        Ran ran = compiling(RELATED);

        assertTrue(ran.gaveUp().isEmpty(),
                () -> "the analysis stopped at " + ran.gaveUp().get(0).where() + ": "
                        + ran.gaveUp().get(0).why());
        assertFalse(ran.said().isEmpty(), "and it reached a construction");
    }

    /** A behavior with no {@code let} has no body to walk, and the analysis is not reported as having
     * stopped on one. Both come out with nothing found, and only one of them is an instrument that
     * failed. */
    @Test
    void aBehaviorWithNoBodyIsNotAnAnalysisThatStopped() {
        Ran ran = compiling("""
                module demo
                data Yen = Int
                    invariant nonNegative = value >= 0
                behavior f : (n: Int) -> Yen
                """);

        assertEquals(List.of(), ran.gaveUp(), "there was nothing to fall over on");
    }
}
