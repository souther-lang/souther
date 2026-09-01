package souther.compiler;

import souther.compiler.diag.Severity;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Composing a comparison out of what an order states repeats while it says something.
 *
 * <p>What an operation answering an order answers is a sign, so a condition settling which side of
 * nought that sign falls on is a condition about the two values it ordered. The sign is a number
 * like any other, so a condition about <em>it</em> can be written the same way round again — and the
 * comparison that comes of reading it once is one more thing to read.
 *
 * <p>Held here because the readings of a condition are a sequence and not a pair
 * ({@link souther.compiler.check.ComparisonReadings}). A reading that composed once and stopped
 * answers every question about a guard written once and loses the values underneath a guard written
 * twice, and nothing between the two cases would say which had happened.
 */
class AnOrderOfASignIsReadDownToTheValuesUnderneathItTest {

    private static final String MODULE = """
            module demo

            data NonNeg = Int
                invariant value >= 0
            data Fine

            behavior f : (a: Int, b: Int) -> NonNeg | Fine
                constructs NonNeg

            let f (a, b) = {
                if %s then
                    NonNeg(a - b)
                else
                    Fine
            }
            """;

    private static long warningsUnder(String guard) {
        return Compiler.compileWithWarnings(MODULE.formatted(guard)).warnings().stream()
                .filter(d -> d.severity() == Severity.WARNING).count();
    }

    /** One composition, which is what the guard as written comes to about {@code a} and {@code b}. */
    @Test
    void anOrderOfTwoValuesIsReadAsTheirComparison() {
        assertEquals(0, warningsUnder("Int.compare(a, b) >= 0"),
                "the guard says a is at or above b, so the difference this constructs is not"
                        + " negative");
    }

    /**
     * And an order of that order comes to the same comparison, one composition further down.
     *
     * <p>The reading after the first is what settles this: composed once, the guard says the sign
     * {@code Int.compare(a, b)} answers is at or above nought, which is a statement about a value no
     * clause here is written over. Composed again, it says what that sign is the order of.
     */
    @Test
    void anOrderOfASignIsReadDownToWhatTheSignOrdered() {
        assertEquals(0, warningsUnder("Int.compare(Int.compare(a, b), 0) >= 0"),
                "the sign of the sign is at or above nought, so the sign is, so a is at or above b");
    }

    /** And where the values underneath are the other way round, the clause is not discharged — so
     *  the reading above is the guard being read and not a construction nothing looks at. */
    @Test
    void theSameGuardTheOtherWayRoundDoesNotDischargeIt() {
        assertEquals(1, warningsUnder("Int.compare(Int.compare(b, a), 0) >= 0"),
                "that guard says b is at or above a, which leaves the difference constructed here"
                        + " able to be negative");
    }
}
