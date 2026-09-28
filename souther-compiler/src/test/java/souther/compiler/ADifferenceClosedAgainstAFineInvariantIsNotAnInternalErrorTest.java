package souther.compiler;

import org.junit.jupiter.api.Test;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A newtype whose invariant bounds it at a decimal of a scale near the end of the range puts its
 * own coordinate's difference bounds, and any comparison of it, through the same fine arithmetic —
 * and failing to close them is never an internal error.
 *
 * <p>Squaring a tenth doubles its scale, so a chain of them written as named values reaches a
 * decimal of more places than an ordinary decimal and it can be held apart in one number. A newtype
 * bounded below by such a value puts every pair of its coordinates through {@code
 * DifferenceBounds.closing}, which is where this compiler used to let an {@code ExactFailure} out
 * as an uncaught exception rather than closing what it could and answering with less.
 *
 * <p>Asked of the answers and never of a rendered report, for the same reason as the sibling test
 * this one is beside ({@code APlaceWorkedOutOfAFineDecimalIsNotAnInternalErrorTest}): writing such
 * a bound out in full is a separate matter, and a report here would be a test of that instead.
 */
class ADifferenceClosedAgainstAFineInvariantIsNotAnInternalErrorTest {

    /** The two rows the issue's reproducer named, held to answering rather than aborting. */
    @Test
    void theDifferenceOfTwoBoundedValuesIsNotAnInternalError() {
        assertAnswered("""
                let below (a, b) = a.value - b.value < 1.0m

                example below
                    | "x" : (P(5.0m), P(1.0m)) -> false
                """);
    }

    /** The same newtype, held against an ordinary decimal rather than against another of its kind. */
    @Test
    void aBoundedValueComparedToAnOrdinaryOneIsNotAnInternalError() {
        assertAnswered("""
                let below (a, b) = a.value > 5.0m

                example below
                    | "x" : (P(6.0m), P(1.0m)) -> true
                """);
    }

    /**
     * The report assembled, which is what closes the difference bounds, and never written out. And
     * the source first held to compiling cleanly, since a model with an error in it asks nothing
     * and would pass here for the wrong reason.
     */
    private static void assertAnswered(String below) {
        Compilation compilation = Compilation.ofSource(BOUNDED + "behavior below : (a: P, b: P) -> Bool\n"
                + below, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors(), "the model is one the language admits");
        assertDoesNotThrow(() -> AdequacyReport.of(compilation));
    }

    /** A tenth squared over and over, named at every step, and a newtype bounded below by the last
     *  of them. */
    private static final String BOUNDED = bounded();

    private static String bounded() {
        StringBuilder chain = new StringBuilder("""
                module example.bounded

                let sq (x: Decimal): Decimal = x * x

                let t0 = 0.1m
                """);
        for (int i = 1; i <= 30; i++) {
            chain.append("let t").append(i).append(" = sq(t").append(i - 1).append(")\n");
        }
        return chain.append("""

                data P = Decimal
                    invariant value > t30

                """).toString();
    }
}
