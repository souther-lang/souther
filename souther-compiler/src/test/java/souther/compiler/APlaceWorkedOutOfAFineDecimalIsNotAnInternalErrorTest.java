package souther.compiler;

import org.junit.jupiter.api.Test;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A place worked out from a decimal of a scale near the end of the range is a place the coverage
 * questions may fail to hold, and failing to hold it is never an internal error.
 *
 * <p>Squaring a tenth doubles its scale, so a chain of them written as named values reaches a
 * decimal of a scale well inside the range and of more places than any number built from it and
 * {@code 1} can be held in. Each question below puts such a decimal beside an ordinary one on the
 * way to a coverage answer. What that question says about the pair is its own to decide; what each
 * of them owes is that it says something and does not stop with an arithmetic exception.
 *
 * <p>Asked of the answers and never of a rendered report: writing such a decimal out in full is a
 * separate matter, and a report here would be a test of that instead. For the same reason a rule
 * that bounds a position at a fine decimal is not asked here: the report's assembly writes that
 * bound out in full as it goes, so such a model is a test of the writing. What a value inside such
 * a bound is, and a value beside one, are held where they are worked out
 * ({@code AValueInsideARunWithNoStepIsWorkedOutOrNotOfferedTest}).
 */
class APlaceWorkedOutOfAFineDecimalIsNotAnInternalErrorTest {

    /** Where two row values of a pair stand apart. */
    @Test
    void thePlacesTwoRowValuesStandApart() {
        assertAnswered("""
                behavior below : (a: Decimal, b: Decimal) -> Bool
                let below (a, b) = a < b

                example below
                    | "fine is below one" : (fine, 1.0m) -> true
                    | "one is not below nought" : (1.0m, 0.0m) -> false
                """);
    }

    /** Where one position of a pair stands once the other is placed, the distance being fine. */
    @Test
    void thePlaceAFineDistanceMovesAPositionTo() {
        assertAnswered("""
                behavior below : (a: Int, b: Int) -> Bool
                let below (a, b) = Decimal.fromInt(a) - Decimal.fromInt(b) < fine

                example below
                    | "apart" : (5, 1) -> false
                """);
    }

    /**
     * The report assembled, which is what asks the coverage questions, and never written out. And
     * the source first held to compiling cleanly, since a model with an error in it asks nothing
     * and would pass here for the wrong reason.
     */
    private static void assertAnswered(String behavior) {
        Compilation compilation = Compilation.ofSource(FINE + behavior, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors(), "the model is one the language admits");
        assertDoesNotThrow(() -> AdequacyReport.of(compilation));
    }

    /** A tenth squared over and over, named at every step, and {@code fine} the last of them. */
    private static final String FINE = fine();

    private static String fine() {
        StringBuilder chain = new StringBuilder("""
                module example.fine

                let sq (x: Decimal): Decimal = x * x

                let t0 = 0.1m
                """);
        for (int i = 1; i <= 30; i++) {
            chain.append("let t").append(i).append(" = sq(t").append(i - 1).append(")\n");
        }
        return chain.append("let fine = t30\n\n").toString();
    }
}
