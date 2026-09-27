package souther.compiler;

import org.junit.jupiter.api.Test;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A report writes a compactly held Decimal in exponent notation past a thousand digits, rather than
 * spelling it out in full.
 *
 * <p>Squaring a tenth doubles its scale, so a chain of them written as named values reaches a
 * decimal the compiler holds in an instant and whose plain notation is over a hundred million
 * characters. Every place that puts such a value in front of a reader — the human report, the JSON
 * report, and a diagnostic over a bound stated at it — has to answer in bounded space, or the one
 * thing that stops the run is the presentation and not the analysis.
 *
 * <p>Held to the reports' own length and not to what they say: what a report says about such a
 * model is its own question, and this one is only that assembling and rendering one completes
 * without exhausting memory or overrunning a writer, in space that does not grow with the scale.
 */
class ADecimalOfExtremeScaleIsWrittenInBoundedNotationTest {

    /** The issue's own reproducer: a bound at a fine decimal, asked for nothing more than a report. */
    @Test
    void aBoundAtAFineDecimalIsReportedInBoundedSpace() {
        assertReportedInBoundedSpace("""
                data P = Decimal
                    invariant value > t30

                behavior below : (a: P, b: P) -> Bool
                let below (a, b) = true

                example below
                    | "x" : (P(5.0m), P(1.0m)) -> true
                """);
    }

    /** A comparison against the fine decimal itself, rather than against a newtype bounded by it. */
    @Test
    void aComparisonAgainstAFineDecimalIsReportedInBoundedSpace() {
        assertReportedInBoundedSpace("""
                behavior atLeast : (a: Decimal) -> Bool
                let atLeast (a) = a >= t30

                example atLeast
                    | "nought" : (0.0m) -> false
                """);
    }

    /** An equality against the fine decimal, the other reproducer the issue's comment names. */
    @Test
    void anEqualityAgainstAFineDecimalIsReportedInBoundedSpace() {
        assertReportedInBoundedSpace("""
                behavior isFine : (a: Decimal) -> Bool
                let isFine (a) = a == t30

                example isFine
                    | "nought" : (0.0m) -> false
                """);
    }

    /**
     * A newtype whose invariant admits the fine decimal as one of a finite set of named values —
     * the shape that reaches {@code ValueClasses.classAt} with it, which used to read the value as
     * one this compiler could not write and stop the compile over the two readings disagreeing,
     * where in fact the reading is exact and the class is one nothing can offer a new row for.
     */
    @Test
    void aFiniteSetOfNamedValuesIncludingTheFineDecimalIsReportedInBoundedSpace() {
        assertReportedInBoundedSpace("""
                data X = Decimal
                    invariant value == t30 || value == 1.0m

                behavior below : (a: X) -> Bool
                let below (a) = true

                example below
                    | "x" : (X(1.0m)) -> true
                """);
    }

    /**
     * The report assembled and both formats the CLI offers rendered, none of them written out. And
     * the source first held to compiling cleanly, since a model with an error in it asks nothing
     * and would pass here for the wrong reason.
     *
     * <p>A length bound and not zero: a report over this model says something about the bound at
     * the fine decimal, and a reader is owed that much. What it is not owed is the decimal's own
     * thousand and more digits, so the bound here is generous against an ordinary report and refuses
     * only what would grow with the scale.
     */
    private static void assertReportedInBoundedSpace(String behavior) {
        Compilation compilation = Compilation.ofSource(FINE + behavior, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors(), "the model is one the language admits");
        AdequacyReport report = assertDoesNotThrow(() -> AdequacyReport.of(compilation));
        SourceRendering rendering = SourceRendering.namedByIdentity(compilation.texts());
        String human = assertDoesNotThrow(() -> report.human(rendering));
        String json = assertDoesNotThrow(() -> report.json(rendering));
        assertTrue(human.length() < 100_000, "the human report stays short of the decimal's own"
                + " scale: " + human.length() + " characters");
        assertTrue(json.length() < 100_000, "and so does the JSON report: " + json.length()
                + " characters");
    }

    /** A tenth squared over and over, named at every step, and {@code t30} the last of them. */
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
        return chain.append("\n").toString();
    }
}
