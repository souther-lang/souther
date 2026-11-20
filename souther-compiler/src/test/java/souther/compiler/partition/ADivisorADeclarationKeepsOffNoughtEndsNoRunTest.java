package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.ACompiledModel;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A remainder ends a run only on a divisor of nought. Where the declarations hold
 * the divisor to numbers that leave nought out, whether the range is above it or below it, the
 * operation ends none: the model is measured complete and nothing is said unread. Where they leave
 * nought in, it may, and the comparison it is worked out for is not read for that.
 */
class ADivisorADeclarationKeepsOffNoughtEndsNoRunTest {

    private static final String SOURCE = """
            module m1

            data Eaches = Int
                invariant value >= 0
            data PackSize = Int
                %s
            data Whole = { n: Int }
            data Part = { left: Int }

            behavior split : (eaches: Eaches, pack: PackSize) -> Whole | Part

            let split (eaches, pack) = {
                let leftover = Int.floorMod(eaches.value, pack.value)
                guard leftover == 0 else Part { left = leftover }
                Whole { n = %s }
            }

            example split
            %s
            """;

    private static final String QUOTIENT = "Rational.toInt(DOWN, eaches.value / pack.value)";

    private static final String ROWS_BY_TWELVE = """
                | "exact" : (Eaches(24), PackSize(12)) -> Whole { n = 1 }
                | "short" : (Eaches(25), PackSize(12)) -> Part { left = 1 }""";

    /** The report of the model, line by line. */
    private static List<String> report(String invariant, String whole, String rows) {
        Compilation compilation = Compilation.ofSource(
                SOURCE.formatted(invariant, whole, rows), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        ACompiledModel.compiles(compilation);
        return AdequacyReport.of(compilation)
                .humanInEnglish(SourceRendering.namedByIdentity(compilation.texts())).lines()
                .toList();
    }

    private static boolean measuredComplete(List<String> report) {
        return report.stream().anyMatch(line -> line.contains("m1")
                && line.contains("measurement: complete"));
    }

    private static List<String> notRead(List<String> report) {
        return report.stream().filter(line -> line.contains("not read:")).toList();
    }

    /** What is left unread because a run working the comparison out may end where nothing here
     *  says. */
    private static List<String> notReadForAStop(List<String> report) {
        return notRead(report).stream()
                .filter(line -> line.contains("may end the run where nothing here says"))
                .toList();
    }

    private static void assertRead(List<String> report) {
        assertEquals(List.of(), notRead(report));
        assertTrue(measuredComplete(report), "the model is measured complete");
    }

    private static void assertNotReadForAStop(List<String> report) {
        assertFalse(notReadForAStop(report).isEmpty(), "a stop is what leaves it unread");
        assertFalse(measuredComplete(report), "the model is not measured complete");
    }

    @Test
    void aRemainderByASizeOfAtLeastOneIsRead() {
        assertRead(report("invariant value >= 1", "1", ROWS_BY_TWELVE));
    }

    @Test
    void aRemainderByASizeBelowNoughtIsRead() {
        String rows = """
                | "exact" : (Eaches(24), PackSize(-12)) -> Whole { n = 1 }
                | "short" : (Eaches(25), PackSize(-12)) -> Part { left = -11 }""";
        assertRead(report("invariant value <= -1", "1", rows));
    }

    /** The quotient is worked out after the comparison, so it is no stop of the rows the guard
     *  lets through; the remainder before it is what the divisor's declaration decides. */
    @Test
    void aRoundedQuotientAfterTheGuardLeavesARemainderByASizeRead() {
        String rows = """
                | "exact" : (Eaches(24), PackSize(12)) -> Whole { n = 2 }""";
        assertRead(report("invariant value >= 1", QUOTIENT, rows));
        assertNotReadForAStop(report("", QUOTIENT, rows));
    }

    @Test
    void aRemainderByAnIntThatMayBeNoughtIsNotRead() {
        assertNotReadForAStop(report("", "1", ROWS_BY_TWELVE));
    }

    @Test
    void aRemainderByASizeThatReachesNoughtIsNotRead() {
        String rows = """
                | "exact" : (Eaches(24), PackSize(1)) -> Whole { n = 1 }""";
        assertNotReadForAStop(report("invariant value >= -1 && value <= 1", "1", rows));
    }
}
