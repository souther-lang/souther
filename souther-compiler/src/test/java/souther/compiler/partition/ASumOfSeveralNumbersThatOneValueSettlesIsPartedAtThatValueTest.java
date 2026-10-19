package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A comparison of three or more numbers, one value of which settles it, is read at each of them:
 * the others together are shown to come to a value on either side of every value left, and the
 * place is not reported as one the other values are not shown to reach.
 */
class ASumOfSeveralNumbersThatOneValueSettlesIsPartedAtThatValueTest {

    private static final String NOT_SHOWN = "not shown to reach";

    private static final String MONTHS_AND_DAYS = """
            data M = { v: Int }
                invariant v >= 1 && v <= 12
            data D = { v: Int }
                invariant v >= 1 && v <= 31
            """;

    private static final String NEAR_THE_GREATEST = """
            data A = { v: Int }
                invariant v >= 9223372036854775800 && v <= 9223372036854775806
            data B = { v: Int }
                invariant v >= 9223372036854775800 && v <= 9223372036854775805
            data Bit = { v: Int }
                invariant v >= 0 && v <= 1
            """;

    @Test
    void severalNumbersOneValueOfWhichSettlesTheComparisonAreAllRead() {
        String report = reportOf(MONTHS_AND_DAYS, "(a: M, b: M, c: D, d: D)",
                "a.v + c.v < b.v");
        assertFalse(report.contains(NOT_SHOWN), report);
    }

    /**
     * The control: the same comparison where the others' sum passes where the type stops is a sum
     * no row computes at its greatest, so the others are no witness and the place keeps its
     * reason.
     */
    @Test
    void whereTheOthersSumPassesWhereTheTypeStopsThePlaceKeepsItsReason() {
        String report = reportOf(NEAR_THE_GREATEST, "(a: A, b: B, c: Bit, d: Bit)",
                "a.v < b.v + 3 * c.v + 4 * d.v");
        assertTrue(report.contains(NOT_SHOWN), report);
    }

    private static String reportOf(String declarations, String parameters, String condition) {
        Compilation compilation = Compilation.ofSource("module demo\n\n" + declarations + """

                behavior f : %s -> Int

                let f %s =
                    if %s then 1 else 0
                """.formatted(parameters, parameters.replaceAll(": [A-Za-z]+", ""), condition),
                "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code().toString()).toList());
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }
}
