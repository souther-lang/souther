package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.PartitionEvidence;
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

    /** Each of the three is parted where the others, together, stop reaching both sides; the
     *  fourth, in no comparison, is parted by nothing. */
    @Test
    void eachNumberIsPartedAtTheValueThatSettlesTheComparison() {
        String parameters = "(a: M, b: M, c: D, d: D)";
        String condition = "a.v + c.v < b.v";
        assertEquals(List.of("a.v/1 <= x < 11", "a.v/11 <= x <= 12"),
                classesAt(MONTHS_AND_DAYS, parameters, condition, "a.v"));
        assertEquals(List.of("b.v/1 <= x <= 2", "b.v/2 < x <= 12"),
                classesAt(MONTHS_AND_DAYS, parameters, condition, "b.v"));
        assertEquals(List.of("c.v/1 <= x < 11", "c.v/11 <= x <= 31"),
                classesAt(MONTHS_AND_DAYS, parameters, condition, "c.v"));
    }

    /** {@code v < 32} and {@code v <= 31} hold the same whole numbers, so they part the same. */
    @Test
    void aRunWhoseUpperEndIsLeftOutIsTheRunOfTheWholeNumbersBelowIt() {
        String leftOut = MONTHS_AND_DAYS.replace("v <= 31", "v < 32");
        assertEquals(List.of("a.v/1 <= x < 11", "a.v/11 <= x <= 12"),
                classesAt(leftOut, "(a: M, b: M, c: D, d: D)", "a.v + c.v < b.v", "a.v"));
    }

    private static List<String> classesAt(String declarations, String parameters,
                                          String condition, String path) {
        Compilation compilation = Compilation.ofSource("module demo\n\n" + declarations + """

                behavior f : %s -> Int

                let f %s =
                    if %s then 1 else 0
                """.formatted(parameters, parameters.replaceAll(": [A-Za-z]+", ""), condition),
                "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        PartitionEvidence evidence =
                compilation.db().ask(new Adequacy.Coverage("demo")).value().get("f");
        return evidence.axes().stream().filter(axis -> axis.path().equals(path))
                .flatMap(axis -> axis.classes().stream()).toList();
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
