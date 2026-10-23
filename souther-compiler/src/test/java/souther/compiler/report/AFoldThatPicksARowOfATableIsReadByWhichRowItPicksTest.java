package souther.compiler.report;

import java.util.Set;
import java.util.stream.Collectors;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A fold over a table written out that keeps the row whose lower bound a value has reached, and a
 * comparison of a field of the row it ends with.
 *
 * <p>The walk ends with the last row its condition holds of, or with its seed where it holds of
 * none. So the comparison is the field of each row, taken where that row is the last the condition
 * holds of, and the lines it draws are the table's bounds. Read as a relation of the row's bound
 * and the value, the lookup drew none, and the behavior asking for a grade was left with rows that
 * could not be placed.
 */
class AFoldThatPicksARowOfATableIsReadByWhichRowItPicksTest {

    private static final String HEAD = """
            module probe.grades

            data Req = { a: Int }
            data Row = { grade: Int, lowerBound: Int }

            data Big
            data Small

            let row (g: Int, bound: Int): Row = Row { grade = g, lowerBound = bound }
            """;

    /** The rows of an ascending table: the grade rises with the value. */
    private static final String AS_SORTED = """
            | "small" : (Req { a = 0 })  -> Small
            | "big" : (Req { a = 300 }) -> Big
            """;

    /** The rows of the table out of order below: whichever value, the last row reached has grade
     *  one. */
    private static final String ALWAYS_SMALL = """
            | "below" : (Req { a = 0 })   -> Small
            | "between" : (Req { a = 150 }) -> Small
            | "above" : (Req { a = 300 }) -> Small
            """;

    private static String lookup(String step, String table, String examples) {
        return HEAD + """

                let rowFor (monthly: Int): Row =
                    List.fold((acc, r) -> %s, row(1, 0), %s)

                behavior judge : (req: Req) -> Big | Small
                    constructs Row
                let judge (req) = if rowFor(req.a).grade >= 2 then Big else Small

                example judge
                """.formatted(step, table) + examples.indent(4);
    }

    private static final String ASCENDING = "[row(1, 0), row(2, 100), row(3, 200)]";

    private static final String REACHED = "if r.lowerBound <= monthly then r else acc";

    private static String reportOf(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(SourceLayouts.NONE));
    }

    /** The lines the table's bounds draw are on the value, and nothing is left unread. */
    @Test
    void theTablesBoundsAreTheLinesOfTheValueItIsLookedUpBy() {
        String report = reportOf(lookup(REACHED, ASCENDING, AS_SORTED));

        assertTrue(report.contains("measurement: complete"), report);
        assertTrue(report.contains("= 99"), report);
        assertTrue(report.contains("in 100 < req.a < 200"), report);
        assertFalse(report.contains("written in a form this compiler does not read"), report);
    }

    /** The step written the other way round, keeping the row where the condition does not hold. */
    @Test
    void aStepKeepingTheRowWhereTheConditionFailsIsTheSame() {
        String reversed = reportOf(
                lookup("if r.lowerBound > monthly then acc else r", ASCENDING, AS_SORTED));

        assertEquals(lines(reportOf(lookup(REACHED, ASCENDING, AS_SORTED))), lines(reversed));
    }

    /**
     * A table not in ascending order of its bounds.
     *
     * <p>The row for 200 is not the last of those reached, so the grade is never above one: a
     * reading that took the greatest bound reached would draw a line at 200 for the comparison of
     * the grade, and there is none.
     */
    @Test
    void aTableOutOfOrderIsNotReadAsIfItWereSorted() {
        String report = reportOf(
                lookup(REACHED, "[row(1, 0), row(3, 200), row(1, 100)]", ALWAYS_SMALL));

        assertFalse(report.contains("written in a form this compiler does not read"), report);
        // The comparison of the grade holds for no input, so the way that takes it is owed no row...
        assertTrue(report.contains("no input takes 1 way through this body"), report);
        assertTrue(report.contains("the comparison at null holds"), report);
        // ...and it draws no line on the value, not at the bounds of the rows nor between them.
        assertEquals(Set.of(), lines(report).stream().filter(each -> each.startsWith("· read as"))
                .collect(Collectors.toSet()), report);
    }

    /** The lines of the report about the value looked up that the behavior's own comparison draws,
     *  and not the ones inside the lookup. */
    private static Set<String> lines(String report) {
        return report.lines().filter(each -> each.contains("req.a"))
                .filter(each -> !each.contains("rowFor@null"))
                .map(String::strip).collect(Collectors.toSet());
    }
}
