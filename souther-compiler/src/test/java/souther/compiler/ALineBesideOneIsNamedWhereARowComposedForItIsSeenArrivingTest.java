package souther.compiler;

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
 * A line beside a border that the rows leave, where the conditions on the way to it say nothing
 * a step along the line keeps, is named once a row composed to rule it out is seen run to the
 * comparison.
 *
 * <p>Past {@code Map.get(period, by)} answering an entry, which a step along the line moves the
 * entry's value past without saying whether the lookup still finds it, the rows of one quota leave
 * lines weighing the entry or the quota once more standing. A row composed on the far side of each
 * and run is an input that arrives, so the line is one an author is shown, with that input; and a
 * row written there rules it out.
 */
class ALineBesideOneIsNamedWhereARowComposedForItIsSeenArrivingTest {

    private static final String MODEL = """
            module p
            behavior f : (by: Map<String, Int>, period: String, quota: Int) -> Int
            let f (by, period, quota) =
                match Map.get(period, by) with
                    | None -> 0
                    | Some got -> if got >= quota then 1 else 2
            example f
                | "on" : ([("Q", 5)], "Q", 5) -> 1
                | "off" : ([("Q", 4)], "Q", 5) -> 2
                | "in" : ([("Q", 9)], "Q", 5) -> 1
                | "out" : ([("Q", 0)], "Q", 5) -> 2
                | "none" : ([], "Q", 5) -> 0
            """;

    private static String report(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors(), "the model compiles");
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }

    private static List<String> besides(String report) {
        return report.lines().map(String::strip)
                .filter(line -> line.startsWith("! no row tells")).toList();
    }

    /** Each line the rows leave is named with an input, and nothing of the border is left
     *  unmeasured for want of one. */
    @Test
    void eachLineTheRowsLeaveIsNamedWithAnInput() {
        String report = report(MODEL);

        assertEquals(3, besides(report).size(), report);
        besides(report).forEach(line -> assertTrue(line.contains("and a row at"), line));
        assertFalse(report.contains("not all of it was measured"), report);
    }

    /** The input named for the line weighing the entry twice rules it out once a row is written
     *  there: the control, that the input is one telling the two apart. */
    @Test
    void aRowAtTheInputNamedRulesTheLineOut() {
        String named = besides(report(MODEL)).stream()
                .filter(line -> line.contains("`2 * by[*] - quota = 5`")).findFirst().orElseThrow();
        assertTrue(named.contains("`by[*] = 6, quota = 7`"), named);

        String report = report(MODEL + """
                    | "the entry twice" : ([("Q", 6)], "Q", 7) -> 2
                """);

        assertTrue(besides(report).stream().noneMatch(line -> line.contains("2 * by[*]")),
                report);
    }
}
