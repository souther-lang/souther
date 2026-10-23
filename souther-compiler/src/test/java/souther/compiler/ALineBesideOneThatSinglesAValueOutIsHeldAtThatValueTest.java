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
 * A rule that singles a value out is held against the lines one step from it, as a rule ordering
 * the values is.
 *
 * <p>{@code amount == gross} keeps the rows on its line and refuses the rest. A line weighing one
 * of the two once more keeps the rows at one place along it, so rows on the model's line that all
 * stand at one place along it leave it standing — and a row on the model's line at another place,
 * or off it at that place, rules it out. A denial of the rule is the same the other way round.
 */
class ALineBesideOneThatSinglesAValueOutIsHeldAtThatValueTest {

    private static final String EQUAL = """
            module p
            behavior f : (amount: Int, gross: Int) -> Int
            let f (amount, gross) = if amount == gross then 1 else 2
            example f
                | "on" : (5, 5) -> 1
                | "below" : (4, 5) -> 2
                | "above" : (6, 5) -> 2
                | "far below" : (0, 5) -> 2
                | "far above" : (9, 5) -> 2
            """;

    private static final String NOT_EQUAL = EQUAL
            .replace("amount == gross", "amount /= gross")
            .replace("-> 1\n", "-> 3\n").replace("-> 2\n", "-> 1\n").replace("-> 3\n", "-> 2\n");

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

    /** Rows at one place on the model's line leave each line weighing a position once more, at
     *  that place, and each is named with an input; nothing is left unmeasured for want of a
     *  strategy. */
    @Test
    void eachLineTheRowsLeaveAtOneValueIsNamedWithAnInput() {
        for (String model : List.of(EQUAL, NOT_EQUAL)) {
            String report = report(model);

            assertEquals(3, besides(report).size(), report);
            besides(report).forEach(line -> assertTrue(line.contains("and a row at"), line));
            assertTrue(report.contains("from `2 * amount - gross = 5`"), report);
            assertFalse(report.contains("not all of it was measured"), report);
        }
    }

    /** A row on the model's line at another place along the line beside it rules that line out:
     *  the control, that the input named tells the two apart. */
    @Test
    void aRowOnTheLineAtAnotherPlaceRulesTheLineOut() {
        String report = report(EQUAL + """
                    | "on, further along" : (6, 6) -> 1
                """);

        assertEquals(List.of(), besides(report), report);
    }

    /** A row off the model's line at the place the line beside it keeps rules that line out, and
     *  only that one: the line keeps it and the model refuses it. */
    @Test
    void aRowOffTheLineAtThePlaceRulesThatLineOut() {
        String report = report(EQUAL + """
                    | "off, at five" : (5, 7) -> 2
                """);

        assertEquals(2, besides(report).size(), report);
        assertTrue(besides(report).stream().noneMatch(line -> line.contains("from `amount = 5`")),
                report);
    }

    /** And rows on the model's line at places apart, which is how a model's own rows usually stand,
     *  rule every line of the family out at once. */
    @Test
    void rowsOnTheLineAtPlacesApartRuleEveryLineOut() {
        String report = report(EQUAL.replace("| \"far above\" : (9, 5) -> 2",
                "| \"far above\" : (9, 5) -> 2\n    | \"on, elsewhere\" : (-3, -3) -> 1"));

        assertEquals(List.of(), besides(report), report);
        assertFalse(report.contains("not all of it was measured"), report);
    }
}
