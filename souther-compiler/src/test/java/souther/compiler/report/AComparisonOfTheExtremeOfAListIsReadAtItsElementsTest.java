package souther.compiler.report;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.CsvSource;

import souther.compiler.ACompiledModel;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The greatest of a list is at or below a number exactly where every element is, and at or above
 * it where some element is; the least is the other way round. A comparison of either with a
 * number is read at the elements, as {@code List.all} and {@code List.any} are, however the option
 * the list answers is opened.
 *
 * <p>Only the reading is asked, with no row measured: what is held is which lines are drawn. Each
 * case carries one claim — which end is every and which some, that a {@code match} opens the option
 * as {@code Option.withDefault} does, that equality and difference are composed of the two ends,
 * that the number written first is the same comparison, and that a list made of each element of
 * another is read at the elements of that other.
 */
class AComparisonOfTheExtremeOfAListIsReadAtItsElementsTest {

    private static String reading(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(new Adequacy.Asked(Adequacy.Level.OFF, false));
        ACompiledModel.compiles(compilation);
        return AdequacyReport.of(compilation)
                .humanInEnglish(SourceRendering.namedByIdentity(compilation.texts()));
    }

    private static String ofACondition(String condition) {
        return reading("""
                module m

                behavior role : (ds: List<Int>, q: Int) -> Int
                let role (ds, q) = if %s then 1 else 2
                """.formatted(condition));
    }

    /** The lines of the report that say where the elements are divided, and nothing else of it. */
    private static List<String> linesDrawn(String report) {
        return report.lines().map(String::strip)
                .filter(line -> line.startsWith("· read as "))
                .map(line -> line.split(" — ")[0]).sorted().toList();
    }

    private static void assertDrawsAtTheElements(String report) {
        assertFalse(report.contains("held together"), report);
        assertFalse(report.contains("· not read:"), report);
        assertTrue(linesDrawn(report).stream().anyMatch(line -> line.contains("ds[*]")), report);
    }

    /**
     * The greatest at or below a number is every element, and the least is some element. The
     * default stands where the list is empty, and is taken so that it answers what that form
     * answers of an empty list: {@code all} holds of none and {@code any} fails of none.
     */
    @ParameterizedTest(name = "{0} <= 10 is List.{1}")
    @CsvSource({"max, all, 0", "min, any, 100"})
    void anEndDrawsTheLinesOfEveryOrSomeElement(String end, String quantifier, int dflt) {
        String equivalent = ofACondition("List." + quantifier + "(d -> d <= 10, ds)");
        String viaDefault = ofACondition("Option.withDefault(" + dflt + ", List." + end
                + "(ds)) <= 10");

        assertDrawsAtTheElements(viaDefault);
        assertEquals(linesDrawn(equivalent), linesDrawn(viaDefault), viaDefault);
    }

    @Test
    void aMatchOpensTheOptionAsWithDefaultDoes() {
        String viaDefault = ofACondition("Option.withDefault(0, List.max(ds)) <= 10");
        String viaMatch = ofACondition("(match List.max(ds) with | None -> 0 | Some m -> m) <= 10");

        assertDrawsAtTheElements(viaMatch);
        assertEquals(linesDrawn(viaDefault), linesDrawn(viaMatch), viaMatch);
    }

    @ParameterizedTest(name = "max {0} 10")
    @CsvSource({"==", "/="})
    void equalityAndDifferenceAreComposedOfTheTwoEnds(String relation) {
        assertDrawsAtTheElements(ofACondition("Option.withDefault(0, List.max(ds)) " + relation
                + " 10"));
    }

    @Test
    void theNumberWrittenFirstIsTheSameComparison() {
        String first = ofACondition("10 <= Option.withDefault(100, List.min(ds))");
        String after = ofACondition("Option.withDefault(100, List.min(ds)) >= 10");

        assertDrawsAtTheElements(first);
        assertEquals(linesDrawn(after), linesDrawn(first), first);
    }

    @Test
    void theNumberMayBeAnotherOfTheInput() {
        assertDrawsAtTheElements(ofACondition("Option.withDefault(0, List.max(ds)) >= q"));
    }

    /** A rate wearing a name, the list made of each line's rate and compared through its value by
     *  the library's order: the elements the end is read at are the lines'. */
    @Test
    void anEndOfAListMadeOfEachElementIsReadAtTheElementsItIsMadeOf() {
        String model = """
                module m

                data Rate = Decimal
                data Line = { discount: Rate }

                behavior f : (lines: List<Line>) -> Int
                let f (lines) = if %s then 1 else 2
                """;
        String equivalent = reading(model.formatted(
                "List.all(r -> Decimal.compare(r.value, 0.10m) <= 0,"
                        + " List.map(l -> l.discount, lines))"));
        String viaDefault = reading(model.formatted("Decimal.compare(Option.withDefault("
                + "Rate(0.0m), List.max(List.map(l -> l.discount, lines))).value, 0.10m) <= 0"));

        assertFalse(viaDefault.contains("· not read:"), viaDefault);
        assertFalse(linesDrawn(viaDefault).isEmpty(), viaDefault);
        assertEquals(linesDrawn(equivalent), linesDrawn(viaDefault), viaDefault);
    }
}
