package souther.compiler.report;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.CsvSource;

import souther.compiler.ACompiledModel;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import java.util.ArrayList;
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

    /**
     * What the report says of where the elements are divided: the summary of the borders, which
     * counts them and the points they owe, and each line drawn. The reasons a point is not shown
     * reached, and the partition and decision lines, differ between spellings that are one rule
     * and are left out.
     */
    private static List<String> linesDrawn(String report) {
        List<String> said = new ArrayList<>();
        report.lines().map(String::strip).filter(line -> line.startsWith("border "))
                .findFirst().ifPresent(line -> said.add(line.replaceAll("\\s+", " ")));
        report.lines().map(String::strip)
                .filter(line -> line.startsWith("· read as "))
                .map(line -> line.split(" — ")[0]).sorted().forEach(said::add);
        return said;
    }

    private static void assertDrawsAtTheElements(String report) {
        assertFalse(report.contains("held together"), report);
        assertFalse(report.contains("· not read:"), report);
        assertTrue(linesDrawn(report).stream().anyMatch(line -> line.contains("ds[*]")), report);
    }

    /**
     * Each relation of an end with a number, beside the {@code List.all} or {@code List.any} it
     * comes to: the greatest at or below a number is every element, at or above it some element,
     * and the least the other way round. Which of the two is a polarity one inversion turns, and
     * each relation is a case of it. The default stands where the list is empty, and is taken so
     * that it answers what that form answers of an empty list: {@code all} holds of none and
     * {@code any} fails of none.
     */
    @ParameterizedTest(name = "{0} {1} 10 is List.{2}")
    @CsvSource({
            "max, <=, all, 0", "max, <, all, 0", "max, >=, any, 0", "max, >, any, 0",
            "min, <=, any, 100", "min, <, any, 100", "min, >=, all, 100", "min, >, all, 100"})
    void anEndDrawsTheLinesOfEveryOrSomeElement(String end, String relation, String quantifier,
                                                int dflt) {
        String equivalent = ofACondition("List." + quantifier + "(d -> d " + relation
                + " 10, ds)");
        String viaDefault = ofACondition("Option.withDefault(" + dflt + ", List." + end
                + "(ds)) " + relation + " 10");

        assertDrawsAtTheElements(viaDefault);
        assertEquals(linesDrawn(equivalent), linesDrawn(viaDefault), viaDefault);
    }

    /** The whole report, as {@code withDefault} is the {@code match} it expands to: where each
     *  was written is the only thing the two reports may differ in. */
    @Test
    void aMatchOpensTheOptionAsWithDefaultDoes() {
        String viaDefault = ofACondition("Option.withDefault(0, List.max(ds)) <= 10");
        String viaMatch = ofACondition("(match List.max(ds) with | None -> 0 | Some m -> m) <= 10");

        assertDrawsAtTheElements(viaMatch);
        assertEquals(withoutPositions(viaDefault), withoutPositions(viaMatch));
    }

    private static String withoutPositions(String report) {
        return report.replaceAll("comparison@[0-9:]+", "comparison@")
                .replaceAll("(, )?at [0-9]+:[0-9]+", "");
    }

    /** A step that may end a run ends it on every element it is handed, whatever the comparison of
     *  its answers is, which the reading made here does not tell of. */
    @Test
    void aListMadeByAStepThatMayEndARunIsNotReadAtTheElementsItIsMadeOf() {
        String report = ofACondition(
                "Option.withDefault(0, List.max(List.map(x -> x + 1, ds))) <= 10");

        assertTrue(report.contains("· not read:"), report);
        assertFalse(report.contains("· read as "), report);
    }

    @ParameterizedTest(name = "{0} {1} 10")
    @CsvSource({"max, ==", "max, /=", "min, ==", "min, /="})
    void equalityAndDifferenceAreComposedOfTheTwoEnds(String end, String relation) {
        assertDrawsAtTheElements(ofACondition("Option.withDefault(0, List." + end + "(ds)) "
                + relation + " 10"));
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

    /**
     * What an arm binds to the payload of a call that answers an element of a list came from that
     * list's elements, whichever call it is and however the payload is used. A comparison of a
     * value worked out of it is about the elements and is not read, which the report says at them:
     * it is no comparison of constants, and the measurement is not complete.
     */
    @ParameterizedTest(name = "{0}")
    @CsvSource(delimiter = '|', value = {
            "List.max(ds) | m + 1 <= 10",
            "List.max(ds) | m * 2 <= 10",
            "List.min(ds) | Int.abs(m) >= 10",
            "List.find(x -> x > q, ds) | m + 1 <= 10",
            "List.get(q, ds) | m + 1 <= 10"})
    void aValueWorkedOutOfAPayloadIsSaidNotReadAtTheElements(String call, String comparison) {
        String report = ofACondition("(match " + call + " with | None -> false | Some m -> "
                + comparison + ")");

        assertTrue(report.contains("measurement: partial"), report);
        assertTrue(report.lines().anyMatch(line -> line.contains("· not read:")
                && line.contains("about `ds[*]`")), report);
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
