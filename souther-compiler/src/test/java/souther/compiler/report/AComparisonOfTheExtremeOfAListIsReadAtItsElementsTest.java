package souther.compiler.report;

import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.CsvSource;

import souther.compiler.ACompiledModel;
import souther.compiler.diag.SourceLayouts;
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
 * the list answers is opened: by {@code Option.withDefault} or by a {@code match}.
 *
 * <p>What is held is that the lines drawn are the ones the equivalent {@code List.all} or
 * {@code List.any} draws, and that the two ways of opening the option say the same.
 */
class AComparisonOfTheExtremeOfAListIsReadAtItsElementsTest {

    private static String report(String model) {
        Compilation compilation = ACompiledModel.measured(model, Adequacy.Asked.fullReport());
        return AdequacyReport.of(compilation)
                .humanInEnglish(SourceRendering.namedByIdentity(SourceLayouts.NONE));
    }

    private static String model(String condition) {
        return """
                module m

                behavior role : (ds: List<Int>) -> Int
                let role (ds) = if %s then 1 else 2
                """.formatted(condition);
    }

    /** The lines of the report that say where the elements are divided, and nothing else of it. */
    private static List<String> linesDrawn(String report) {
        return report.lines().map(String::strip)
                .filter(line -> line.startsWith("· read as "))
                .map(line -> line.split(" — ")[0]).sorted().toList();
    }

    /**
     * Each relation of an end with 10, beside the {@code List.all} or {@code List.any} it comes to.
     * The default stands where the list is empty, and is taken so that it answers what that form
     * answers of an empty list: {@code all} holds of none and {@code any} fails of none.
     */
    @ParameterizedTest(name = "{0} {1} 10 is List.{2}")
    @CsvSource({
            "max, <=, all, 0",
            "max, <,  all, 0",
            "max, >=, any, 0",
            "max, >,  any, 0",
            "min, <=, any, 100",
            "min, <,  any, 100",
            "min, >=, all, 100",
            "min, >,  all, 100"})
    void anEndComparedWithANumberDrawsTheLinesOfEveryOrSomeElement(
            String end, String relation, String quantifier, int dflt) {
        String equivalent = report(model("List." + quantifier + "(d -> d " + relation
                + " 10, ds)"));
        String viaDefault = report(model("Option.withDefault(" + dflt + ", List." + end
                + "(ds)) " + relation + " 10"));
        String viaMatch = report(model("(match List." + end + "(ds) with | None -> " + dflt
                + " | Some m -> m) " + relation + " 10"));

        assertFalse(viaDefault.contains("held together"), viaDefault);
        assertFalse(viaMatch.contains("held together"), viaMatch);
        assertEquals(linesDrawn(equivalent), linesDrawn(viaDefault), viaDefault);
        assertEquals(linesDrawn(equivalent), linesDrawn(viaMatch), viaMatch);
        assertFalse(linesDrawn(viaDefault).isEmpty(), viaDefault);
    }

    /** The number an end is compared with may be another of the input's: the elements are held
     *  against it as they are against a constant. Where the list is empty the default is what is
     *  compared, so lines of the list's length come beside the ones at the elements. */
    @ParameterizedTest(name = "{0} >= q")
    @CsvSource({"max, 0", "min, 100"})
    void anEndComparedWithAnotherNumberOfTheInputIsReadAtTheElements(String end, int dflt) {
        String report = report("""
                module m

                behavior role : (ds: List<Int>, q: Int) -> Int
                let role (ds, q) = if Option.withDefault(%d, List.%s(ds)) >= q then 1 else 2
                """.formatted(dflt, end));

        assertFalse(report.contains("held together"), report);
        assertFalse(report.contains("not read"), report);
        assertTrue(linesDrawn(report).stream().anyMatch(line -> line.contains("ds[*]")), report);
    }

    /** A rate wearing a name, the list made of each line's rate and compared through its value by
     *  the library's order: the elements the end is read at are the lines'. */
    @ParameterizedTest(name = "{0} through List.map and Decimal.compare is List.{1}")
    @CsvSource({"max, all", "min, any"})
    void anEndOfAListMadeOfEachElementIsReadAtTheElementsItIsMadeOf(String end, String quantifier) {
        String model = """
                module m

                data Rate = Decimal
                data Line = { discount: Rate }

                behavior f : (lines: List<Line>) -> Int
                let f (lines) = if %s then 1 else 2
                """;
        String dflt = end.equals("max") ? "0.0m" : "1.0m";
        String equivalent = report(model.formatted("List." + quantifier
                + "(r -> Decimal.compare(r.value, 0.10m) <= 0, List.map(l -> l.discount, lines))"));
        String viaDefault = report(model.formatted("Decimal.compare(Option.withDefault(Rate(" + dflt
                + "), List." + end + "(List.map(l -> l.discount, lines))).value, 0.10m) <= 0"));

        assertFalse(viaDefault.contains("not read"), viaDefault);
        assertEquals(linesDrawn(equivalent), linesDrawn(viaDefault), viaDefault);
        assertFalse(linesDrawn(viaDefault).isEmpty(), viaDefault);
    }

    /** Equality is the end at or below and at or above, and a difference is the end below or
     *  above, each at the elements. */
    @ParameterizedTest(name = "{0} {1} 10")
    @CsvSource({"max, ==", "max, /=", "min, ==", "min, /="})
    void anEndEqualOrUnequalToANumberIsReadAtTheElements(String end, String relation) {
        String viaDefault = report(model("Option.withDefault(0, List." + end + "(ds)) " + relation
                + " 10"));

        assertFalse(viaDefault.contains("held together"), viaDefault);
        assertFalse(viaDefault.contains("not read"), viaDefault);
        assertFalse(linesDrawn(viaDefault).isEmpty(), viaDefault);
    }

    /** The number written before the end is the same comparison turned about. */
    @ParameterizedTest(name = "10 {0} the {1}")
    @CsvSource({"<=, max", "<, max", ">=, min", ">, min"})
    void aNumberComparedWithAnEndIsTheSameComparisonTurnedAbout(String relation, String end) {
        String turned = switch (relation) {
            case "<=" -> ">=";
            case "<" -> ">";
            case ">=" -> "<=";
            default -> "<";
        };
        String before = report(model("10 " + relation + " Option.withDefault(0, List." + end
                + "(ds))"));
        String after = report(model("Option.withDefault(0, List." + end + "(ds)) " + turned
                + " 10"));

        assertEquals(linesDrawn(after), linesDrawn(before), before);
        assertFalse(linesDrawn(before).isEmpty(), before);
    }
}
