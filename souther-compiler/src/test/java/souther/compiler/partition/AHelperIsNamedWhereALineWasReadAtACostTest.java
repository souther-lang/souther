package souther.compiler.partition;

import org.junit.jupiter.api.Test;
import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import souther.compiler.ACompiledModel;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.List;
import java.util.Locale;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Where a line was read all the same although its cases were more ways of choosing one than are
 * taken apart, and the cases choose among a helper's readings one beside another, the report names
 * the helper beside the line: the helper, where it was read and the helpers its call has to move
 * out of. Beside the line and no reason it was not read, so no count of the cases is told of it.
 *
 * <p>The model searches four days for a business day, each day read through the helper that says
 * whether it is one: the cases of its lines are many as the choices stand and few as the numbers
 * leave them, at a figure between the two. Below the figure the line is not worked out, and above
 * it its cases are within what is taken apart; in neither is a helper told of beside the line.
 */
class AHelperIsNamedWhereALineWasReadAtACostTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    private static final String MODEL = """
            module demo exposing (g, PaymentCalendar)
            data PaymentCalendar = { holidays: Set<Date>, aSunday: Date }
            let weekday (calendar: PaymentCalendar, d: Date): Int =
                Int.floorMod(Date.daysBetween(calendar.aSunday, d), 7)
            let isBusinessDay (calendar: PaymentCalendar, d: Date): Bool =
                weekday(calendar, d) >= 1 && weekday(calendar, d) <= 5
                    && Bool.not(Set.contains(d, calendar.holidays))
            let firstBusinessDay (calendar: PaymentCalendar, from: Date): Date =
                List.rangeInclusive(0, 3)
                    |> List.map(n -> Date.addDays(n, from))
                    |> List.find(d -> isBusinessDay(calendar, d))
                    |> Option.withDefault(from)
            behavior g : (calendar: PaymentCalendar, from: Date) -> Bool
            let g (calendar, from) =
                Bool.not(isBusinessDay(calendar, firstBusinessDay(calendar, from)))
            """;

    /** Past what the numbers leave of the cases, and below what the choices stand for. */
    private static final int BETWEEN = 20;

    /** The model measured with the cases of a line taken apart into no more than {@code figure}. */
    private static Compilation compiled(int figure) {
        Compilation compilation = Compilation.ofSource(MODEL, "Main").allowing(
                Allowances.DECLARED.with(CompositionBudget.CASES_A_LINE_IS_TAKEN_APART_INTO,
                        figure));
        compilation.measure(Adequacy.Asked.reportOnly(Adequacy.Level.OFF));
        return ACompiledModel.compiles(compilation);
    }

    private static JsonNode partition(Compilation compiled) {
        return JSON.readTree(AdequacyReport.of(compiled)
                        .json(SourceRendering.namedByIdentity(compiled.texts())))
                .path("modules").get(0).path("behaviors").get(0).path("partition");
    }

    @Test
    void theHelperTheCasesChooseAmongIsNamedBesideALineReadAllTheSameInTheDocumentAndInBothLanguages() {
        Compilation compiled = compiled(BETWEEN);
        AdequacyReport report = AdequacyReport.of(compiled);
        JsonNode partition = partition(compiled);

        assertTrue(partition.path("caseExpansions").isEmpty(),
                "every line is worked out: " + partition);
        assertFalse(partition.path("costlyReadings").isEmpty(), partition.toString());
        for (JsonNode costly : partition.path("costlyReadings")) {
            assertFalse(costly.has("case"), "no count of the cases: " + costly);
            for (JsonNode reading : costly.path("readings")) {
                assertFalse(reading.has("caseExpansion"), reading.toString());
                for (JsonNode helper : reading.path("helpers")) {
                    assertEquals("demo.isBusinessDay", helper.path("helper").asString());
                    for (JsonNode at : helper.path("madeAt")) {
                        assertEquals(List.of("demo.firstBusinessDay"),
                                JSON.convertValue(at.path("calledInside"), List.class), at.toString());
                    }
                }
            }
        }

        SourceRendering rendering = SourceRendering.namedByIdentity(compiled.texts());

        List<String> english = report.humanInEnglish(rendering).lines()
                .filter(line -> line.contains("many cases:")).toList();
        assertFalse(english.isEmpty());
        for (String line : english) {
            assertTrue(line.contains(". The helper `isBusinessDay` is read more than once")
                            && line.contains("the call written inside `firstBusinessDay` has to"
                            + " move into the `let` of the behavior itself"), line);
            assertFalse(line.contains("ways"), "no count of the cases: " + line);
        }
        List<String> japanese = report.human(rendering, Locale.JAPANESE).lines()
                .filter(line -> line.contains("ケースが多い行")).toList();
        assertFalse(japanese.isEmpty());
        for (String line : japanese) {
            assertTrue(line.contains("。ヘルパ `isBusinessDay` は複数回読まれ")
                    && line.contains("behavior 自身の `let` に移す必要があります"), line);
        }
    }

    @Test
    void aLineNotWorkedOutOrWithItsCasesWithinTheFigureHasNoEntryBesideIt() {
        JsonNode stopped = partition(compiled(0));
        assertFalse(stopped.path("caseExpansions").isEmpty(), stopped.toString());
        assertFalse(stopped.has("costlyReadings"), stopped.toString());

        JsonNode within = partition(compiled(
                CompositionBudget.CASES_A_LINE_IS_TAKEN_APART_INTO.maximum()));
        assertFalse(within.has("costlyReadings"), within.toString());
    }
}
