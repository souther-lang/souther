package souther.compiler.partition;

import org.junit.jupiter.api.Test;
import tools.jackson.databind.JsonNode;
import tools.jackson.databind.ObjectMapper;

import souther.compiler.ACompiledModel;
import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.ArrayList;
import java.util.List;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * Where a statement stops for a reason, the report says that reason, at the places the reason is
 * about. A comparison written in a form this compiler reads is not said to be in a form it does not.
 *
 * <p>A membership of each element of a mapped list, chosen by a test on the same container, needs
 * two elements of one container; and the weekday of a date a walk found is a remainder of a number
 * no position holds. Both stopped the reading, and both were reported as a form not read, at the
 * container as well as at its elements.
 */
class AStopIsSaidForWhatStoppedItNotForTheFormTest {

    private static final String TWO_ELEMENTS = "rule_relating_two_elements_of_one_container";
    private static final String REMAINDER = "rule_about_a_remainder_no_position_holds";

    /** {@code position reason} of each place the report of the first behavior says is not read. */
    private static List<String> notReadOf(String source) {
        Compilation model = Compilation.ofSource(source, "Main");
        model.measure(Adequacy.Asked.reportOnly(Adequacy.Level.WITNESS));
        ACompiledModel.compiles(model);
        JsonNode report = new ObjectMapper().readTree(AdequacyReport.of(model)
                .json(SourceRendering.namedByIdentity(SourceLayouts.NONE)));
        List<String> out = new ArrayList<>();
        for (JsonNode each : report.path("modules").get(0).path("behaviors").get(0)
                .path("partition").path("notRead")) {
            out.add(each.path("position").asString() + " " + each.path("reason").asString());
        }
        return out;
    }

    private static List<String> saying(List<String> notRead, String reason) {
        return new ArrayList<>(new TreeSet<>(notRead.stream()
                .filter(each -> each.endsWith(" " + reason)).toList()));
    }

    private static String membership(String container, String contains, String value) {
        return """
                module i1

                behavior f : (hs: %s<Int>, ns: List<Int>) -> List<Int>
                let f (hs, ns) =
                    ns
                        |> List.map(n -> if Bool.not(%s) then n else n + 1)
                        |> List.filter(d -> %s)
                """.formatted(container, contains, value);
    }

    @Test
    void aMembershipOfEachMappedValueChosenByAMembershipOfTheSameListIsTwoElementsOfOneList() {
        List<String> notRead = notReadOf(membership("List", "List.contains(n, hs)",
                "List.contains(d, hs)"));
        assertEquals(List.of("hs[*] " + TWO_ELEMENTS, "ns[*] " + TWO_ELEMENTS),
                saying(notRead, TWO_ELEMENTS));
        assertFalse(notRead.contains("hs unsupported_syntax"), notRead.toString());
        assertEquals(List.of(), saying(notRead, "unsupported_syntax"), notRead.toString());
    }

    @Test
    void theSameWithAnyAndWithASetIsSaidTheSame() {
        List<String> list = notReadOf(membership("List", "List.contains(n, hs)",
                "List.contains(d, hs)"));
        assertEquals(saying(list, TWO_ELEMENTS), saying(notReadOf(membership("List",
                "List.any(k -> k == n, hs)", "List.any(h -> h == d, hs)")), TWO_ELEMENTS));
        assertEquals(saying(list, TWO_ELEMENTS), saying(notReadOf(membership("Set",
                "Set.contains(n, hs)", "Set.contains(d, hs)")), TWO_ELEMENTS));
    }

    @Test
    void theWeekdayOfADateAWalkFoundIsARemainderNoPositionHolds() {
        List<String> notRead = notReadOf("""
                module o1

                data PaymentCalendar = { holidays: Set<Date>, aSunday: Date }

                let weekday (calendar: PaymentCalendar, d: Date): Int =
                    Int.floorMod(Date.daysBetween(calendar.aSunday, d), 7)

                let isBusinessDay (calendar: PaymentCalendar, d: Date): Bool =
                    weekday(calendar, d) >= 1 && weekday(calendar, d) <= 5
                        && Bool.not(Set.contains(d, calendar.holidays))

                let firstBusinessDay (calendar: PaymentCalendar, from: Date): Date =
                    List.rangeInclusive(0, 1)
                        |> List.map(n -> Date.addDays(n, from))
                        |> List.find(d -> isBusinessDay(calendar, d))
                        |> Option.withDefault(from)

                behavior unpayable : (calendar: PaymentCalendar, from: Date, days: Int)
                        -> List<Date>
                let unpayable (calendar, from, days) =
                    List.rangeInclusive(0, days)
                        |> List.map(n -> firstBusinessDay(calendar, Date.addDays(n, from)))
                        |> List.filter(d -> Bool.not(isBusinessDay(calendar, d)))
                """);
        assertEquals(List.of("calendar.aSunday " + REMAINDER, "calendar.holidays[*] " + REMAINDER,
                "from " + REMAINDER), saying(notRead, REMAINDER));
        assertEquals(List.of(), saying(notRead, "unsupported_syntax"), notRead.toString());
        assertFalse(notRead.stream().anyMatch(each -> each.startsWith("calendar.holidays ")),
                notRead.toString());
    }
}
