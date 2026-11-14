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

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Where a statement stops for a reason, the report says that reason, at the places the reason is
 * about, and never as a form this compiler does not read.
 *
 * <p>One case for each reason: the claim is which word is said and where, not how many shapes reach
 * it, and the shapes that reach it are the ones these two are the smallest of.
 */
class AStopIsSaidForWhatStoppedItNotForTheFormTest {

    /** {@code position reason} of each place the report of the first behavior says is not read,
     *  for the reasons this is about and for a form not read. */
    private static List<String> notReadOf(String source) {
        Compilation model = Compilation.ofSource(source, "Main");
        model.measure(Adequacy.Asked.reportOnly(Adequacy.Level.WITNESS));
        ACompiledModel.compiles(model);
        JsonNode report = new ObjectMapper().readTree(AdequacyReport.of(model)
                .json(SourceRendering.namedByIdentity(SourceLayouts.NONE)));
        List<String> out = new ArrayList<>();
        for (JsonNode each : report.path("modules").get(0).path("behaviors").get(0)
                .path("partition").path("notRead")) {
            String reason = each.path("reason").asString();
            if (reason.startsWith("rule_relating_two_elements")
                    || reason.endsWith("no_position_holds") || reason.equals("unsupported_syntax")) {
                out.add(each.path("position").asString() + " " + reason);
            }
        }
        return out.stream().sorted().distinct().toList();
    }

    /** A value chosen by a membership of a list and held to a membership of the same list: two
     *  elements of one list, at the elements and not at the list. */
    @Test
    void twoElementsOfOneListAreSaidAtTheElementsAndNotAtTheList() {
        assertEquals(List.of(
                        "hs[*] rule_relating_two_elements_of_one_container",
                        "ns[*] rule_relating_two_elements_of_one_container"),
                notReadOf("""
                        module i1

                        behavior f : (hs: List<Int>, ns: List<Int>) -> List<Int>
                        let f (hs, ns) =
                            ns
                                |> List.map(n -> if Bool.not(List.contains(n, hs)) then n else n + 1)
                                |> List.filter(d -> List.contains(d, hs))
                        """));
    }

    /** The weekday of a date a walk found, held to a bound, beside a membership of a set: the
     *  remainder is what stopped it, and the set is not named where its elements are. */
    @Test
    void theWeekdayOfADateAWalkFoundIsSaidAtTheNumbersItIsMadeOf() {
        assertEquals(List.of(
                        "c.aSunday rule_about_a_remainder_no_position_holds",
                        "c.holidays[*] rule_about_a_remainder_no_position_holds",
                        "from rule_about_a_remainder_no_position_holds"),
                notReadOf("""
                        module o1

                        data C = { holidays: Set<Date>, aSunday: Date }

                        let weekday (c: C, d: Date): Int =
                            Int.floorMod(Date.daysBetween(c.aSunday, d), 7)

                        let ok (c: C, d: Date): Bool =
                            weekday(c, d) >= 1 && Bool.not(Set.contains(d, c.holidays))

                        let first (c: C, from: Date): Date =
                            List.rangeInclusive(0, 1)
                                |> List.map(n -> Date.addDays(n, from))
                                |> List.find(d -> ok(c, d))
                                |> Option.withDefault(from)

                        behavior u : (c: C, from: Date, days: Int) -> List<Date>
                        let u (c, from, days) =
                            List.rangeInclusive(0, days)
                                |> List.map(n -> first(c, Date.addDays(n, from)))
                                |> List.filter(d -> Bool.not(ok(c, d)))
                        """));
    }
}
