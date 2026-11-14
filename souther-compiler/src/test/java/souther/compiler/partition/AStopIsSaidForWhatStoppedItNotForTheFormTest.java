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
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Where a statement stops for a reason, the report says that reason, at the places the reason is
 * about, and never as a form this compiler does not read.
 *
 * <p>One case for each claim: which word is said and where, not how many shapes reach it, and the
 * shapes that reach it are the ones these are the smallest of.
 */
class AStopIsSaidForWhatStoppedItNotForTheFormTest {

    private static final String TWO_ELEMENTS = "rule_relating_two_elements_of_one_container";
    private static final String REMAINDER = "rule_about_a_remainder_no_position_holds";
    private static final String DERIVED = "rule_about_a_derived_value";

    private static final Set<String> THE_WORDS_THESE_ARE_ABOUT = Set.of(TWO_ELEMENTS, REMAINDER,
            "unsupported_syntax");

    /** {@code position reason} of each place the report of the first behavior says is not read,
     *  for {@code reasons} only. */
    private static List<String> notReadOf(String source, Set<String> reasons) {
        Compilation model = Compilation.ofSource(source, "Main");
        model.measure(Adequacy.Asked.reportOnly(Adequacy.Level.WITNESS));
        ACompiledModel.compiles(model);
        JsonNode report = new ObjectMapper().readTree(AdequacyReport.of(model)
                .json(SourceRendering.namedByIdentity(SourceLayouts.NONE)));
        List<String> out = new ArrayList<>();
        for (JsonNode each : report.path("modules").get(0).path("behaviors").get(0)
                .path("partition").path("notRead")) {
            String reason = each.path("reason").asString();
            if (reasons.contains(reason)) {
                out.add(each.path("position").asString() + " " + reason);
            }
        }
        return out.stream().sorted().distinct().toList();
    }

    /** A value chosen by a membership of a list and held to a membership of the same list: two
     *  elements of one list, at the elements and not at the list. */
    @Test
    void twoElementsOfOneListAreSaidAtTheElementsAndNotAtTheList() {
        assertEquals(List.of("hs[*] " + TWO_ELEMENTS, "ns[*] " + TWO_ELEMENTS),
                notReadOf("""
                        module i1

                        behavior f : (hs: List<Int>, ns: List<Int>) -> List<Int>
                        let f (hs, ns) =
                            ns
                                |> List.map(n -> if Bool.not(List.contains(n, hs)) then n else n + 1)
                                |> List.filter(d -> List.contains(d, hs))
                        """, THE_WORDS_THESE_ARE_ABOUT));
    }

    /** What a part that stopped for something a place words for itself says is the place's: the
     *  product is named, and the two elements are not said beside it. */
    @Test
    void aPartAPlaceWordsForItselfIsSaidBeforeTwoElementsOfOneList() {
        List<String> notRead = notReadOf("""
                module m

                behavior f : (hs: List<Int>, ns: List<Int>) -> List<Int>
                let f (hs, ns) =
                    ns
                        |> List.map(n -> if Bool.not(List.contains(n, hs)) then n else n + 1)
                        |> List.filter(d -> List.contains(d * d, hs))
                """, Set.of(TWO_ELEMENTS, "non_affine_product"));
        assertTrue(notRead.contains("hs[*] non_affine_product"), notRead.toString());
        assertTrue(notRead.contains("ns[*] non_affine_product"), notRead.toString());
        assertFalse(notRead.stream().anyMatch(each -> each.endsWith(" " + TWO_ELEMENTS)),
                notRead.toString());
    }

    private static final String A_WALK_OVER_DAYS = """
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
            """;

    /** The weekday of a date a walk found, held to a bound, beside a membership of a set: the
     *  remainder is what no line is drawn through, and the set is not named where its elements
     *  are. */
    @Test
    void theWeekdayOfADateAWalkFoundIsSaidAtTheNumbersItIsMadeOf() {
        assertEquals(List.of(
                        "c.aSunday " + REMAINDER,
                        "c.holidays[*] " + REMAINDER,
                        "from " + REMAINDER),
                notReadOf("""
                        module o1

                        data C = { holidays: Set<Date>, aSunday: Date }

                        let weekday (c: C, d: Date): Int =
                            Int.floorMod(Date.daysBetween(c.aSunday, d), 7)

                        let ok (c: C, d: Date): Bool =
                            weekday(c, d) >= 1 && Bool.not(Set.contains(d, c.holidays))

                        """ + A_WALK_OVER_DAYS, THE_WORDS_THESE_ARE_ABOUT));
    }

    /** A statement that states a remainder takes no place's own word from it: the set is made by
     *  an operation and says so, as it did before the remainder was named. */
    @Test
    void aPlaceKeepsTheWordItHasOfItsOwnWhereTheStatementStatesARemainder() {
        List<String> notRead = notReadOf("""
                module o1

                data C = { holidays: Set<Date>, aSunday: Date, name: String }

                let weekday (c: C, d: Date): Int =
                    Int.floorMod(Date.daysBetween(c.aSunday, d), 7)

                let ok (c: C, d: Date): Bool =
                    weekday(c, d) >= 1 && String.length(String.lowercase(c.name)) > 2
                        && Bool.not(Set.contains(d, c.holidays))

                """ + A_WALK_OVER_DAYS, Set.of(REMAINDER, DERIVED));
        assertTrue(notRead.contains("c.holidays " + DERIVED), notRead.toString());
        assertFalse(notRead.contains("c.holidays " + REMAINDER), notRead.toString());
    }
}
