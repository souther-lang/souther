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

    /** A comparison beside the membership in the search that chose the value is no reason for the
     *  report to be refused: it is the same two elements of one list, said the same. */
    @Test
    void aComparisonBesideTheMembershipThatChoseTheValueIsReportedNotRefused() {
        assertEquals(List.of("hs[*] " + TWO_ELEMENTS, "ns[*] " + TWO_ELEMENTS),
                notReadOf("""
                        module m

                        behavior f : (hs: List<Int>, ns: List<Int>) -> List<Int>
                        let f (hs, ns) =
                            ns
                                |> List.map(n -> [ n, n + 1 ]
                                    |> List.find(x -> x > 0 && Bool.not(List.contains(x, hs)))
                                    |> Option.withDefault(n))
                                |> List.filter(d -> List.contains(d, hs))
                        """, THE_WORDS_THESE_ARE_ABOUT));
    }

    /** A test of the value beside the membership that chose it, and the membership written as
     *  {@code List.any} or as {@code Set.contains}, are the same two elements of one container
     *  said the same: the report is made, with no place left to an internal error. */
    @Test
    void theFormTheMembershipIsWrittenInChangesWhatIsSaidNeitherInWordNorPlace() {
        assertEquals(List.of("hs[*] " + TWO_ELEMENTS, "ns[*] " + TWO_ELEMENTS),
                notReadOf("""
                        module h7

                        behavior f : (hs: List<Int>, ns: List<Int>) -> List<Int>
                        let f (hs, ns) =
                            ns
                                |> List.map(n -> if n >= 1 && Bool.not(List.any(k -> k == n, hs)) then n else n + 1)
                                |> List.filter(d -> List.any(h -> h == d, hs))
                        """, THE_WORDS_THESE_ARE_ABOUT));
        assertEquals(List.of("hs[*] " + TWO_ELEMENTS, "ns[*] " + TWO_ELEMENTS),
                notReadOf("""
                        module h7

                        behavior f : (hs: Set<Int>, ns: List<Int>) -> List<Int>
                        let f (hs, ns) =
                            ns
                                |> List.map(n -> if n >= 1 && Set.contains(n, hs) then n else n + 1)
                                |> List.filter(d -> Set.contains(d, hs))
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

    /** The weekday of a date a walk found, held to a bound, beside a membership of a set and the
     *  length of a lowercased name. The remainder is what no line is drawn through, said at the
     *  numbers it is made of; a place that has a word of its own keeps it, and the set is not
     *  named as a place where its elements are.
     *
     *  <p>One model for these claims, since the walk over days is what the test costs. */
    @Test
    void theWeekdayOfADateAWalkFoundIsSaidAtTheNumbersItIsMadeOfAndNoPlaceLosesItsOwnWord() {
        List<String> notRead = notReadOf("""
                module o1

                data C = { holidays: Set<Date>, aSunday: Date, name: String }

                let weekday (c: C, d: Date): Int =
                    Int.floorMod(Date.daysBetween(c.aSunday, d), 7)

                let ok (c: C, d: Date): Bool =
                    weekday(c, d) >= 1 && String.length(String.lowercase(c.name)) > 2
                        && Bool.not(Set.contains(d, c.holidays))

                """ + A_WALK_OVER_DAYS, Set.of(REMAINDER, DERIVED));
        assertTrue(notRead.containsAll(List.of("c.aSunday " + REMAINDER,
                "c.holidays[*] " + REMAINDER, "from " + REMAINDER)), notRead.toString());
        assertTrue(notRead.contains("c.holidays " + DERIVED), notRead.toString());
        assertFalse(notRead.contains("c.holidays " + REMAINDER), notRead.toString());
    }

    /** What is left unread is said at the elements and not at their container, and the container
     *  still holds its own measure open: the length of {@code hs} is not told apart on what a
     *  statement over its elements leaves unread, so it is not said to be read to the end. */
    @Test
    void theContainerIsNotSaidUnreadButItsMeasureIsStillHeldOpen() {
        Compilation model = Compilation.ofSource("""
                module m

                behavior f : (hs: List<Int>, ns: List<Int>) -> List<Int>
                let f (hs, ns) =
                    if List.length(hs) >= 2 then
                        ns
                            |> List.map(n -> if Bool.not(List.contains(n, hs)) then n else n + 1)
                            |> List.filter(d -> List.contains(d, hs))
                    else [ ]
                """, "Main");
        model.measure(Adequacy.Asked.reportOnly(Adequacy.Level.WITNESS));
        ACompiledModel.compiles(model);
        JsonNode partition = new ObjectMapper().readTree(AdequacyReport.of(model)
                .json(SourceRendering.namedByIdentity(SourceLayouts.NONE)))
                .path("modules").get(0).path("behaviors").get(0).path("partition");

        List<String> extents = new ArrayList<>();
        for (JsonNode axis : partition.path("axes")) {
            extents.add(axis.path("path").asString() + " " + axis.path("read").path("extent")
                    .asString());
        }
        assertEquals(List.of("List.length(hs) partial"), extents);

        List<String> unanswered = new ArrayList<>();
        for (JsonNode each : partition.path("unanswered")) {
            unanswered.add(each.path("at").asString());
        }
        assertTrue(unanswered.contains("hs"), unanswered.toString());

        for (JsonNode each : partition.path("notRead")) {
            assertFalse(each.path("position").asString().equals("hs"), each.toString());
        }
    }
}
