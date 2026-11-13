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
import java.util.Collections;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * {@code List.contains(v, xs)} says some element of {@code xs} is {@code v}, which is what
 * {@code List.any(own -> own == v, xs)} says: the two are one comparison of each element with
 * {@code v}, and what the partition says of the one it says of the other, whatever {@code v} is
 * and whichever of an element or a key of a container the law names.
 *
 * <p>What is held is what the report says: the places divided and how, what is left unanswered,
 * what is not read and why, and whether the divisions are whole. So a comparison that cannot be
 * read is said unread at the places it compares, as it is where it is written, and is never an
 * application that divides no place.
 */
class AMembershipIsReadAsTheComparisonOfEachElementTest {

    private static final String SOURCE = """
            module m

            data E = String invariant String.length(value) <= 254
            data Rec = { tags: List<String>, label: String }

            behavior f : (email: String, emails: List<String>, sset: Set<String>, n: Int,
                          ns: List<Int>, ds: Set<Int>, mp: Map<String, Int>, ks: List<String>,
                          rec: Rec, rs: List<Rec>, e: E, es: List<E>, d: Date,
                          dates: List<Date>, b: Bool) -> Bool
            let f (email, emails, sset, n, ns, ds, mp, ks, rec, rs, e, es, d, dates, b) =
                %s
            """;

    /** What the report of {@code body} says of the partition, with what is not an answer — the
     *  rules' names and their order — left out. */
    private static String reportOf(String body) {
        Compilation model = Compilation.ofSource(SOURCE.formatted(body), "Main");
        model.measure(Adequacy.Asked.reportOnly(Adequacy.Level.WITNESS));
        ACompiledModel.compiles(model);
        JsonNode report = new ObjectMapper().readTree(AdequacyReport.of(model)
                .json(SourceRendering.namedByIdentity(SourceLayouts.NONE)));
        JsonNode partition = report.path("modules").get(0).path("behaviors").get(0)
                .path("partition");
        List<String> axes = new ArrayList<>();
        for (JsonNode axis : partition.path("axes")) {
            axes.add(axis.path("path").asString() + "=" + axis.path("read").path("extent")
                    .asString() + axis.path("classes"));
        }
        List<String> unanswered = new ArrayList<>();
        for (JsonNode each : partition.path("unanswered")) {
            unanswered.add(each.path("at").asString() + ":" + each.path("question").asString()
                    + ":" + each.path("stopped").findValuesAsString("reason"));
        }
        List<String> notRead = new ArrayList<>();
        for (JsonNode each : partition.path("notRead")) {
            notRead.add(each.path("position").asString() + ":" + each.path("reason").asString());
        }
        List<String> notDerivable = new ArrayList<>();
        partition.path("notDerivable").forEach(each -> notDerivable.add(each.asString()));
        for (List<String> each : List.of(axes, unanswered, notRead, notDerivable)) {
            Collections.sort(each);
        }
        return partition.path("axesMeasure").path("status").asString() + " axes " + axes
                + " unanswered " + unanswered + " notRead " + notRead + " notDerivable "
                + notDerivable;
    }

    private static void sameAs(String membership, String comparison) {
        assertEquals(reportOf(comparison), reportOf(membership),
                membership + " beside " + comparison);
    }

    @Test
    void aValueAtAPlaceAndAConvertedOneAreReadAsTheComparisonOfEachElementWithIt() {
        for (String value : List.of("email", "String.lowercase(email)", "\"lit\"",
                "rec.label")) {
            sameAs("List.contains(" + value + ", emails)",
                    "List.any(own -> own == " + value + ", emails)");
        }
    }

    @Test
    void aSetAndAKeyAreReadAsTheListIs() {
        for (String value : List.of("email", "String.lowercase(email)",
                "String.append(email, \"x\")")) {
            sameAs("Set.contains(" + value + ", sset)",
                    "List.any(own -> own == " + value + ", Set.toList(sset))");
            sameAs("Map.containsKey(" + value + ", mp)",
                    "List.any(own -> own == " + value + ", Map.keys(mp))");
        }
    }

    @Test
    void aNumberAndADateAreReadAsTheComparisonOfEachElementWithIt() {
        for (String value : List.of("n", "n + 1", "Int.floorMod(n, 7)", "List.length(ns)")) {
            sameAs("List.contains(" + value + ", ns)",
                    "List.any(own -> own == " + value + ", ns)");
            sameAs("Set.contains(" + value + ", ds)",
                    "List.any(own -> own == " + value + ", Set.toList(ds))");
        }
        sameAs("List.contains(Date.addDays(1, d), dates)",
                "List.any(own -> own == Date.addDays(1, d), dates)");
        sameAs("List.contains(d, dates)", "List.any(own -> own == d, dates)");
    }

    /**
     * A value no reading of the comparison can take apart leaves the comparison unread, and the
     * places it compares are told so: the elements of the container, and the places the value
     * is made of.
     */
    @Test
    void aComparisonNoReadingTookToTheEndIsSaidUnreadAtThePlacesItComparesAndNeverComplete() {
        for (String container : List.of("emails", "rec.tags")) {
            String report = reportOf("List.contains(String.append(email, \"x\"), " + container
                    + ")");
            assertTrue(report.contains(container + "[*]:unsupported_syntax"), report);
            assertTrue(report.contains("email:rule_about_a_derived_value"), report);
            assertFalse(report.startsWith("complete"), report);
            sameAs("List.contains(String.append(email, \"x\"), " + container + ")",
                    "List.any(own -> own == String.append(email, \"x\"), " + container + ")");
        }
        sameAs("Set.contains(String.append(email, \"x\"), sset)",
                "List.any(own -> own == String.append(email, \"x\"), Set.toList(sset))");
    }

    /**
     * Some element of a list meeting a statement about another element of the same list is read
     * as the comparison of the two is, and said unread: two elements of one container are not
     * two places.
     */
    @Test
    void anElementHeldAgainstAnotherOfTheSameListIsSaidUnreadWhereTheComparisonIs() {
        String report = reportOf("List.any(k -> List.contains(k + 1, ns), ns)");
        assertTrue(report.contains("ns[*]:unsupported_syntax"), report);
        assertFalse(report.startsWith("complete"), report);
        sameAs("List.any(k -> List.contains(k + 1, ns), ns)",
                "List.any(k -> List.any(own -> own == k + 1, ns), ns)");
        sameAs("List.any(k -> List.contains(String.lowercase(k), emails), ks)",
                "List.any(k -> List.any(own -> own == String.lowercase(k), emails), ks)");
    }

    @Test
    void theOtherPolarityAndTheQuantifiersAroundAreReadAsTheComparisonsAre() {
        for (String value : List.of("email", "String.lowercase(email)", "\"lit\"")) {
            sameAs("Bool.not(List.contains(" + value + ", emails))",
                    "List.all(own -> own /= " + value + ", emails)");
        }
        sameAs("Bool.not(List.contains(n, ns))", "List.all(own -> own /= n, ns)");
        sameAs("List.contains(email, emails) && List.contains(rec.label, emails)",
                "List.any(own -> own == email, emails) && List.any(own -> own == rec.label, emails)");
        sameAs("List.any(r -> List.contains(r.label, emails), rs)",
                "List.any(r -> List.any(own -> own == r.label, emails), rs)");
        sameAs("n > 0 && List.contains(n, ns)", "n > 0 && List.any(own -> own == n, ns)");
        sameAs("List.contains(e, es)", "List.any(own -> own == e, es)");
    }

    /**
     * The element a law names is one element of one container at one call: two memberships of one
     * value in two lists name two elements, each divided at its own list, and two of one list at
     * two calls are two as well.
     */
    @Test
    void eachMembershipNamesTheElementOfItsOwnContainerAtItsOwnCall() {
        String both = reportOf("List.contains(email, emails) && List.contains(email, ks)");
        assertTrue(both.contains("emails[*]:"), both);
        assertTrue(both.contains("ks[*]:"), both);
        sameAs("List.contains(email, emails) && List.contains(email, ks)",
                "List.any(own -> own == email, emails) && List.any(own -> own == email, ks)");
        sameAs("List.contains(email, emails) && List.contains(String.lowercase(email), emails)",
                "List.any(own -> own == email, emails)"
                        + " && List.any(own -> own == String.lowercase(email), emails)");
        sameAs("Bool.not(List.contains(email, emails)) && List.contains(email, ks)",
                "List.all(own -> own /= email, emails) && List.any(own -> own == email, ks)");
        sameAs("List.contains(email, emails) && List.contains(n, ns)"
                        + " && Set.contains(email, sset)",
                "List.any(own -> own == email, emails) && List.any(own -> own == n, ns)"
                        + " && List.any(own -> own == email, Set.toList(sset))");
    }

    /** What an element is compared with is told of the places that stand in the comparison, so a
     *  comparison of the elements is never reported as dividing no place. */
    @Test
    void aMembershipTestOfAConvertedValueDividesTheElements() {
        String report = reportOf("List.contains(String.lowercase(email), emails)");
        assertTrue(report.contains("emails[*]=complete[\"emails[*]: x can be "
                + "String.lowercase(email)\",\"emails[*]: x is never String.lowercase(email)\"]"),
                report);
    }
}
