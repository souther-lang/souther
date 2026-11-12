package souther.compiler.partition;

import org.junit.jupiter.api.Test;
import tools.jackson.databind.JsonNode;
import tools.jackson.databind.ObjectMapper;

import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * An exact equality on the right of {@code ||} is reached only past the left, which lowercases the
 * same string inside a closure over another list. A row holding that list empty works out no
 * conversion, and the equality is reached at every string — so no string of either of its places
 * is left open for the conversion. Where a rule holds the list to an entry, the conversion is
 * worked out on every run that gets there, and the strings it is not exact on stay open.
 */
class AnEqualityPastAConversionARowNeedNotWorkOutIsReadTest {

    private static final String FREE = """
            module free

            behavior f : (email: String, domains: List<String>, emails: List<String>) -> Bool
            let f (email, domains, emails) =
                List.any(own -> own == String.lowercase(email), domains)
                    || List.any(own -> own == email, emails)

            example f
                | "domain" : ("a.com", [ "a.com" ], []) -> true
                | "email"  : ("x@b.com", [], [ "x@b.com" ]) -> true
                | "none"   : ("x@b.com", [ "a.com" ], [ "y@b.com" ]) -> false
            """;

    private static final String HELD = """
            module held

            data Domains = List<String> invariant List.length(value) >= 1

            behavior f : (email: String, domains: Domains, emails: List<String>) -> Bool
            let f (email, Domains(domains), emails) =
                List.any(own -> own == String.lowercase(email), domains)
                    || List.any(own -> own == email, emails)

            example f
                | "domain" : ("a.com", Domains([ "a.com" ]), []) -> true
                | "email"  : ("x@b.com", Domains([ "q" ]), [ "x@b.com" ]) -> true
                | "none"   : ("x@b.com", Domains([ "a.com" ]), [ "y@b.com" ]) -> false
            """;

    /**
     * The same equality over two lists of one record, with {@code rule} the record's invariant:
     * where it ties the lists, a row holding the one the conversion is worked out over empty
     * may break it beside the entry the other holds for the equality to be reached at.
     */
    private static String paired(String rule) {
        return """
                module paired

                data Pair = { domains: List<String>, emails: List<String> }%s

                behavior f : (email: String, pair: Pair) -> Bool
                let f (email, pair) =
                    List.any(own -> own == String.lowercase(email), pair.domains)
                        || List.any(own -> own == email, pair.emails)

                example f
                    | "domain" : ("a.com", Pair { domains = [ "a.com" ], emails = [ "q" ] }) -> true
                    | "email"  : ("x@b.com", Pair { domains = [ "q" ], emails = [ "x@b.com" ] }) -> true
                    | "none"   : ("x@b.com", Pair { domains = [ "a.com" ], emails = [ "y@b.com" ] }) -> false
                """.formatted(rule);
    }

    /** The places of {@code source}'s behavior a region is left open at, by what the report
     *  asks of them. */
    private static List<String> leftOpenIn(String source) {
        Compilation model = Compilation.ofSource(source, "Main");
        model.measure(Adequacy.Asked.reportOnly(Adequacy.Level.WITNESS));
        model.answerEverything();
        assertEquals(List.of(), model.errors().stream()
                .map(e -> e.diagnostic().code()).toList(), "the model compiles");
        JsonNode report = new ObjectMapper().readTree(AdequacyReport.of(model)
                .json(SourceRendering.namedByIdentity(SourceLayouts.NONE)));
        List<String> open = new ArrayList<>();
        for (JsonNode module : report.path("modules")) {
            for (JsonNode behavior : module.path("behaviors")) {
                for (JsonNode each : behavior.path("partition").path("unanswered")) {
                    if (each.path("question").asString().equals("regionNotDetermined")) {
                        open.add(each.path("subject").path("path").asString());
                    }
                }
            }
        }
        return open;
    }

    @Test
    void theEqualityIsReachedAtEveryStringWhereTheListMayBeEmpty() {
        List<String> open = leftOpenIn(FREE);
        assertTrue(!open.contains("email") && !open.contains("emails[*]"), open.toString());
    }

    @Test
    void theStringsTheConversionIsNotExactOnStayOpenWhereTheListHoldsOne() {
        List<String> open = leftOpenIn(HELD);
        assertTrue(open.contains("email") && open.contains("emails[*]"), open.toString());
    }

    @Test
    void listsOfOneRecordNoRuleTiesAreReadAsListsApart() {
        List<String> open = leftOpenIn(paired(""));
        assertTrue(!open.contains("email") && !open.contains("pair.emails[*]"), open.toString());
    }

    /** As long as each other: an entry for the equality is an entry to work the conversion over. */
    @Test
    void theStringsStayOpenWhereARuleHoldsTheListsToOneLength() {
        List<String> open = leftOpenIn(paired(
                "\n    invariant List.length(domains) == List.length(emails)"));
        assertTrue(open.contains("email") && open.contains("pair.emails[*]"), open.toString());
    }

    /**
     * The same said as a choice, which the region holds as no bound on either list alone: the tie
     * is the rule's, and a row emptying the one beside the other's entry breaks it.
     */
    @Test
    void theStringsStayOpenWhereARuleSaysTheOtherHoldsOneWhereThisDoes() {
        List<String> open = leftOpenIn(paired(
                "\n    invariant List.length(emails) == 0 || List.length(domains) >= 1"));
        assertTrue(open.contains("email") && open.contains("pair.emails[*]"), open.toString());
    }
}
