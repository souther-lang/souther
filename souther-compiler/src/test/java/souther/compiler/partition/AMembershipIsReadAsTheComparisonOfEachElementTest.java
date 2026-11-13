package souther.compiler.partition;

import org.junit.jupiter.api.Test;
import tools.jackson.databind.JsonNode;
import tools.jackson.databind.ObjectMapper;

import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * {@code List.contains(v, xs)} says some element of {@code xs} is {@code v}, which is what
 * {@code List.any(own -> own == v, xs)} says: the two are one comparison of each element with
 * {@code v}, and a report of the one is the report of the other, a conversion of {@code v}
 * included.
 */
class AMembershipIsReadAsTheComparisonOfEachElementTest {

    private static final String VALUE = "email";

    private static final String CONVERTED = "String.lowercase(email)";

    private static JsonNode partitionOf(String body) {
        String source = """
                module m

                data E = String invariant String.length(value) <= 254

                behavior f : (email: E, emails: List<String>) -> Bool
                let f (E(email), emails) =
                    %s

                example f
                    | "a" : (E("a"), [ "a" ]) -> true
                """.formatted(body);
        Compilation model = ACompiledModel.measured(source,
                Adequacy.Asked.reportOnly(Adequacy.Level.WITNESS));
        JsonNode report = new ObjectMapper().readTree(AdequacyReport.of(model)
                .json(SourceRendering.namedByIdentity(SourceLayouts.NONE)));
        return report.path("modules").get(0).path("behaviors").get(0).path("partition");
    }

    private static String any(String value) {
        return "List.any(own -> own == " + value + ", emails)";
    }

    private static String contains(String value) {
        return "List.contains(" + value + ", emails)";
    }

    @Test
    void aValueIsReadAsTheComparisonOfEachElementWithIt() {
        assertEquals(partitionOf(any(VALUE)), partitionOf(contains(VALUE)));
    }

    @Test
    void aConvertedValueIsReadAsTheComparisonOfEachElementWithIt() {
        assertEquals(partitionOf(any(CONVERTED)), partitionOf(contains(CONVERTED)));
    }

    /** What an element is compared with is told of the places that stand in the comparison, so a
     *  comparison of the elements is never reported as dividing no place. */
    @Test
    void aMembershipTestOfAConvertedValueDividesTheElements() {
        JsonNode partition = partitionOf(contains(CONVERTED));
        assertFalse(partition.path("axes").isEmpty(), partition.toString());
        assertTrue(partition.path("unanswered").toString().contains("emails[*]"),
                partition.toString());
    }
}
