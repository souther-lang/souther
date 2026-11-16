package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import java.util.ArrayList;
import java.util.List;
import java.util.Locale;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A behavior whose measure went without a meeting it could not join to what a run records says
 * which meeting and why, on the page and in the document, and not only that the measure is partial.
 */
class AMeetingNotJoinedSaysWhyAndWhereOnThePageTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    /** The choice is made in one closure and written out again by another, so which evaluation is
     *  an element's is not known. */
    private static final String SOURCE = """
            module example.ways

            data Row = { days: Int, pay: Int }

            behavior total : (first: Row, second: Row) -> Int

            let total (first, second) =
                List.sum(List.flatMap(r -> [ r, r ], List.map(r -> if r.days >= 17
                    then r.pay else 0, [ first, second ])))

            example total
                | "both" : (Row { days = 20, pay = 5 }, Row { days = 20, pay = 7 }) -> 24
                | "neither" : (Row { days = 1, pay = 5 }, Row { days = 1, pay = 7 }) -> 0
            """;

    private static final Compilation COMPILATION =
            ACompiledModel.measured(SOURCE, Adequacy.Asked.fullReport());

    private static final SourceRendering RENDERING =
            SourceRendering.namedByIdentity(COMPILATION.texts());

    private static final AdequacyReport REPORT = AdequacyReport.of(COMPILATION);

    @Test
    void thePageNamesTheMeetingTheReasonAndWhereItIsWritten() {
        String human = REPORT.humanInEnglish(RENDERING);

        assertTrue(human.contains("meeting 1 is not joined to what a run records"), human);
        assertTrue(human.contains("which of its evaluations is the element's is not known"), human);
        assertTrue(human.contains("written at"), human);
    }

    @Test
    void theJapanesePageSaysItToo() {
        String human = REPORT.human(RENDERING, Locale.JAPANESE);

        assertTrue(human.contains("合流点 1"), human);
        assertFalse(human.contains("report."), "no entry is left unsaid: " + human);
    }

    @Test
    void theDocumentHoldsTheSameMeetingWithItsReasonAndPlace() {
        List<JsonNode> found = new ArrayList<>();
        find(JSON.readTree(REPORT.json(RENDERING)), "meetingsNotJoined", found);

        assertEquals(1, found.size(), "one behavior, one list of meetings");
        JsonNode meetings = found.getFirst();
        assertEquals(1, meetings.size());
        assertEquals("a_value_choice_not_numbered", meetings.get(0).get("why").asString());
        assertTrue(meetings.get(0).has("at"), "and where it is written");
    }

    private static void find(JsonNode node, String name, List<JsonNode> into) {
        if (node.isObject()) {
            node.properties().forEach(each -> {
                if (each.getKey().equals(name)) {
                    into.add(each.getValue());
                }
                find(each.getValue(), name, into);
            });
        } else if (node.isArray()) {
            node.forEach(one -> find(one, name, into));
        }
    }
}
