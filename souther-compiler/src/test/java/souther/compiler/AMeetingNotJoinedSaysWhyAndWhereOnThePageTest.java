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
 * A behavior whose measure went without meetings it could not join to what a run records says which
 * meetings, why, and where each is written, on the page and in the document, and not only that the
 * measure is partial.
 *
 * <p>Two meetings of different reasons, so what is held is that each reason is the one of the
 * meeting it is said beside, in the order the walk met them, at the place the meeting is written
 * — and that the page and the document say the same place.
 */
class AMeetingNotJoinedSaysWhyAndWhereOnThePageTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    /** The choice of the first is made in one closure and written out again by another, so which
     *  evaluation is an element's is not known. The second is kept by what is no comparison. */
    private static final String SOURCE = """
            module example.ways

            data Row = { days: Int, pay: Int, active: Bool }

            behavior total : (first: Row, second: Row) -> Int

            let total (first, second) =
                List.sum(List.flatMap(r -> [ r, r ], List.map(r -> if r.days >= 17
                    then r.pay else 0, [ first, second ])))
                + List.length(List.filter(r -> r.active, [ first, second ]))

            example total
                | "both" : (Row { days = 20, pay = 5, active = true },
                            Row { days = 20, pay = 7, active = true }) -> 26
            """;

    private static final Compilation COMPILATION =
            ACompiledModel.measured(SOURCE, Adequacy.Asked.fullReport());

    private static final SourceRendering RENDERING =
            SourceRendering.namedByIdentity(COMPILATION.texts());

    private static final AdequacyReport REPORT = AdequacyReport.of(COMPILATION);

    /** Where the meetings are written, read off the source and not written down beside it. */
    private static final String FIRST_AT = positionOf("List.sum(");

    private static final String SECOND_AT = positionOf("List.length(");

    /** The line and column, counted from 1, of the first place {@code written} stands in the
     *  source. */
    private static String positionOf(String written) {
        int offset = SOURCE.indexOf(written);
        assertTrue(offset >= 0, written);
        String before = SOURCE.substring(0, offset);
        int line = (int) before.chars().filter(c -> c == '\n').count() + 1;
        int column = offset - before.lastIndexOf('\n');
        return line + ":" + column;
    }

    @Test
    void thePageSaysEachMeetingAtItsPlaceWithItsOwnReasonInTheOrderMet() {
        List<String> lines = REPORT.humanInEnglish(RENDERING).lines()
                .filter(line -> line.contains("is not joined to what a run records")).toList();

        assertEquals(2, lines.size(), String.valueOf(lines));
        assertTrue(lines.get(0).contains("meeting 1 ")
                        && lines.get(0).contains("written at " + FIRST_AT + ":")
                        && lines.get(0).contains("which of its evaluations is the element's"),
                lines.get(0));
        assertTrue(lines.get(1).contains("meeting 2 ")
                        && lines.get(1).contains("written at " + SECOND_AT + ":")
                        && lines.get(1).contains("what keeps an element is not a comparison"),
                lines.get(1));
    }

    @Test
    void theHeadingSaysTheCountLeavesThemOut() {
        String human = REPORT.humanInEnglish(RENDERING);

        assertTrue(human.lines().anyMatch(line -> line.contains("interaction combinations")
                        && line.endsWith("2 meetings not joined")),
                human);
    }

    @Test
    void theBehaviorSaysWhatItWentWithout() {
        String human = REPORT.humanInEnglish(RENDERING);

        assertTrue(human.contains("partial: a meeting of the body's decisions was not joined"),
                human);
    }

    @Test
    void theJapanesePageSaysItToo() {
        String human = REPORT.human(RENDERING, Locale.JAPANESE);

        assertTrue(human.contains("合流点 1"), human);
        assertTrue(human.contains("合流点 2"), human);
        assertFalse(human.contains("report."), "no entry is left unsaid: " + human);
        assertFalse(human.contains("kind."), "no phrase is left unsaid: " + human);
    }

    @Test
    void theDocumentHoldsTheSameMeetingsWithTheirReasonsAndPlaces() {
        JsonNode document = JSON.readTree(REPORT.json(RENDERING));
        List<JsonNode> found = new ArrayList<>();
        find(document, "meetingsNotJoined", found);

        assertEquals(1, found.size(), "one behavior, one list of meetings");
        JsonNode meetings = found.getFirst();
        assertEquals(2, meetings.size());
        assertEquals("a_value_choice_not_numbered", meetings.get(0).get("why").asString());
        assertEquals(FIRST_AT, placeOf(meetings.get(0)));
        assertEquals("not_one_comparison", meetings.get(1).get("why").asString());
        assertEquals(SECOND_AT, placeOf(meetings.get(1)));
        EveryObjectThisWritesIsShapedTheWayTheSchemaSaysTest.assertShapedLikeTheSchema(document);
    }

    /** {@code line:column} of the place a meeting of the document is written at. */
    private static String placeOf(JsonNode meeting) {
        JsonNode at = meeting.get("at");
        return at.get("line").asInt() + ":" + at.get("column").asInt();
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
