package souther.compiler.report;

import org.junit.jupiter.api.Test;

import souther.compiler.DocumentShape;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * One clause of a type, read at two positions, holds a verdict open at each of them.
 *
 * <p>{@code Minutes} stands under a meeting and under a connected call, so each of its ends is a
 * line at both places: one rule, one line of the model, two places a row would be written. Where
 * the rows could not settle either, what holds the verdict open is said about each line. Named by
 * the line of the model alone, the two entries at one end were one identity under two labels, and
 * the order a document writes its entries in refused to choose between them.
 *
 * <p>The rows are what make the two readings come to nothing. A row holding a meeting and a call
 * has its values under one element for one reading and under the other for the other, and a row
 * listing them the other way round does the same from the other side — so at each place there is a
 * reading that met no value of its own.
 */
class ALineOfATypeReadAtTwoPositionsIsTwoEntriesTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    private static final String MODEL = """
            module probe.load

            data Minutes = Int
                invariant value >= 15 && value <= 480

            data Connected = { minutes: Minutes }
            data Voicemail
            data Outcome = Connected | Voicemail

            data Call = { outcome: Outcome }
            data Meeting = { minutes: Minutes }
            data Activity = Call | Meeting

            data Load = { total: Int }

            behavior tally : (activities: List<Activity>) -> Load
                constructs Load

            let minutesOf (a: Activity): Int =
                match a with
                    | Meeting as m -> m.minutes.value
                    | Call as c -> match c.outcome with
                        | Connected as k -> k.minutes.value
                        | Voicemail -> 0

            let tally (activities) =
                Load { total = List.fold((acc, a) -> acc + minutesOf(a), 0, activities) }

            example tally
                | "a meeting" : ([ Meeting { minutes = Minutes(30) } ]) -> Load { total = 30 }
                | "both" : ([ Meeting { minutes = Minutes(30) },
                              Call { outcome = Connected { minutes = Minutes(20) } } ])
                    -> Load { total = 50 }
                | "both, the call first" : ([ Call { outcome = Connected { minutes = Minutes(20) } },
                                              Meeting { minutes = Minutes(30) } ])
                    -> Load { total = 50 }
                | "a voicemail" : ([ Call { outcome = Voicemail } ]) -> Load { total = 0 }
            """;

    /**
     * Every line the clause draws holds the verdict open, each as an entry of its own, in the order
     * the document's identities put them in.
     */
    @Test
    void eachPlaceTheLineIsReadAtIsAnEntry() {
        JsonNode document = written();

        List<String> said = new ArrayList<>();
        for (JsonNode each : document.get("keptOpenBy")) {
            said.add(each.get("kind").asString() + " " + each.get("about").get("label").asString());
        }
        assertEquals(List.of(
                        "border_value_absent activities[*]@Call.outcome@Connected.minutes = 15",
                        "border_value_absent activities[*]@Call.outcome@Connected.minutes = 480",
                        "border_value_absent activities[*]@Meeting.minutes = 15",
                        "border_value_absent activities[*]@Meeting.minutes = 480"),
                said);
    }

    /**
     * The two entries at one end share the line of the model and differ in where it was drawn.
     *
     * <p>What the defect was, said as what the document now carries: the half both had was the whole
     * of what told them apart, and the half they differ in is written beside it.
     */
    @Test
    void theTwoAtOneEndAreOneLineOfTheModelAtTwoPlaces() {
        List<JsonNode> atFifteen = new ArrayList<>();
        for (JsonNode each : written().get("keptOpenBy")) {
            if (each.get("about").get("label").asString().endsWith("= 15")) {
                atFifteen.add(each.get("about").get("lineId"));
            }
        }
        assertEquals(2, atFifteen.size(), () -> "one entry per place: " + atFifteen);

        assertEquals(atFifteen.get(0).get("line"), atFifteen.get(1).get("line"),
                "one line of the model");
        assertNotEquals(atFifteen.get(0).get("target"), atFifteen.get(1).get("target"),
                "drawn at two places");
    }

    /**
     * Each line an entry holds the verdict open on is one of the behavior's boundaries, found by the
     * id both write; and no two boundaries are written under one id.
     */
    @Test
    void anEntryAboutALineJoinsTheBoundaryItIsAbout() {
        JsonNode document = written();
        List<JsonNode> boundaries = new ArrayList<>();
        document.get("modules").get(0).get("behaviors").get(0).get("partition").get("boundaries")
                .forEach(each -> boundaries.add(each.get("lineId")));
        assertEquals(boundaries.size(), new LinkedHashSet<>(boundaries).size(),
                () -> "a boundary per line: " + boundaries);

        for (JsonNode each : document.get("keptOpenBy")) {
            JsonNode lineId = each.get("about").get("lineId");
            assertEquals(1, boundaries.stream().filter(lineId::equals).count(),
                    () -> each.get("about").get("label") + " names one boundary: " + lineId);
        }
    }

    /** And the document is one the schema describes. */
    @Test
    void theDocumentIsShapedLikeTheSchema() {
        DocumentShape.assertShapedLikeTheSchema(written());
    }

    private static JsonNode written() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertTrue(compilation.errors().isEmpty(),
                () -> "a model that did not compile answers every question with nothing: "
                        + compilation.errors());
        return JSON.readTree(AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(compilation.texts())));
    }
}
