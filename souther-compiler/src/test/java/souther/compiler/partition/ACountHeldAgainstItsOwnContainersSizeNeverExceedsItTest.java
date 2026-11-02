package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * How many elements of a container meet a statement, less how many the container holds, is never
 * above nought, so a point of the border above it is excluded by what the quantity can hold and
 * not left to a search.
 *
 * <p>That is a claim about the quantity and nothing else. The size of another container leaves it
 * unbounded, and a level the quantity can hold is still owed whatever the bound on the other side
 * of it. The tests read each point of the border drawn on the count, as the structured report
 * gives it, and say which are excluded and which are owed.
 */
class ACountHeldAgainstItsOwnContainersSizeNeverExceedsItTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    private static final String EXCLUDED = "no_value_can_stand_there";

    private static String model(String guard, String moreRows) {
        return """
                module probe.count exposing ( check, Deal, Code, Table, Ok, Short )

                data Code = String
                    invariant String.matches("[A-Z]{3}", value)

                data Deal = { currency: Code }

                data Table = { rates: Map<Code, Int> }

                data Ok
                data Short

                behavior check : (deals: List<Deal>, others: List<Deal>, table: Table) -> Ok | Short

                let check (deals, others, table) = {
                    let priced = List.filterMap(d -> Map.get(d.currency, table.rates), deals)
                    if %s then Ok else Short
                }

                let usd = Deal { currency = Code("USD") }
                let eur = Deal { currency = Code("EUR") }
                let known = Table { rates = Map.fromList([ (Code("USD"), 1) ]) }

                example check
                    | "all priced" : ([ usd ], [ usd ], known) -> Ok
                    | "none" : ([ ], [ ], known) -> Ok
                    | "one missing" : ([ usd, eur ], [ usd, eur ], known) -> Short
                %s
                """.formatted(guard, moreRows);
    }

    private static Compilation measured(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation;
    }

    /**
     * Each point of the border drawn on the count, as {@code point:excluded} where the quantity
     * holds no value there and {@code point:owed <level> hit|unhit} where it is owed, by whether a
     * row stands at it.
     */
    private static List<String> pointsOf(String guard, String moreRows) {
        Compilation compilation = measured(model(guard, moreRows));
        JsonNode document = JSON.readTree(AdequacyReport.of(compilation).json(
                SourceRendering.namedByIdentity(compilation.texts())));
        List<String> out = new ArrayList<>();
        for (JsonNode module : document.get("modules")) {
            for (JsonNode behavior : module.get("behaviors")) {
                for (JsonNode boundary : behavior.get("partition").get("boundaries")) {
                    if (!boundary.get("lineId").toString().contains("#deals")) {
                        continue;
                    }
                    for (JsonNode item : boundary.get("items")) {
                        String point = item.get("point").asString();
                        if (item.has("notOwed")) {
                            out.add(point + ":" + (item.get("notOwed").asString().equals(EXCLUDED)
                                    ? "excluded" : item.get("notOwed").asString()));
                        } else {
                            out.add(point + ":owed " + item.get("against").asString()
                                    + (item.get("hit").asBoolean() ? " hit" : " unhit"));
                        }
                    }
                }
            }
        }
        return out;
    }

    private static List<String> pointsOf(String guard) {
        return pointsOf(guard, "");
    }

    private static List<String> excludedIn(List<String> points) {
        return points.stream().filter(point -> point.endsWith(":excluded")).toList();
    }

    @Test
    void theLevelTheQuantityCanHoldIsOwedAndTheOnesAboveItAreExcluded() {
        List<String> points = pointsOf("List.length(priced) == List.length(deals)");

        assertEquals(List.of("off:excluded", "out:excluded"), excludedIn(points), points::toString);
        assertTrue(points.contains("on:owed 0 hit"), points::toString);
        assertTrue(points.contains("off:owed -1 hit"), points::toString);
    }

    /** The same quantity however the relation is written: sides turned, both scaled. */
    @Test
    void theSameQuantityWrittenTheOtherWayRoundOrScaledIsTheSameBorder() {
        List<String> points = pointsOf("List.length(priced) == List.length(deals)");

        assertEquals(points, pointsOf("List.length(deals) == List.length(priced)"));
        assertEquals(points,
                pointsOf("List.length(priced) * 2 == List.length(deals) * 2"));
    }

    /**
     * A level below nought is a level the quantity holds. Only what is above nought is excluded;
     * nought itself, beside the line, is a row somebody can write and is owed.
     */
    @Test
    void aLevelBelowNoughtStillOwesTheValueBesideItThatIsNought() {
        List<String> points = pointsOf("List.length(priced) + 1 == List.length(deals)");

        assertEquals(List.of("out:excluded"), excludedIn(points), points::toString);
        assertTrue(points.contains("on:owed -1 hit"), points::toString);
        assertTrue(points.contains("off:owed 0 hit"), points::toString);
    }

    /** A level above nought is one the quantity never holds, and the report says so. */
    @Test
    void aLevelAboveNoughtIsALineOutsideWhatTheQuantityHolds() {
        Compilation compilation = measured(model(
                "List.length(priced) == List.length(deals) + 1", ""));
        String said = AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));

        assertEquals(List.of(), pointsOf("List.length(priced) == List.length(deals) + 1"));
        assertTrue(said.contains("draws its line outside what the quantity it cuts ever holds"),
                said);
    }

    /**
     * The size of another container does not bound the difference: the count of the first is two
     * where the other holds none, and the point above the line is a row that stands.
     */
    @Test
    void theSizeOfAnotherContainerLeavesTheDifferenceUnbounded() {
        String rows = """
                    | "two priced, none other" : ([ usd, usd ], [ ], known) -> Short
                    | "one priced, none other" : ([ usd ], [ ], known) -> Short
                """;
        List<String> points = pointsOf("List.length(priced) == List.length(others)", rows);

        assertEquals(List.of(), excludedIn(points), points::toString);
        assertTrue(points.contains("off:owed 1 hit"), points::toString);
    }

    /** Its own size added and not taken away is a different quantity, above nought as it may be. */
    @Test
    void theSizeOfItsOwnContainerAddedLeavesItUnbounded() {
        List<String> points = pointsOf("List.length(priced) + List.length(deals) == 2");

        assertEquals(List.of(), excludedIn(points), points::toString);
        assertFalse(points.isEmpty());
    }

    @Test
    void theSizeOfAnotherContainerBesideItsOwnLeavesItUnbounded() {
        List<String> points = pointsOf(
                "List.length(priced) == List.length(deals) + List.length(others)");

        assertEquals(List.of(), excludedIn(points), points::toString);
        assertFalse(points.isEmpty());
    }
}
