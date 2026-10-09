package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceRendering;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * How many elements of a container meet a statement is a number a rule can draw a line on, and a
 * row stands on that line where that many of its elements meet the statement.
 *
 * <p>{@code List.length(List.filter(x -> x > limit, xs)) == 1} is a line on how many elements of
 * {@code xs} are above {@code limit}: one, with none and two beside it. The count is no form over
 * the row's numbers — it turns on every element and on {@code limit} — so a row is read at it whole,
 * element by element, and the line divides no position.
 */
class HowManyElementsMeetAStatementIsALineOnTheCountTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    private static final String EXACTLY_ONE = """
            module probe

            behavior exactlyOne : (xs: List<Int>, limit: Int) -> Int
            let exactlyOne (xs, limit) =
                if List.length(List.filter(x -> x > limit, xs)) == 1 then 1 else 0
            """;

    @Test
    void aCountAgainstANumberIsALineOnTheCount() {
        JsonNode report = reportOf("""
                module probe

                behavior atLeastTwo : (xs: List<Int>) -> Int
                let atLeastTwo (xs) =
                    if List.length(List.filter(x -> x > 0, xs)) >= 2 then 1 else 0
                """);
        List<JsonNode> counts = countBorders(report);
        assertEquals(1, counts.size(), () -> "one line on the count: " + counts);
        assertEquals("#xs [xs[*] > 0]",
                counts.getFirst().at("/lineId/target/quantity/counted").asString());
        assertEquals("2", pointAt(counts.getFirst(), "on").path("against").asString(),
                "at two of them");
        assertEquals("1", pointAt(counts.getFirst(), "off").path("against").asString(),
                "and one beside it");
        assertEquals("2 < #xs [xs[*] > 0]",
                pointAt(counts.getFirst(), "in").path("against").asString(),
                "with the side above it the one the rule holds on");

        JsonNode turned = countBorders(reportOf("""
                module probe

                behavior atLeastTwo : (xs: List<Int>) -> Int
                let atLeastTwo (xs) =
                    if 2 <= List.length(List.filter(x -> x > 0, xs)) then 1 else 0
                """)).getFirst();
        assertEquals("2 < #xs [xs[*] > 0]", pointAt(turned, "in").path("against").asString(),
                "and the same written the other way round");
    }

    /**
     * The rows #2218 was written with, each standing where as many of its elements are above the
     * limit as it holds: none, one and two meet the line's three points.
     */
    @Test
    void aRowStandsWhereSoManyOfItsElementsMeetTheStatement() {
        JsonNode report = reportOf(EXACTLY_ONE + """
                example exactlyOne
                    | "none" : ([], 0) -> 0
                    | "one" : ([5], 0) -> 1
                    | "two" : ([5, 6], 0) -> 0
                    | "one of two" : ([5, -1], 0) -> 1
                """);
        JsonNode count = countBorders(report).getFirst();
        assertTrue(pointAt(count, "on").path("hit").asBoolean(), "one of them above the limit");
        for (JsonNode off : pointsAt(count, "off")) {
            assertTrue(off.path("hit").asBoolean(),
                    () -> "none and two of them above it: " + off);
        }
    }

    /** And a row whose elements put it beside the line is not at it, whatever the elements are. */
    @Test
    void aRowWithAnotherCountIsNotAtTheLine() {
        JsonNode report = reportOf(EXACTLY_ONE + """
                example exactlyOne
                    | "two" : ([5, 6], 0) -> 0
                """);
        assertTrue(!pointAt(countBorders(report).getFirst(), "on").path("hit").asBoolean(),
                "two elements above the limit are not one");
    }

    /**
     * An element the statement could not be read at is neither counted nor left out: the count is
     * somewhere from those that meet it to those together with every element nothing could say of,
     * and a row is at an item only where every count in that run is.
     */
    @Test
    void anElementNothingCouldReadIsNeitherCountedNorLeftOut() {
        AStatementAtARow.HowManyAtARow oneMeetsAndOneIsUnread =
                new AStatementAtARow.HowManyAtARow(1, 1, Set.of(ReadingGap.NO_VALUE));
        assertEquals(AStatementAtARow.Answer.HOLDS,
                oneMeetsAndOneIsUnread.whether(n -> ExactAnswer.held(n >= 1)),
                "at least one, whichever way the unread element went");
        assertEquals(AStatementAtARow.Answer.FAILS,
                oneMeetsAndOneIsUnread.whether(n -> ExactAnswer.held(n >= 3)),
                "and not three, whichever way it went");
        assertEquals(new AStatementAtARow.Answer.CouldNotTell(Set.of(ReadingGap.NO_VALUE)),
                oneMeetsAndOneIsUnread.whether(n -> ExactAnswer.held(n == 1)),
                "and exactly one turns on it, which could not be told — not counted as failing");
    }

    /**
     * A count against another of the input's numbers is two numbers held apart, and no line on a
     * count.
     */
    @Test
    void aCountAgainstAnotherNumberOfTheInputIsNoLineOnTheCount() {
        JsonNode report = reportOf("""
                module probe

                behavior asMany : (xs: List<Int>, n: Int) -> Int
                let asMany (xs, n) =
                    if List.length(List.filter(x -> x > 0, xs)) == n then 1 else 0
                """);
        assertTrue(countBorders(report).isEmpty(), () -> "no line on the count: " + report);
    }

    /** Two counts held together in one statement are two lines of the one rule, each its own. */
    @Test
    void twoCountsInOneStatementAreTwoLines() {
        JsonNode report = reportOf("""
                module probe

                behavior oneEach : (xs: List<Int>) -> Int
                let oneEach (xs) =
                    if List.length(List.filter(x -> x > 0, xs)) == 1
                            && List.length(List.filter(x -> x < 0, xs)) == 1
                        then 1 else 0
                """);
        Set<String> counted = new TreeSet<>();
        countBorders(report).forEach(each ->
                counted.add(each.at("/lineId/target/quantity/counted").asString()));
        assertEquals(Set.of("#xs [xs[*] < 0]", "#xs [xs[*] > 0]"), counted);
    }

    /** A statement about each element that is itself about the elements of another container is
     *  read through, element by element of each. */
    @Test
    void aCountOfElementsMeetingAQuantifierIsReadThroughIt() {
        JsonNode report = reportOf("""
                module probe

                behavior fitsOne : (ws: List<Int>, cs: List<Int>) -> Int
                let fitsOne (ws, cs) =
                    if List.length(List.filter(w -> List.all(c -> w > c, cs), ws)) == 1
                        then 1 else 0
                example fitsOne
                    | "one fits" : ([5, 0], [1, 2]) -> 1
                """);
        JsonNode count = countBorders(report).getFirst();
        assertTrue(pointAt(count, "on").path("hit").asBoolean(),
                "five is above both one and two, and nought is above neither");
    }

    private static JsonNode reportOf(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return JSON.readTree(AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(SourceLayouts.NONE)));
    }

    /** Every border drawn on a count. */
    private static List<JsonNode> countBorders(JsonNode report) {
        List<JsonNode> out = new ArrayList<>();
        collect(report, out);
        return out;
    }

    private static void collect(JsonNode node, List<JsonNode> out) {
        if (node.isObject() && node.has("items") && "count_of_elements".equals(node.path("kind").asString())) {
            out.add(node);
        }
        node.forEach(child -> collect(child, out));
    }

    private static JsonNode pointAt(JsonNode border, String point) {
        return pointsAt(border, point).getFirst();
    }

    private static List<JsonNode> pointsAt(JsonNode border, String point) {
        List<JsonNode> out = new ArrayList<>();
        border.path("items").forEach(each -> {
            if (point.equals(each.path("point").asString())) {
                out.add(each);
            }
        });
        if (out.isEmpty()) {
            throw new AssertionError("a " + point + " point on " + border);
        }
        return out;
    }
}
