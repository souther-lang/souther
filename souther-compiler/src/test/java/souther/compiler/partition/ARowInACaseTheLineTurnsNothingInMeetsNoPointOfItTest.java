package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.ACompiledModel;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceRendering;
import souther.compiler.inputs.InputDomain;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.WhereEachLineDecides;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.concurrent.ConcurrentHashMap;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A row meets a line of a statement of several only in a case the line turns the statement in,
 * however many cases there are and whether they were said one by one or as one.
 *
 * <p>{@code x} is compared with nought in each of several cases, each a truth of its own taken with
 * {@code x + y > 0} or with its failing, over a {@code y} declared at nought or above. Where that
 * part fails, the declarations leave {@code x} at nought or below, so the line on {@code x} has
 * rows on one side of it only and turns nothing — though the statement, read without the
 * declarations, turns there as anywhere. Nought is still a point of the line there, and a row in
 * such a case at nought tells nothing about the line.
 *
 * <p>Past a figure the cases are said as one condition, and that condition holds the cases the line
 * turns nothing in as well as the ones it turns in. The line is read in the cases that divide rows
 * and no other, so a row in the condition is not by that alone a row at the line.
 *
 * <p>Which cases the line is drawn in is asked of the guards, for each way the cases come past the
 * cases said one by one, with one case that fails the part beside those that hold it: said as one
 * and taken apart again into as many as are said one by one (as many holding it as the figure),
 * and said as one with more than that dividing rows, kept as one (one more). That a row is at the
 * line's point only in a case the line is drawn in is asked of the report once, with as few cases
 * as there can be — one holding the part and one failing it: what reads a row against a point is
 * the same however the cases it was drawn in came, and how many cases there are against the figure
 * is asked without a compilation in
 * {@code meaning.WhereALineDecidesIsAskedOfEachCaseItWasSaidForTest}.
 */
class ARowInACaseTheLineTurnsNothingInMeetsNoPointOfItTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    /** The guards of {@code e} for each number of cases holding the part, which every test here
     *  only reads. */
    private static final Map<Integer, GuardThresholds.Guards> GUARDS = new ConcurrentHashMap<>();

    /** As many cases holding the part as are said one by one, and one more. */
    private static final List<Integer> AT_AND_PAST_THE_FIGURE =
            List.of(WhereEachLineDecides.MOST_CASES, WhereEachLineDecides.MOST_CASES + 1);

    /**
     * A row where {@code x + y > 0} fails, at nought on {@code x}, meets no point of the line on
     * {@code x}.
     */
    @Test
    void aRowInACaseTheLineTurnsNothingInIsNotAtItsPoint() {
        assertFalse(atNought(statement(1), "0, MB(0), false, true"),
                "x + y > 0 fails and the line turns nothing there");
    }

    /**
     * And a row where it holds, at the same point, meets it, which is what makes the one above
     * tell anything: the line is read in the cases it turns in, and nought is a point of it there.
     */
    @Test
    void aRowInACaseTheLineTurnsInIsAtItsPoint() {
        assertTrue(atNought(statement(1), "0, MB(1), true, false"),
                "x + y > 0 holds and the line turns there");
    }

    /**
     * The line on {@code x} is drawn in the cases that hold {@code x + y > 0} and in no case that
     * holds it failing: one by one where those are as few as are said one by one, and as one where
     * they are more. With the one case failing it, the cases are past the figure either way.
     */
    @Test
    void theLineIsDrawnOnlyInTheCasesItTurnsIn() {
        for (int holding : AT_AND_PAST_THE_FIGURE) {
            int of = holding;
            List<Proposition> cases = casesTheLineIsDrawnIn(holding);
            assertEquals(holding <= WhereEachLineDecides.MOST_CASES ? holding : 1, cases.size(),
                    () -> "the cases the line is drawn in, of " + of + " holding: " + cases);
            for (Proposition each : cases) {
                List<Boolean> comparisons = each.partsHeld().stream()
                        .flatMap(part -> part instanceof Proposition.Compared compared
                                ? Stream.of(compared.holds()) : Stream.empty())
                        .toList();
                assertEquals(List.of(true), comparisons,
                        () -> "a case the line is drawn in holds x + y > 0, of " + of
                                + " holding: " + each);
            }
        }
    }

    /**
     * The way to each case a line is drawn in is filed under that case, with the case put on it:
     * the cases are known once the line is narrowed by what arrives, and a border asks for its way
     * by the case it was drawn in ({@link ReachingCuts#wayTo}), and finds the way to the comparison
     * with that case after it.
     */
    @Test
    void theWayToEachCaseALineIsDrawnInIsFiledUnderThatCase() {
        for (int holding : AT_AND_PAST_THE_FIGURE) {
            int of = holding;
            GuardThresholds.Guards guards = guards(holding);
            List<LineOrigin.ComparisonOrigin> inACase = drawnInACase(guards);
            assertFalse(inACase.isEmpty(), () -> "some line is drawn in a case, of " + of);
            for (LineOrigin.ComparisonOrigin origin : inACase) {
                List<OnTheWay> toTheCase = guards.reaching().wayTo(origin).onTheWay();
                List<OnTheWay> toTheComparison = guards.reaching().byLine()
                        .get(new ReachingCuts.ALine(origin.read().states(), Optional.empty()));
                assertTrue(toTheCase.size() > toTheComparison.size()
                                && toTheCase.containsAll(toTheComparison),
                        () -> "the way to " + origin.part().orElseThrow().part()
                                + " is the way to the comparison and the case after it, of " + of
                                + ": " + toTheCase);
            }
        }
    }

    /**
     * A line every case of which divides rows is asked to the end and read in all of them, and
     * nothing of it is left not worked out: {@code x} compared with nought where any of the
     * truths holds, each truth a case the line turns in, and one case past the figure. No two
     * truths are one, so none of the cases joins another.
     */
    @Test
    void aLineEveryCaseOfWhichDividesRowsIsWorkedOutInAll() {
        List<String> names = new ArrayList<>();
        List<String> typed = new ArrayList<>();
        for (int i = 0; i <= WhereEachLineDecides.MOST_CASES; i++) {
            names.add("t" + i);
            typed.add("t" + i + ": Bool");
        }
        JsonNode report = JSON.readTree(measured("""
                module probe
                behavior e : (x: Int, TYPED) -> Int
                let e (x, NAMES) = if (if ANY then x else 0) > 0 then 1 else 0
                """.replace("TYPED", String.join(", ", typed))
                .replace("NAMES", String.join(", ", names))
                .replace("ANY", anyOf(names)))
                .json(SourceRendering.namedByIdentity(SourceLayouts.NONE)));
        List<JsonNode> onX = new ArrayList<>();
        borders(report, "e/x", onX);
        assertEquals(1, onX.size(), () -> "the line on x is a border: " + report);
        List<String> left = new ArrayList<>();
        reasons(report, "x", left);
        assertEquals(List.of(), left, "and nothing is left at x");
    }

    private static void reasons(JsonNode node, String position, List<String> out) {
        if (node.isObject() && node.has("ruleId") && node.has("reason")
                && position.equals(node.path("position").asString())) {
            out.add(node.path("reason").asString());
        }
        node.forEach(child -> reasons(child, position, out));
    }

    /** The case each line drawn in a case of the statement is drawn in. */
    private static List<Proposition> casesTheLineIsDrawnIn(int holding) {
        return drawnInACase(guards(holding)).stream()
                .map(origin -> origin.part().orElseThrow().decides())
                .toList();
    }

    private static List<LineOrigin.ComparisonOrigin> drawnInACase(GuardThresholds.Guards guards) {
        return guards.evidence().stream()
                .map(each -> each.evidence().by())
                .flatMap(by -> by instanceof LineOrigin.ComparisonOrigin comparison
                        && comparison.part().isPresent()
                        ? Stream.of(comparison) : Stream.empty())
                .toList();
    }

    private static GuardThresholds.Guards guards(int holding) {
        return GUARDS.computeIfAbsent(holding, of -> guardsOf(statement(of)));
    }

    /** What the guards of {@code e} come to in {@code source}. */
    private static GuardThresholds.Guards guardsOf(String source) {
        Compilation compilation = ACompiledModel.answered(source);
        String module = compilation.modules().getFirst();
        RuleReadingSource rules = RuleReadings.of(compilation, module);
        Bodies.Elaborated checked = compilation.db().ask(new Bodies.Checked(module)).value();
        assertNotNull(checked, "the model compiles");
        Map<String, InputDomain> inputs =
                compilation.db().ask(new Adequacy.Inputs(module)).value();
        return ThresholdFixtures.guardsOf("e", checked.analysisBodies().get("e"),
                checked.behaviorBodies().get("e"), checked.plan(), inputs.get("e"), rules);
    }

    /** Whether the row {@code (row)} meets the point of the line on {@code x} at nought. */
    private static boolean atNought(String statement, String row) {
        JsonNode report = JSON.readTree(measured(statement + """

                example e
                    | (ROW) -> 0
                """.replace("ROW", row))
                .json(SourceRendering.namedByIdentity(SourceLayouts.NONE)));
        // The comparison inside the statement draws a line of its own on x, at one: y is held at
        // nought or above, so x from one on holds it whatever y is. It is written once in each way
        // of the statement, and each writing a row gets to draws that line: the one after the
        // first is got to where the first held and where it failed, and comes out as the first
        // did on each side of one. The line asked about is the statement's, drawn where the part
        // of it that is x turns.
        List<JsonNode> onX = new ArrayList<>();
        borders(report, "e/x", onX);
        List<String> besideIt = new ArrayList<>();
        onX.removeIf(each -> {
            String kind = each.path("lineId").path("line").path("which").path("kind").asString();
            if (!kind.equals("part_of_comparison")) {
                besideIt.add(kind);
            }
            return !kind.equals("part_of_comparison");
        });
        assertEquals(List.of("comparison", "comparison"), besideIt,
                () -> "beside it, each writing of the comparison's own line at one: " + besideIt);
        assertEquals(1, onX.size(), () -> "one line on x, read in every case it turns in: " + onX);
        List<JsonNode> atTheLine = new ArrayList<>();
        onX.getFirst().path("items").forEach(item -> {
            if (item.path("location").path("kind").asString().equals("at_the_line")) {
                atTheLine.add(item);
            }
        });
        assertEquals(1, atTheLine.size(), () -> "one point at nought: " + onX);
        return atTheLine.getFirst().path("hit").asBoolean();
    }

    /**
     * {@code x} compared with nought in {@code holding} cases that hold {@code x + y > 0} and one
     * that fails it, and nought compared with nought outside them. Each case is a truth of its own
     * taken with the part, {@code t1 .. t[holding]} holding it and the one after failing it, so any
     * two cases differ in two parts and none joins another.
     */
    private static String statement(int holding) {
        List<String> ways = new ArrayList<>();
        List<String> names = new ArrayList<>();
        List<String> typed = new ArrayList<>();
        for (int i = 1; i <= holding + 1; i++) {
            ways.add("(" + (i <= holding ? "x + y.value > 0" : "Bool.not(x + y.value > 0)")
                    + " && t" + i + ")");
            names.add("t" + i);
            typed.add("t" + i + ": Bool");
        }
        return """
                module probe
                data MB = Int
                    invariant value >= 0
                behavior e : (x: Int, y: MB, TYPED) -> Int
                let e (x, y, NAMES) = if (if ANY then x else 0) > 0 then 1 else 0
                """.replace("TYPED", String.join(", ", typed))
                .replace("NAMES", String.join(", ", names))
                .replace("ANY", anyOf(ways));
    }

    /** Any one of {@code ways}, joined two halves at a time so that the source is only as deep
     *  as the halving. */
    private static String anyOf(List<String> ways) {
        if (ways.size() == 1) {
            return ways.getFirst();
        }
        int half = ways.size() / 2;
        return "(" + anyOf(ways.subList(0, half)) + " || "
                + anyOf(ways.subList(half, ways.size())) + ")";
    }

    private static AdequacyReport measured(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        ACompiledModel.compiles(compilation);
        return AdequacyReport.of(compilation);
    }

    private static void borders(JsonNode node, String axis, List<JsonNode> out) {
        if (node.isObject() && node.has("items") && node.has("lineId")
                && axis.equals(node.path("axis").asString())) {
            out.add(node);
        }
        node.forEach(child -> borders(child, axis, out));
    }
}
