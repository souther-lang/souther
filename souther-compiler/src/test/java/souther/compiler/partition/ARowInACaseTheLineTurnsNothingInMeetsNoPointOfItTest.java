package souther.compiler.partition;

import org.junit.jupiter.api.Test;

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
 * <p>{@code x} is compared with nought where an even number of the statement's parts hold, and one
 * of the parts is {@code x + y > 0} over a {@code y} declared at nought or above. Where that part
 * fails, the declarations leave {@code x} at nought or below, so the line on {@code x} has rows on
 * one side of it only and turns nothing — though the statement, read without the declarations,
 * turns there as anywhere. Nought is still a point of the line there, and a row in such a case at
 * nought tells nothing about the line.
 *
 * <p>Past a figure the cases are said as one condition, and that condition holds the cases the line
 * turns nothing in as well as the ones it turns in. The line is read in the cases that divide rows
 * and no other, so a row in the condition is not by that alone a row at the line.
 *
 * <p>Which cases the line is drawn in is asked of the guards, for each way the cases come: said
 * one by one (four truths beside the part), said as one and taken apart again into as many as are
 * said one by one (five), and said as one with more than that dividing rows, kept as one (six).
 * That a row is at the line's point only in a case the line is drawn in is asked of the report
 * once, with the cases said one by one: what reads a row against a point is the same however the
 * cases it was drawn in came, and how many cases there are against the figure is asked without a
 * compilation in {@code meaning.WhereALineDecidesIsAskedOfEachCaseItWasSaidForTest}.
 */
class ARowInACaseTheLineTurnsNothingInMeetsNoPointOfItTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    /** The guards of {@code e} for each number of truths, which every test here only reads. */
    private static final Map<Integer, GuardThresholds.Guards> GUARDS = new ConcurrentHashMap<>();

    /**
     * A row where {@code x + y > 0} fails, at nought on {@code x}, meets no point of the line on
     * {@code x}.
     */
    @Test
    void aRowInACaseTheLineTurnsNothingInIsNotAtItsPoint() {
        assertFalse(atNought(statement(4), "0, MB(0)", 4, 2),
                "x + y > 0 fails and the line turns nothing there");
    }

    /**
     * And a row where it holds, at the same point, meets it, which is what makes the one above
     * tell anything: the line is read in the cases it turns in, and nought is a point of it there.
     */
    @Test
    void aRowInACaseTheLineTurnsInIsAtItsPoint() {
        assertTrue(atNought(statement(4), "0, MB(1)", 4, 1),
                "x + y > 0 holds and the line turns there");
    }

    /**
     * The line on {@code x} is drawn in the cases that hold {@code x + y > 0} and in no case that
     * holds it failing: one by one where those are as few as are said one by one, and as one where
     * they are more. Of the assignments to the truths, half put the part on its holding side.
     */
    @Test
    void theLineIsDrawnOnlyInTheCasesItTurnsIn() {
        for (int truths = 4; truths <= 6; truths++) {
            int of = truths;
            int dividing = 1 << (truths - 1);
            List<Proposition> cases = casesTheLineIsDrawnIn(truths);
            assertEquals(dividing <= WhereEachLineDecides.MOST_CASES ? dividing : 1, cases.size(),
                    () -> "the cases the line is drawn in, of " + of + " truths: " + cases);
            for (Proposition each : cases) {
                List<Boolean> comparisons = each.partsHeld().stream()
                        .flatMap(part -> part instanceof Proposition.Compared compared
                                ? Stream.of(compared.holds()) : Stream.empty())
                        .toList();
                assertEquals(List.of(true), comparisons,
                        () -> "a case the line is drawn in holds x + y > 0, of " + of
                                + " truths: " + each);
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
        for (int truths = 5; truths <= 6; truths++) {
            int of = truths;
            GuardThresholds.Guards guards = guards(truths);
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
     * nothing of it is left not worked out: {@code x} compared with nought where an even number of
     * seven truths hold, which is more cases than are said one by one and each a case the line
     * turns in.
     */
    @Test
    void aLineEveryCaseOfWhichDividesRowsIsWorkedOutInAll() {
        List<String> ways = new ArrayList<>();
        int truths = 7;
        for (int each = 0; each < 1 << truths; each++) {
            if (Integer.bitCount(each) % 2 != 0) {
                continue;
            }
            List<String> parts = new ArrayList<>();
            for (int i = 0; i < truths; i++) {
                parts.add((each >> i & 1) == 1 ? "t" + i : "Bool.not(t" + i + ")");
            }
            ways.add("(" + String.join(" && ", parts) + ")");
        }
        List<String> names = new ArrayList<>();
        List<String> typed = new ArrayList<>();
        for (int i = 0; i < truths; i++) {
            names.add("t" + i);
            typed.add("t" + i + ": Bool");
        }
        JsonNode report = JSON.readTree(measured("""
                module probe
                behavior e : (x: Int, TYPED) -> Int
                let e (x, NAMES) = if (if EVEN then x else 0) > 0 then 1 else 0
                """.replace("TYPED", String.join(", ", typed))
                .replace("NAMES", String.join(", ", names))
                .replace("EVEN", anyOf(ways)))
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
    private static List<Proposition> casesTheLineIsDrawnIn(int truths) {
        return drawnInACase(guards(truths)).stream()
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

    private static GuardThresholds.Guards guards(int truths) {
        return GUARDS.computeIfAbsent(truths, of -> guardsOf(statement(of)));
    }

    /** What the guards of {@code e} come to in {@code source}. */
    private static GuardThresholds.Guards guardsOf(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        String module = compilation.modules().getFirst();
        RuleReadingSource rules = RuleReadings.of(compilation, module);
        Bodies.Elaborated checked = compilation.db().ask(new Bodies.Checked(module)).value();
        assertNotNull(checked, "the model compiles");
        Map<String, InputDomain> inputs =
                compilation.db().ask(new Adequacy.Inputs(module)).value();
        return ThresholdFixtures.guardsOf("e", checked.analysisBodies().get("e"),
                checked.behaviorBodies().get("e"), checked.plan(), inputs.get("e"), rules);
    }

    /**
     * Whether the row {@code (written, t1 .. t[holding] true, the rest false)} meets the point of
     * the line on {@code x} at nought.
     */
    private static boolean atNought(String statement, String written, int truths, int holding) {
        List<String> row = new ArrayList<>();
        for (int i = 1; i <= truths; i++) {
            row.add(i <= holding ? "true" : "false");
        }
        JsonNode report = JSON.readTree(measured(statement + """

                example e
                    | (WRITTEN, ROW) -> 0
                """.replace("WRITTEN", written).replace("ROW", String.join(", ", row)))
                .json(SourceRendering.namedByIdentity(SourceLayouts.NONE)));
        List<JsonNode> onX = new ArrayList<>();
        borders(report, "e/x", onX);
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
     * {@code x} compared with nought where an even number of {@code x + y > 0} and {@code truths}
     * truths hold, and nought compared with nought where they do not.
     */
    private static String statement(int truths) {
        List<String> ways = new ArrayList<>();
        for (int each = 0; each < 1 << (truths + 1); each++) {
            if (Integer.bitCount(each) % 2 != 0) {
                continue;
            }
            List<String> parts = new ArrayList<>();
            parts.add((each & 1) == 1 ? "x + y.value > 0" : "Bool.not(x + y.value > 0)");
            for (int i = 1; i <= truths; i++) {
                parts.add((each >> i & 1) == 1 ? "t" + i : "Bool.not(t" + i + ")");
            }
            ways.add("(" + String.join(" && ", parts) + ")");
        }
        List<String> names = new ArrayList<>();
        List<String> typed = new ArrayList<>();
        for (int i = 1; i <= truths; i++) {
            names.add("t" + i);
            typed.add("t" + i + ": Bool");
        }
        return """
                module probe
                data MB = Int
                    invariant value >= 0
                behavior e : (x: Int, y: MB, TYPED) -> Int
                let e (x, y, NAMES) = if (if EVEN then x else 0) > 0 then 1 else 0
                """.replace("TYPED", String.join(", ", typed))
                .replace("NAMES", String.join(", ", names))
                .replace("EVEN", anyOf(ways));
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
        compilation.answerEverything();
        assertTrue(compilation.errors().isEmpty(), () -> "compiles: " + compilation.errors()
                .stream().map(e -> e.diagnostic().code() + " " + e.diagnostic().titleKey())
                .toList());
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
