package souther.compiler;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;
import java.util.function.IntBinaryOperator;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A rule of a declaration holds the sum or the difference of two of its fields to an interval, and
 * a guard after it on that form is read where it draws its lines: a row at a line of the guard has
 * the form within a step of the line, which the rule holds it to, so the rule ties the two fields
 * to one another by nothing that row needs.
 *
 * <p>Held here: that the guard is read and owes a row at each of its points, whichever side of the
 * line the rule's bound lies and however the guard is spelled; that what it draws over fields
 * bounded from nought to ten is what a walk of every pair finds; and that a rule which leaves no
 * room around the line, which states more than the form, or which holds another form, still ties
 * the fields.
 */
class ARuleOfADeclarationHoldingAFormToAnIntervalStillLeavesTheNextComparisonOfItsLinesTest {

    private static final String NOT_READ = "· not read: comparison";

    private static String model(String rule, String guard) {
        return """
                module example.band

                data Low
                data Mid
                data High

                let opaque (a: Int, b: Int) : Bool = a * b > 3

                data Pair = { a: Int, b: Int }
                    invariant %s

                behavior band : (p: Pair) -> Low | Mid | High

                let band (p) = {
                %s
                    Mid
                }
                """.formatted(rule, guard);
    }

    private static String report(String rule, String guard) {
        String source = model(rule, guard);
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code().toString()).toList(), source);
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }

    /** Whether a row is owed at each point the comparison on {@code line} draws. */
    private static Map<String, String> pointsOf(String report, int line) {
        Pattern owed = Pattern.compile("undecided whether a row is at the (ON|OFF|IN|OUT) point"
                + " \\(comparison@" + line + ":");
        Map<String, String> out = new TreeMap<>(Map.of("ON", "none", "OFF", "none", "IN", "none",
                "OUT", "none"));
        for (String each : report.split("\n")) {
            Matcher asked = owed.matcher(each);
            if (asked.find()) {
                out.put(asked.group(1), "owed");
            }
        }
        return out;
    }

    private static int lineOf(String rule, String guard) {
        List<String> text = model(rule, guard).lines().toList();
        return 1 + text.indexOf(text.stream().filter(each -> each.contains("guard"))
                .findFirst().orElseThrow());
    }

    /** The guard after the rule is read, and a row is owed at each of the points it draws. */
    @Test
    void aGuardOnTheDifferenceAfterTheRuleIsReadAndOwesARowAtEachPoint() {
        String guard = "    guard p.a - p.b < 200 else High";
        String report = report("a - b >= 100", guard);
        assertFalse(report.contains(NOT_READ), report);
        assertEquals(Map.of("ON", "owed", "OFF", "owed", "IN", "owed", "OUT", "owed"),
                pointsOf(report, lineOf("a - b >= 100", guard)), report);
    }

    /** The spelling of the guard and of the rule, and the side of the line the bound lies, are
     *  not what decides it. */
    @Test
    void theSpellingOfTheGuardAndOfTheRuleDoNotMatter() {
        for (String[] each : new String[][] {
                {"a - b >= 100", "    guard p.b - p.a > -200 else High"},
                {"a - b >= 100", "    guard p.a - p.b + 5 < 200 else High"},
                {"b - a <= -100", "    guard p.a - p.b < 200 else High"},
                {"a - b > 99", "    guard 200 > p.a - p.b else High"},
                {"a - b >= -100", "    guard p.a - p.b <= 150 else High"}}) {
            String report = report(each[0], each[1]);
            assertFalse(report.contains(NOT_READ), each[0] + " " + each[1] + "\n" + report);
        }
    }

    /**
     * Both fields from nought to ten, the rule holding {@code form} to at least {@code least},
     * then the guard asking whether it is below {@code below}. The points a row is owed at are
     * those a walk of every pair finds a row at: the last value below the line, the line, the
     * values between the rule's bound and the last below it, and those past the line.
     */
    @Test
    void whatTheGuardDrawsOverBoundedFieldsIsWhatAWalkOfEveryPairFinds() {
        // Each pair leaves values of the form on both sides of the line, so the guard decides
        // nothing already.
        int[][] differences = {{-10, 5}, {0, 5}, {-5, 3}, {2, 9}, {-9, 10}, {1, 4}, {5, 8}};
        int[][] sums = {{0, 5}, {3, 10}, {10, 14}, {15, 19}, {19, 20}, {0, 20}, {10, 20}};
        int read = 0;
        for (boolean sum : new boolean[] {false, true}) {
            String form = sum ? "p.a + p.b" : "p.a - p.b";
            for (int[] each : sum ? sums : differences) {
                int least = each[0];
                int below = each[1];
                String rule = (sum ? "a + b" : "a - b") + " >= " + least
                        + "\n    invariant a >= 0\n    invariant a <= 10"
                        + "\n    invariant b >= 0\n    invariant b <= 10";
                String guard = "    guard " + form + " < " + below + " else High";
                String report = report(rule, guard);
                String name = form + " from " + least + " below " + below;
                assertFalse(report.contains(NOT_READ), name + "\n" + report);
                read++;
                assertEquals(walked(sum, least, below), pointsOf(report, lineOf(rule, guard)),
                        name + "\n" + report);
            }
        }
        assertEquals(differences.length + sums.length, read,
                "a pair of bounds was not read, so it was not compared with the walk");
    }

    /** Which points the guard owes a row at, from a walk of every pair. */
    private static Map<String, String> walked(boolean sum, int least, int below) {
        Map<String, String> out = new TreeMap<>();
        out.put("ON", walkFinds(sum, least, below - 1, below - 1) ? "owed" : "none");
        out.put("OFF", walkFinds(sum, least, below, below) ? "owed" : "none");
        out.put("IN", walkFinds(sum, least, least, below - 2) ? "owed" : "none");
        out.put("OUT", walkFinds(sum, least, below + 1, Integer.MAX_VALUE) ? "owed" : "none");
        return out;
    }

    /** Whether some pair from nought to ten holds a value of the form of at least {@code least}
     *  and within the run from {@code from} to {@code to}. */
    private static boolean walkFinds(boolean sum, int least, int from, int to) {
        for (int a = 0; a <= 10; a++) {
            for (int b = 0; b <= 10; b++) {
                int value = sum ? a + b : a - b;
                if (value >= least && value >= from && value <= to) {
                    return true;
                }
            }
        }
        return false;
    }

    /** A rule that states more than the difference ties the fields by what it states besides. */
    @Test
    void aRuleStatingMoreThanTheDifferenceStillTiesTheFields() {
        String report = report("a - b >= 100 && opaque(a, b)",
                "    guard p.a - p.b < 200 else High");
        assertTrue(report.contains(NOT_READ), report);
    }

    /** A rule holding the sum ties the fields to one another in a way the difference's line can
     *  meet. */
    @Test
    void aRuleHoldingAnotherFormStillTiesTheFields() {
        String report = report("a + b >= 100", "    guard p.a - p.b < 200 else High");
        assertTrue(report.contains(NOT_READ), report);
    }

    /**
     * One rule holding {@code form} to {@code from..to}, each field from a bound to a bound, and a
     * guard asking whether the form is below {@code below}.
     *
     * @param oneClause whether the interval is one rule joining its two ends, or two rules
     */
    private record Case(String form, String inTheGuard, IntBinaryOperator valueOf, int[] a,
                        int[] b, int from, int to, int below, boolean oneClause) {

        String source() {
            String interval = oneClause
                    ? form + " >= " + from + " && " + form + " <= " + to
                    : form + " >= " + from + "\n    invariant " + form + " <= " + to;
            return model(interval + "\n    invariant a >= " + a[0] + "\n    invariant a <= " + a[1]
                    + "\n    invariant b >= " + b[0] + "\n    invariant b <= " + b[1],
                    "    guard " + inTheGuard + " < " + below + " else High");
        }

        /** The points some pair the rules leave has a value of the form at. */
        Map<String, String> walk() {
            boolean on = false;
            boolean off = false;
            boolean in = false;
            boolean out = false;
            for (int x = a[0]; x <= a[1]; x++) {
                for (int y = b[0]; y <= b[1]; y++) {
                    int value = valueOf.applyAsInt(x, y);
                    if (value < from || value > to) {
                        continue;
                    }
                    on |= value == below - 1;
                    off |= value == below;
                    in |= value <= below - 2;
                    out |= value >= below + 1;
                }
            }
            Map<String, String> points = new TreeMap<>();
            points.put("ON", on ? "owed" : "none");
            points.put("OFF", off ? "owed" : "none");
            points.put("IN", in ? "owed" : "none");
            points.put("OUT", out ? "owed" : "none");
            return points;
        }

        boolean leavesTheGuardUndecided() {
            Map<String, String> points = walk();
            return (points.get("ON").equals("owed") || points.get("IN").equals("owed"))
                    && (points.get("OFF").equals("owed") || points.get("OUT").equals("owed"));
        }
    }

    /**
     * What the rules leave of the fields is not always what the rule alone does: the bounds of the
     * fields can leave the form a narrower run than the rule, the rule can leave no pair at all,
     * and a rule over a weighted sum skips values of the form. A point is owed only where some
     * pair has a value there, and where the guard is left undecided and read, at every such point.
     */
    @Test
    void whatTheRulesAndTheBoundsLeaveTogetherIsWhatAWalkOfEveryPairFinds() {
        int[] zeroToTen = {0, 10};
        List<Case> cases = List.of(
                // the bounds leave the first field only the upper part of what it would otherwise take
                new Case("a + b", "p.a + p.b", (x, y) -> x + y, new int[] {0, 4}, new int[] {5, 7},
                        9, 11, 10, false),
                new Case("a + b", "p.a + p.b", (x, y) -> x + y, new int[] {0, 4}, new int[] {5, 7},
                        9, 11, 10, true),
                // an interval of one value, and one value of it either side
                new Case("a + b", "p.a + p.b", (x, y) -> x + y, zeroToTen, zeroToTen, 10, 10, 10,
                        false),
                new Case("a - b", "p.a - p.b", (x, y) -> x - y, zeroToTen, new int[] {0, 3},
                        4, 6, 5, true),
                // a weighted sum, whose values the second field steps over
                new Case("a + 2 * b", "p.a + 2 * p.b", (x, y) -> x + 2 * y, new int[] {0, 3},
                        new int[] {2, 6}, 9, 11, 10, false),
                new Case("a + 2 * b", "p.a + 2 * p.b", (x, y) -> x + 2 * y, zeroToTen, zeroToTen,
                        5, 6, 6, true),
                // the form takes only even values, and the interval's ends are odd
                new Case("2 * a + 2 * b", "2 * p.a + 2 * p.b", (x, y) -> 2 * x + 2 * y, zeroToTen,
                        zeroToTen, 9, 11, 10, false));
        int compared = 0;
        List<String> left = new ArrayList<>();
        for (Case each : cases) {
            String report = reportOf(each.source());
            int line = lineWith(each.source(), "guard");
            Map<String, String> found = pointsOf(report, line);
            Map<String, String> walked = each.walk();
            for (String point : walked.keySet()) {
                assertFalse(found.get(point).equals("owed") && walked.get(point).equals("none"),
                        "a row is owed at " + point + " where no pair has one\n" + each.source()
                                + "\n" + report);
            }
            if (each.leavesTheGuardUndecided() && !report.contains(NOT_READ)) {
                assertEquals(walked, found, each.source() + "\n" + report);
                compared++;
            }
            left.add(each.form() + " " + each.from() + ".." + each.to() + " below " + each.below()
                    + (each.leavesTheGuardUndecided() ? " undecided" : " decided")
                    + (report.contains(NOT_READ) ? " not read" : " read") + " " + found);
        }
        assertTrue(compared >= 3, "only " + compared + " of the cases were read and compared: "
                + left);
    }

    /** Rules that leave no pair are refused where they are written, so no guard is ever read over
     *  the region they would put aside. */
    @Test
    void rulesThatLeaveNoPairAreRefusedWhateverComesAfterThem() {
        Case empty = new Case("a + b", "p.a + p.b", (x, y) -> x + y, new int[] {0, 4},
                new int[] {0, 4}, 9, 11, 10, false);
        Compilation compilation = Compilation.ofSource(empty.source(), "Main");
        compilation.answerEverything();
        assertTrue(compilation.errors().stream()
                .anyMatch(each -> each.diagnostic().code().toString().equals("E1013")),
                empty.source());
    }

    private static String reportOf(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code().toString()).toList(), source);
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }

    private static int lineWith(String source, String text) {
        List<String> lines = source.lines().toList();
        return 1 + lines.indexOf(lines.stream().filter(each -> each.contains(text))
                .findFirst().orElseThrow());
    }

    /** The guards one after another on the one sum, as a body states them: each is read, and a row
     *  is owed at every point either of them draws. */
    @Test
    void guardsOneAfterAnotherOnTheSameSumAreEachReadAndOweARowAtEachPoint() {
        String source = """
                module example.band

                data Low
                data Mid
                data High

                data Pair = { a: Int, b: Int }

                behavior band : (p: Pair) -> Low | Mid | High

                let band (p) = {
                    let s = p.a + p.b
                    guard s >= 100 else Low
                    guard s < 200 else High
                    Mid
                }
                """;
        String report = reportOf(source);
        assertFalse(report.contains(NOT_READ), report);
        Map<String, String> owed = Map.of("ON", "owed", "OFF", "owed", "IN", "owed", "OUT", "owed");
        assertEquals(owed, pointsOf(report, lineWith(source, "guard s >= 100")), report);
        assertEquals(owed, pointsOf(report, lineWith(source, "guard s < 200")), report);
    }

    private static final String TWO_VALUES_OF_THE_DECLARATION = """
            module example.band

            data Low
            data Mid
            data High

            data Pair = { a: Int, b: Int }
                invariant a - b >= 100

            data Two = { p: Pair, q: Pair }

            behavior band : (x: Pair, y: Pair) -> Low | Mid | High

            let band (x, y) = {
                guard x.a - x.b < 200 else High
                Mid
            }

            behavior nested : (t: Two) -> Low | Mid | High

            let nested (t) = {
                guard t.p.a - t.p.b < 200 else High
                Mid
            }
            """;

    /** A rule of the declaration is a rule of every value of it, and the line of a guard is drawn
     *  on one of them: another parameter holding a value of the declaration changes nothing. */
    @Test
    void theSameDeclarationOnAnotherParameterDoesNotKeepTheGuardFromBeingRead() {
        String report = reportOf(TWO_VALUES_OF_THE_DECLARATION);
        int line = lineWith(TWO_VALUES_OF_THE_DECLARATION, "guard x.a - x.b < 200");
        assertFalse(report.contains("· not read: comparison@" + line), report);
        assertEquals(Map.of("ON", "owed", "OFF", "owed", "IN", "owed", "OUT", "owed"),
                pointsOf(report, line), report);
    }

    /** The declaration at two places of one parameter: what holds of one of them is not shown of
     *  the other, so the rule keeps tying the fields. */
    @Test
    void theSameDeclarationAtTwoPlacesOfOneParameterStillTiesTheFields() {
        String report = reportOf(TWO_VALUES_OF_THE_DECLARATION);
        int line = lineWith(TWO_VALUES_OF_THE_DECLARATION, "guard t.p.a - t.p.b < 200");
        assertTrue(report.contains("· not read: comparison@" + line), report);
    }

    /** A rule ending at the line leaves no row beside it that the rule does not meet. */
    @Test
    void aRuleEndingAtTheLineLeavesNoRoomAndStillTiesTheFields() {
        String report = report("a - b <= 200", "    guard p.a - p.b < 200 else High");
        assertTrue(report.contains(NOT_READ), report);
    }
}
