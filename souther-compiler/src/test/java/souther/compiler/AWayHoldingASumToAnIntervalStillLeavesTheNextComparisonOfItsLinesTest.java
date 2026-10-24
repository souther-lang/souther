package souther.compiler;

import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;
import souther.compiler.report.GeneratedRows;

import org.junit.jupiter.api.Test;

import java.math.BigInteger;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A guard on a sum holds the numbers it adds to an interval, and the guard after it is read there:
 * a row at the line of the second guard has the sum within a step of the line, which the first
 * holds it to, so the first ties the numbers to one another by nothing that row needs.
 *
 * <p>Held here: that the guard after is read, whatever the numbers are bounded by and however the
 * sum is written; that what it draws is what a walk of every pair of values says it draws, and the
 * rows made for it are at the sums its lines are at; and that a way holding the numbers to another
 * form still ties them.
 */
class AWayHoldingASumToAnIntervalStillLeavesTheNextComparisonOfItsLinesTest {

    private static final String NOT_READ = "· not read: comparison";

    private static final Pattern A_ROW = Pattern.compile("\\((-?\\d+),\\s*(-?\\d+)\\)");

    private static String model(String guards) {
        return """
                module example.band

                data Low
                data Mid
                data High

                behavior band : (a: Int, b: Int) -> Low | Mid | High

                let band (a, b) = {
                %s
                    Mid
                }
                """.formatted(guards);
    }

    private static Compilation compiled(String guards) {
        String source = model(guards);
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code().toString()).toList(), source);
        return compilation;
    }

    private static String report(Compilation compilation) {
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }

    private static String report(String guards) {
        return report(compiled(guards));
    }

    /** The sum each row made for what nothing covers holds. */
    private static Set<Integer> sumsOfTheRows(Compilation compilation) {
        String text = GeneratedRows.of(compilation, null, null,
                SourceRendering.namedByIdentity(SourceLayouts.NONE)).text();
        Set<Integer> sums = new TreeSet<>();
        for (RowsOfABlock.Row row : RowsOfABlock.of(text)) {
            Matcher found = A_ROW.matcher(row.written());
            if (found.find()) {
                sums.add(Integer.parseInt(found.group(1)) + Integer.parseInt(found.group(2)));
            }
        }
        return sums;
    }

    /** Whether a row is owed at each point the comparison on {@code line} draws, as the report
     *  says it: the ones a row is owed at, and those no value can stand at. */
    private static Map<String, String> pointsOf(String report, int line) {
        Pattern owed = Pattern.compile("undecided whether a row is at the (ON|OFF|IN|OUT) point"
                + " \\(comparison@" + line + ":");
        Pattern excluded = Pattern.compile("no row can stand at the (ON|OFF|IN|OUT) point"
                + " \\(comparison@" + line + ":");
        Map<String, String> out = new TreeMap<>(Map.of("ON", "none", "OFF", "none", "IN", "none",
                "OUT", "none"));
        for (String each : report.split("\n")) {
            Matcher asked = owed.matcher(each);
            if (asked.find()) {
                out.put(asked.group(1), "owed");
            }
            Matcher none = excluded.matcher(each);
            if (none.find()) {
                out.put(none.group(1), "none");
            }
        }
        return out;
    }

    /** The line of the first guard of {@code guards} that holds {@code written}. */
    private static int lineOf(String guards, String written) {
        List<String> text = model(guards).lines().toList();
        return 1 + text.indexOf(text.stream().filter(each -> each.contains(written)).findFirst()
                .orElseThrow());
    }

    /** The first guard alone is read, and the second beside it is read to the same lines. */
    @Test
    void aSecondGuardOnTheSameSumIsReadBesideTheFirst() {
        String first = "    guard a + b >= 100 else Low";
        String alone = report(first);
        assertFalse(alone.contains(NOT_READ), alone);
        String both = report(first + "\n    guard a + b < 200 else High");
        assertFalse(both.contains(NOT_READ), both);
        assertTrue(both.contains("borders 2"), both);
    }

    /** The same from the other end, with the strict side of each line the other way, with the
     *  sum written another way, and with a third guard on it. */
    @Test
    void theOrderOfTheGuardsTheSideOfEachLineAndTheSpellingOfTheSumDoNotMatter() {
        for (String guards : List.of(
                "    guard a + b < 200 else High\n    guard a + b >= 100 else Low",
                "    guard a + b > 99 else Low\n    guard a + b <= 199 else High",
                "    guard a + b >= 100 else Low\n    guard b + a < 200 else High",
                "    guard a + b >= 100 else Low\n    guard a + b + 5 < 200 else High",
                "    guard a + b >= 100 else Low\n    guard 200 > a + b else High",
                "    guard a + b >= 100 else Low\n    guard 2 * a + 2 * b < 400 else High",
                "    guard a + b >= 100 else Low\n    guard a + b < 200 else High\n"
                        + "    guard a + b < 150 else High",
                "    guard a >= 0 else Low\n    guard a + b >= 100 else Low\n"
                        + "    guard a + b < 200 else High")) {
            String report = report(guards);
            assertFalse(report.contains(NOT_READ), guards + "\n" + report);
        }
    }

    /**
     * Both numbers from nought to ten, held to a sum of at least {@code least} and then asked
     * whether it is below {@code below}. The points a row is owed at are those a walk of every
     * pair finds a row at: the last sum below the line, the line, the sums between the way's
     * bound and the last below it, and those past the line. Each pair of bounds here leaves the
     * walk sums on both sides of the line, so the guard decides nothing already.
     */
    @Test
    void whatTheSecondGuardDrawsOverBoundedNumbersIsWhatAWalkOfEveryPairFinds() {
        for (int[] each : new int[][] {{0, 5}, {3, 10}, {10, 14}, {15, 19}, {19, 20}, {0, 20},
                {10, 20}}) {
            int least = each[0];
            int below = each[1];
            String guards = "    guard a >= 0 else Low\n    guard a <= 10 else Low\n"
                    + "    guard b >= 0 else Low\n    guard b <= 10 else Low\n"
                    + "    guard a + b >= " + least + " else Low\n"
                    + "    guard a + b < " + below + " else High";
            Compilation compilation = compiled(guards);
            String report = report(compilation);
            String name = "from " + least + " below " + below;
            assertFalse(report.contains(NOT_READ), name + "\n" + report);
            assertEquals(walked(least, below), pointsOf(report, lineOf(guards, "a + b < ")),
                    name);
            Set<Integer> sums = sumsOfTheRows(compilation);
            for (int sum : List.of(below - 1, below)) {
                assertEquals(walkFinds(least, sum, sum), sums.contains(sum),
                        name + ": a row at the sum " + sum + " of " + sums);
            }
        }
    }

    /** The points the comparison {@code sum < below} draws after {@code sum >= least}. */
    private static Map<String, String> walked(int least, int below) {
        Map<String, String> out = new TreeMap<>();
        out.put("ON", walkFinds(least, below - 1, below - 1) ? "owed" : "none");
        out.put("OFF", walkFinds(least, below, below) ? "owed" : "none");
        out.put("IN", walkFinds(least, least, below - 2) ? "owed" : "none");
        out.put("OUT", walkFinds(least, below + 1, Integer.MAX_VALUE) ? "owed" : "none");
        return out;
    }

    /** Whether some pair from nought to ten holds a sum of at least {@code least} and within the
     *  run from {@code from} to {@code to}. */
    private static boolean walkFinds(int least, int from, int to) {
        for (int a = 0; a <= 10; a++) {
            for (int b = 0; b <= 10; b++) {
                int sum = a + b;
                if (sum >= least && sum >= from && sum <= to) {
                    return true;
                }
            }
        }
        return false;
    }

    /** Rows at the sums either side of each line, over numbers that run to the ends of an
     *  {@code Int}: the sum is held to what a row can stand at and no further. */
    @Test
    void theRowsMadeForTheSecondGuardAreAtTheSumsEitherSideOfItsLine() {
        Compilation compilation = compiled("    guard a + b >= 100 else Low\n"
                + "    guard a + b < 200 else High");
        assertTrue(sumsOfTheRows(compilation).containsAll(List.of(99, 100, 199, 200)),
                sumsOfTheRows(compilation).toString());
    }

    /** Beside the greatest and the least {@code Int}, a row whose sum passes the type stops where
     *  it adds, and is no row: what the way holds the sum to takes none of them in. */
    @Test
    void theRowsMadeBesideTheEndsOfIntAreRowsTheSumOfWhichIsAnInt() {
        BigInteger greatest = BigInteger.valueOf(Long.MAX_VALUE);
        BigInteger least = BigInteger.valueOf(Long.MIN_VALUE);
        for (String guards : List.of(
                "    guard a + b >= 9223372036854775790 else Low\n"
                        + "    guard a + b < 9223372036854775800 else High",
                "    guard a + b >= -9223372036854775800 else Low\n"
                        + "    guard a + b < -9223372036854775790 else High",
                "    guard a + b >= 100 else Low\n"
                        + "    guard a + b < 9223372036854775807 else High")) {
            Compilation compilation = compiled(guards);
            String text = GeneratedRows.of(compilation, null, null,
                    SourceRendering.namedByIdentity(SourceLayouts.NONE)).text();
            int made = 0;
            for (RowsOfABlock.Row row : RowsOfABlock.of(text)) {
                Matcher found = A_ROW.matcher(row.written());
                if (found.find()) {
                    made++;
                    BigInteger sum = new BigInteger(found.group(1))
                            .add(new BigInteger(found.group(2)));
                    assertTrue(sum.compareTo(greatest) <= 0 && sum.compareTo(least) >= 0,
                            guards + "\n a row with the sum " + sum + ": " + row.written());
                }
            }
            assertTrue(made > 0, "rows are made for " + guards + "\n" + text);
        }
    }

    /** A way holding the numbers to another form ties them, and says nothing a row at the line
     *  of the sum could meet. */
    @Test
    void aWayHoldingAnotherFormStillTiesTheNumbers() {
        for (String guards : List.of(
                "    guard a - b >= 0 else Low\n    guard a + b < 200 else High",
                "    guard a + b >= 100 else Low\n    guard a - b < 10 else High")) {
            String report = report(guards);
            assertTrue(report.contains(NOT_READ), guards + "\n" + report);
        }
    }

    /** A way that does not hold on both sides of the line, as far from it as a row beside it can
     *  be, is not met by such a row, and the guard after it is read as it was. */
    @Test
    void aWayEndingAtTheLineLeavesNoRoomAndStillTiesTheNumbers() {
        String report = report("    guard a + b <= 200 else Low\n    guard a + b < 200 else High");
        assertTrue(report.contains(NOT_READ), report);
    }
}
