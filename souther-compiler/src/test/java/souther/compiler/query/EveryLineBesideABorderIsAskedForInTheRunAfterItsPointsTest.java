package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.SourceRendering;
import souther.compiler.report.AdequacyReport;
import souther.compiler.report.GeneratedRows;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Pasting the block whole and answering it reaches the state where nothing is owed, over borders
 * whose rows leave several lines of the family standing at once.
 *
 * <p>The order is the specification's: a line beside a border is asked about once a row stands at
 * every point of it, so the first block is the points and the second is the lines. What this holds
 * is that the second is every line — not the first one a walk over the family reached, with the next
 * left for the run after it — and that answering it leaves nothing: no line moved along by a row that
 * only answered it at the threshold it happened to stand at, and no line left owed because the only
 * input that settles it is on the side of the border a search did not look at.
 *
 * <p>The model's three guards each leave lines standing. {@code y >= x} leaves two, which a run
 * naming one line per border asked for a run apart, and {@code y <= -1/2 * x + 30} leaves one that
 * only a row the model keeps can rule out: under the guards before it, nothing the model refuses
 * there is within reach of the rows it keeps.
 */
class EveryLineBesideABorderIsAskedForInTheRunAfterItsPointsTest {

    private static final String MODEL = """
            module example.region

            behavior inside : (x: Int, y: Int) -> Bool

            let inside (x, y) = {
                guard y <= 2 * x else false
                guard y >= x else false
                guard y <= (- 1/2 * x + 30) else false

                true
            }
            """;

    /** Every line the rows of the points leave standing, in the report's own words. */
    private static final Set<String> EVERY_LINE_LEFT_STANDING = new TreeSet<>(List.of(
            "no row tells `-2 * x + y = 0` from `-3 * x + y = 0`",
            "no row tells `y = x` from `y = 0`",
            "no row tells `y = x` from `-x + 2 * y = 0`",
            "no row tells `0.5 * x + y = 30` from `x + y = 36`",
            "no row tells `0.5 * x + y = 30` from `x + 3 * y = 84`"));

    private static final Pattern ROW = Pattern.compile("\\((-?\\d+),\\s*(-?\\d+)\\)\\s*->\\s*<\\?>");

    private static final Pattern A_LINE_NOT_TOLD_APART =
            Pattern.compile("no row tells `[^`]+` from `[^`]+`");

    @Test
    void thePointsComeFirstAndAskNothingOfTheLines() {
        assertEquals(Set.of(), linesNotToldApart(report(MODEL)),
                () -> "no line is asked about before a row stands at its points:\n"
                        + report(MODEL));
        assertFalse(rowsOffered(MODEL).isEmpty(), () -> "the points are:\n" + block(MODEL));
    }

    @Test
    void theRunAfterThePointsAsksForEveryLineLeftStanding() {
        String points = answered(MODEL, rowsOffered(MODEL));

        assertEquals(EVERY_LINE_LEFT_STANDING, linesNotToldApart(report(points)),
                () -> "every line the rows leave standing, and not the first of each border's:\n"
                        + report(points));
    }

    @Test
    void andAnsweringThatBlockLeavesNothingOwed() {
        String points = answered(MODEL, rowsOffered(MODEL));
        List<String> forTheLines = rowsOffered(points);
        assertFalse(forTheLines.isEmpty(), () -> "the lines are asked for:\n" + block(points));

        String lines = answered(points, forTheLines);
        assertEquals(List.of(), marked(report(lines)),
                () -> "nothing is left owed:\n" + report(lines));
        assertEquals("", block(lines), () -> "and nothing is offered a third time");
    }

    /**
     * Left unanswered, the rows are owed their answers and nothing else.
     *
     * <p>A row waiting for its answer ran, and what it ran to is not what the model owes there. Read
     * as evidence about a rewrite of the body, a body every row of which is waiting would be asked
     * as though it had no fork, and the block would offer the rows already written as rows telling
     * the body from its own answers — on every run, without end.
     */
    @Test
    void rowsLeftWaitingForTheirAnswersAreOwedTheirAnswersAndNothingElse() {
        // Pasted whole each time and never answered, until the block has nothing more to offer:
        // the points, then the lines, then nothing. Never a row already written.
        String model = MODEL;
        Set<String> written = new TreeSet<>();
        for (int run = 1; !rowsOffered(model).isEmpty(); run++) {
            String sofar = model;
            // Compared by the input, since the block lines its columns up afresh each run.
            for (String offered : rowsOffered(model)) {
                assertFalse(written.contains(inputOf(offered)),
                        () -> "a row already written is not offered again: " + offered + "\n"
                                + block(sofar));
            }
            assertTrue(run <= 2, "the block runs dry once the points and the lines are written");
            rowsOffered(model).forEach(each -> written.add(inputOf(each)));
            model = unanswered(model, rowsOffered(model));
        }
        Set<String> codes = codesIn(model);
        assertTrue(codes.contains("E1934"), () -> "the rows are owed their answers: " + codes);
        assertFalse(codes.contains("E1939"),
                () -> "and no rewrite of the body is said to be untold by rows that state nothing: "
                        + codes);
    }

    /** The lines the report says no row tells apart. */
    private static Set<String> linesNotToldApart(String human) {
        Set<String> out = new TreeSet<>();
        Matcher found = A_LINE_NOT_TOLD_APART.matcher(human);
        while (found.find()) {
            out.add(found.group());
        }
        return out;
    }

    /** The lines the report marks as work left. */
    private static List<String> marked(String human) {
        return human.lines().map(String::strip).filter(line -> line.startsWith("! ")).toList();
    }

    /** The rows the block offers, as an author would copy them. */
    private static List<String> rowsOffered(String model) {
        List<String> out = new ArrayList<>();
        for (String line : block(model).lines().toList()) {
            String row = line.strip();
            if (row.startsWith("| ") && ROW.matcher(row).find()) {
                out.add(row);
            }
        }
        return out;
    }

    /** The input an offered row is written at. */
    private static String inputOf(String row) {
        Matcher at = ROW.matcher(row);
        assertTrue(at.find(), row);
        return at.group(1) + "," + at.group(2);
    }

    /** The model with those rows written into its block, each answered as the model owes. */
    private static String answered(String model, List<String> rows) {
        List<String> written = new ArrayList<>();
        for (String row : rows) {
            Matcher at = ROW.matcher(row);
            assertTrue(at.find(), row);
            long x = Long.parseLong(at.group(1));
            long y = Long.parseLong(at.group(2));
            boolean inside = y <= 2 * x && y >= x && 2 * y <= 60 - x;
            written.add(row.substring(0, row.length() - "<?>".length()) + inside);
        }
        return withRows(model, written);
    }

    /** The same, with every answer left owed. */
    private static String unanswered(String model, List<String> rows) {
        return withRows(model, rows);
    }

    private static String withRows(String model, List<String> rows) {
        StringBuilder out = new StringBuilder(model);
        if (!model.contains("example inside")) {
            out.append(System.lineSeparator()).append("example inside")
                    .append(System.lineSeparator());
        }
        for (String row : rows) {
            out.append("    ").append(row).append(System.lineSeparator());
        }
        return out.toString();
    }

    /** The codes this model's gaps are reported under, at the level a build warns at. */
    private static Set<String> codesIn(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Level.ALL);
        compilation.answerEverything();
        Set<String> out = new TreeSet<>();
        for (Db.Found each : compilation.db().allReports()) {
            Diagnostic said = each.report().diagnostic();
            if (!each.report().isError() && said.code() != null) {
                out.add(said.code());
            }
        }
        return out;
    }

    private static String block(String model) {
        Compilation measured = measured(model);
        return GeneratedRows.of(measured, "example.region", null,
                SourceRendering.namedByIdentity(measured.texts())).text();
    }

    private static String report(String model) {
        Compilation measured = measured(model);
        return AdequacyReport.of(measured)
                .human(SourceRendering.namedByIdentity(measured.texts()));
    }

    private static Compilation measured(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation;
    }
}
