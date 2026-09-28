package souther.cli;

import org.junit.jupiter.api.Test;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.PrintStream;
import java.io.UncheckedIOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A row at each of a border's points shows the line has not moved, and shows nothing about how it
 * runs.
 *
 * <p>The four points are one place on a line and its neighbours, so a model whose rows answer every
 * one of them can be a model weighing a position differently and no row written would say so:
 * {@code y <= 2 * x} and {@code y <= 3 * x} are two models, and the rows below hold under both. What
 * says which of them the model draws is a row the two answer differently at, and the report names
 * one.
 *
 * <p><b>The first two below are one model with one row added.</b> Everything else is equal — the
 * same rules, the same points met, the same counts — and the row that arrives is the row the report
 * asked for. A test that only showed the sentence appearing would pass over a measure that says it
 * of every border there is.
 */
class ABorderEveryPointOfWhichHasARowMayStillBeTheWrongLineTest {

    /** The line the first guard draws, as the report names it. */
    private static final String THE_LINE = "-2 * x + y = 0";

    /** The line the rows below leave standing beside it, which is {@code y <= 3 * x}. */
    private static final String THE_OTHER = "-3 * x + y = 0";

    /**
     * The rows of the model this came from: four at the line the first guard draws and its
     * neighbours, and two more the generator offered.
     */
    private static final String ROWS = """
              | (0, 29)  -> false
              | (15, 29) -> false
              | (15, 30) -> false
              | (16, 31) -> false
              | (0, 0)   -> true
              | (0, 1)   -> false
              | (0, -1)  -> false
              | (0, -2)  -> false
              | (13, 23) -> true
              | (12, 24) -> false""";

    @Test
    void theRowsAtItsPointsLeaveALineBesideItStanding() {
        String report = run(over(ROWS));

        assertTrue(report.contains("obligations 12/12"),
                () -> "every point of every border has a row:\n" + report);
        assertEquals(List.of("! no row tells `" + THE_LINE + "` from `" + THE_OTHER + "`,"
                        + " and a row at `x = 1, y = 3` would"), said(report, THE_OTHER),
                () -> "and the rows still do not say which of the two lines the model draws:\n"
                        + report);
        assertTrue(report.contains("adequacy: not satisfied"),
                () -> "which is a row the model asks for:\n" + report);
    }

    @Test
    void andTheRowItAsksForIsTheRowThatSettlesIt() {
        String report = run(over(ROWS + "\n  | (1, 3) -> false"));

        assertEquals(List.of(), said(report, THE_OTHER),
                () -> "the row the report named answers one way under one line and the other way"
                        + " under the other, so the two are told apart:\n" + report);
        assertTrue(report.contains("obligations 12/12"),
                () -> "and the points it was already at are where they were:\n" + report);
    }

    /**
     * A bound on one position is owed nothing here: weighed one less it is nothing and weighed one
     * more it is the same line, so its four points are the whole of what it asks for.
     */
    @Test
    void aBorderOnOnePositionHasNoLineBesideItToBeToldFrom() {
        String report = run("""
                module m

                behavior f : (n: Int) -> Bool

                let f (n) = {
                    guard n <= 10 else false

                    true
                }

                example f
                  | (10) -> true
                  | (11) -> false
                  | (0)  -> true
                  | (99) -> false
                """);

        assertEquals(List.of(), said(report, "no row tells"),
                () -> "there is no other line to name:\n" + report);
        assertTrue(report.contains("adequacy: satisfied"),
                () -> "and nothing holds the verdict against it:\n" + report);
    }

    /**
     * Nor is a rule holding two dates apart. A date counts from an origin nobody wrote, so twice a
     * date is a number and no date — the weights such a rule has are the one pair a distance is
     * written with, and a line weighing one of them two is a line nobody can state.
     */
    @Test
    void norIsALineBetweenTwoPositionsNoModelCanWeigh() {
        String report = run("""
                module m

                behavior f : (from: Date, to: Date) -> Bool

                let f (from, to) = {
                    guard to >= from else false

                    true
                }

                example f
                  | (Date("2026-01-01"), Date("2026-01-01")) -> true
                  | (Date("2026-01-02"), Date("2026-01-01")) -> false
                  | (Date("2026-01-01"), Date("2026-12-31")) -> true
                  | (Date("2026-12-31"), Date("2026-01-01")) -> false
                """);

        assertEquals(List.of(), said(report, "no row tells"),
                () -> "a date has no weight but one, so there is no line beside this one:\n"
                        + report);
    }

    /** The model, with the rows handed in. */
    private static String over(String rows) {
        return """
                module m

                behavior f : (x: Int, y: Int) -> Bool

                let f (x, y) = {
                    guard y <= 2 * x else false
                    guard y >= x else false
                    guard x + 2 * y < 60 else false

                    true
                }

                example f
                %s
                """.formatted(rows);
    }

    /** What the report says about {@code about}, and nothing about anything else. */
    private static List<String> said(String report, String about) {
        List<String> said = new ArrayList<>();
        for (String line : report.split("\n")) {
            if (line.contains(about)) {
                said.add(line.strip());
            }
        }
        return said;
    }

    private static String run(String source) {
        try {
            Path file = Files.createTempDirectory("souther-borders").resolve("m.sou");
            Files.writeString(file, source);
            PrintStream out = System.out;
            PrintStream err = System.err;
            ByteArrayOutputStream said = new ByteArrayOutputStream();
            System.setOut(new PrintStream(said, true, StandardCharsets.UTF_8));
            System.setErr(new PrintStream(new ByteArrayOutputStream(), true,
                    StandardCharsets.UTF_8));
            try {
                Main.main(new String[] {"examples", file.toString()});
            } finally {
                System.setOut(out);
                System.setErr(err);
            }
            return said.toString(StandardCharsets.UTF_8);
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
    }
}
