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
 * A line the rows do not tell from the line beside it is offered a row, and it is the row the
 * sentence names.
 *
 * <p>What such a line asks for is an input the two lines answer differently at, which is not a
 * point of either of them: the four points can all be met and the question still stands. So it is
 * looked for at the line's own {@code OFF} point — where the model refuses everything — inside the
 * region where the line beside it keeps a row, and anything composed there answers the two
 * differently.
 *
 * <p><b>Two runs of one model, and the second is the first with what it offered written down.</b> A
 * test that showed a row appearing in the block would pass over a row composed anywhere the point
 * admits, which is most places and settles nothing. What makes the row the right one is that
 * writing it takes the sentence away.
 */
class ARowThatTellsALineFromTheOneBesideItIsComposedTest {

    /** The lines the rows of this model leave standing beside the ones it draws. */
    private static final List<String> STANDING = List.of(
            "no row tells `-2 * x + y = 0` from `-3 * x + y = 0`,"
                    + " and a row at `x = 1, y = 3` would",
            "no row tells `y = x` from `y = 0`, and a row at `x = 1, y = 0` would",
            "no row tells `x + 2 * y = 60` from `y = 23`, and a row at `x = 20, y = 20` would");

    /** Rows at every point of every line this model draws, and at nothing else. */
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
    void aRowIsOfferedAtTheInputTheSentenceNames() {
        String report = run(over(ROWS));

        assertEquals(STANDING, findings(report),
                () -> "every point of every line is met and three lines beside them still"
                        + " stand:\n" + report);
        // The same inputs, and in the same words the sentences above use. A row offered at a place
        // the sentence does not name is a person shown one input and handed another.
        assertEquals(List.of("(1, 3)", "(1, 0)", "(20, 20)"), offered(report),
                () -> "and a row is offered at each of the inputs those sentences name:\n"
                        + report);
    }

    @Test
    void andWritingWhatWasOfferedTellsThoseLinesApart() {
        String report = run(over(ROWS + """

                  | (1, 3)   -> false
                  | (1, 0)   -> false
                  | (20, 20) -> false"""));

        assertEquals(List.of("no row tells `y = x` from `-x + 2 * y = 0`,"
                        + " and a row at `x = 2, y = 1` would"), findings(report),
                () -> "the three rows tell the three lines from the ones that stood beside them,"
                        + " and the one left is the next line the family puts beside `y = x`:\n"
                        + report);
        assertEquals(List.of("(2, 1)"), offered(report),
                () -> "which is offered a row of its own:\n" + report);
        assertTrue(report.contains("obligations 12/12"),
                () -> "and the points the rows were already at are where they were:\n" + report);
    }

    /**
     * A line on an order that names no value beside it is looked for all the same.
     *
     * <p>Nothing stands one step outside {@code y <= 2.0m * x}: between any two decimals there is
     * another, so the point against the line out there is one the order cannot write and the border
     * owes no row at it. What the line refuses is not empty, though — it is every value above the
     * line — and an input the two lines part company at is one of those. Looked for at the point
     * instead, the search was never made and the block said nothing while the report asked for a
     * row.
     *
     * <p>What comes back here is a figure of this compiler's rather than a row, which is the other
     * half of the same rule: a side is never settled by looking, so what such a search says is that
     * it left something untried. That is a thing an author can act on; silence is not.
     */
    @Test
    void aLineOnAnOrderWithNoValueBesideItIsStillSearched() {
        String report = run("""
                module m

                behavior f : (x: Decimal, y: Decimal) -> Bool

                let f (x, y) = {
                    guard y <= 2.0m * x else false

                    true
                }

                example f
                  | (0.0m, 0.0m)   -> true
                  | (0.0m, 1.0m)   -> false
                  | (13.0m, 23.0m) -> true
                  | (12.0m, 24.0m) -> true
                """);

        assertEquals(List.of("no row tells `-2 * x + y = 0` from `-3 * x + y = 0`,"
                        + " and a row at `x = -1, y = -2` would"), findings(report),
                () -> "the rows meet every point this order owes one at and still leave a line"
                        + " standing:\n" + report);
        assertTrue(report.contains("no row for `-2 * x + y = 0 against -3 * x + y = 0` in `f`"),
                () -> "and the block says what looking for a row came to, rather than passing"
                        + " over a line whose point against it the order cannot write:\n" + report);
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

    /** What the report says about the lines beside the ones this model draws. */
    private static List<String> findings(String report) {
        List<String> said = new ArrayList<>();
        for (String line : report.split("\n")) {
            if (line.contains("no row tells")) {
                said.add(line.strip().replaceFirst("^! ", ""));
            }
        }
        return said;
    }

    /** The inputs of the rows the block offers, in the order they are offered. */
    private static List<String> offered(String report) {
        List<String> rows = new ArrayList<>();
        for (String line : report.split("\n")) {
            String said = line.strip();
            if (said.startsWith("| (") && said.endsWith("-> <?>")) {
                rows.add(said.substring(2, said.lastIndexOf(')') + 1).strip());
            }
        }
        return rows;
    }

    private static String run(String source) {
        try {
            Path file = Files.createTempDirectory("souther-apart").resolve("m.sou");
            Files.writeString(file, source);
            PrintStream out = System.out;
            PrintStream err = System.err;
            ByteArrayOutputStream said = new ByteArrayOutputStream();
            System.setOut(new PrintStream(said, true, StandardCharsets.UTF_8));
            System.setErr(new PrintStream(new ByteArrayOutputStream(), true,
                    StandardCharsets.UTF_8));
            try {
                Main.main(new String[] {"examples", "--generate", file.toString()});
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
