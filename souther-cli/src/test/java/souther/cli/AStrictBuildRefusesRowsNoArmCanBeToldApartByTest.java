package souther.cli;

import org.junit.jupiter.api.Test;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A strict build refuses rows every arm of the body answers alike on, where the arms are decided
 * by a comparison between two inputs: rewritten as its sibling, no arm answers any of them
 * differently, and a row exists that it would.
 *
 * <p>Every row holds the amount at nothing, which is what each arm answers on either side of the
 * ninety days, so a body that never hands the add-on out passes every one of them as well.
 */
class AStrictBuildRefusesRowsNoArmCanBeToldApartByTest {

    private static final String MODEL = """
            data Megabytes = Int

            behavior usable : (purchased: Date, on: Date, amount: Megabytes) -> Megabytes

            let usable (purchased, on, amount) = {
                let elapsed = Date.daysBetween(purchased, on)
                if elapsed < 0 then Megabytes(0)
                else if elapsed < 90 then amount
                else Megabytes(0)
            }

            example usable
                | (Date("1970-01-02"), Date("1970-01-01"), Megabytes(0)) -> Megabytes(0)
                | (Date("1970-01-01"), Date("1970-01-01"), Megabytes(0)) -> Megabytes(0)
                | (Date("1970-01-03"), Date("1970-01-01"), Megabytes(0)) -> Megabytes(0)
                | (Date("1969-10-04"), Date("1970-01-01"), Megabytes(0)) -> Megabytes(0)
                | (Date("1969-10-03"), Date("1970-01-01"), Megabytes(0)) -> Megabytes(0)
                | (Date("1969-10-02"), Date("1970-01-01"), Megabytes(0)) -> Megabytes(0)
            """;

    @Test
    void everyArmRewrittenAsItsSiblingIsAGapTheStrictBuildRefuses() throws Exception {
        Path file = Files.createTempDirectory("souther-strict").resolve("addon.sou");
        Files.writeString(file, MODEL);
        PrintStream originalOut = System.out;
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        System.setOut(new PrintStream(out, true, StandardCharsets.UTF_8));
        int code;
        try {
            code = Main.dispatch(new String[] {"examples", file.toString(), "--strict"});
        } finally {
            System.setOut(originalOut);
        }
        String report = out.toString(StandardCharsets.UTF_8);

        assertTrue(report.contains("replacement 0/4"),
                "each of the four arms as its sibling, none told apart: " + report);
        assertEquals(1, code, "and the strict build refuses over them: " + report);
    }

    /**
     * Each of the four says which arm answered as which, and the fork it is an arm of: the two
     * {@code if}s are told apart by where each is written, and the two rewrites at one of them by
     * which arm is rewritten.
     */
    @Test
    void eachGapNamesTheArmAndTheArmItAnsweredAs() throws Exception {
        Path file = Files.createTempDirectory("souther-strict").resolve("addon.sou");
        Files.writeString(file, MODEL);
        PrintStream originalOut = System.out;
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        System.setOut(new PrintStream(out, true, StandardCharsets.UTF_8));
        try {
            Main.dispatch(new String[] {"examples", file.toString(), "--strict"});
        } finally {
            System.setOut(originalOut);
        }
        String report = out.toString(StandardCharsets.UTF_8);

        assertEquals(List.of(
                        "! no row would come out differently if `then` (7:5) answered as `else`",
                        "! no row would come out differently if `else` (7:5) answered as `then`",
                        "! no row would come out differently if `then` (8:10) answered as `else`",
                        "! no row would come out differently if `else` (8:10) answered as `then`"),
                report.lines().map(String::strip)
                        .filter(line -> line.startsWith("! no row would come out differently"))
                        .toList(),
                report);
    }

    /**
     * A row generated for one of them is offered under the same words, so a reader can tell which
     * gap each row is for.
     */
    @Test
    void aRowGeneratedForAGapIsNamedByTheArms() throws Exception {
        Path file = Files.createTempDirectory("souther-strict").resolve("addon.sou");
        Files.writeString(file, MODEL);
        PrintStream originalOut = System.out;
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        System.setOut(new PrintStream(out, true, StandardCharsets.UTF_8));
        try {
            Main.dispatch(new String[] {"examples", "--generate", file.toString()});
        } finally {
            System.setOut(originalOut);
        }
        String generated = out.toString(StandardCharsets.UTF_8);

        assertTrue(generated.contains("\"then answering as else\""),
                "a row named for the arm and the arm it answers as: " + generated);
    }
}
