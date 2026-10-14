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
        Ran ran = run("--strict");

        assertTrue(ran.out().contains("replacement 0/4"),
                "each of the four arms as its sibling, none told apart: " + ran.out());
        assertEquals(1, ran.code(), "and the strict build refuses over them: " + ran.out());
    }

    /**
     * Each of the four says which arm answered as which, and the fork it is an arm of: the two
     * {@code if}s are told apart by where each is written, and the two rewrites at one of them by
     * which arm is rewritten.
     */
    @Test
    void eachGapNamesTheArmAndTheArmItAnsweredAs() throws Exception {
        String report = run("--strict").out();

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
     * A row generated for one of them is offered under the words the report says the arms in. Not
     * the fork's place: a row's name stays in the source, where a coordinate would go stale, so
     * rows for the same pair of arms at the two {@code if}s are offered under one name.
     */
    @Test
    void aRowGeneratedForAGapIsNamedByTheArms() throws Exception {
        String generated = run("--generate").out();

        assertTrue(generated.contains("\"then answering as else\""),
                "a row named for the arm and the arm it answers as: " + generated);
    }

    private record Ran(int code, String out) {}

    /** {@code souther examples} over the model with {@code flag}, and what it printed. */
    private static Ran run(String flag) throws Exception {
        Path file = Files.createTempDirectory("souther-strict").resolve("addon.sou");
        Files.writeString(file, MODEL);
        PrintStream originalOut = System.out;
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        System.setOut(new PrintStream(out, true, StandardCharsets.UTF_8));
        int code;
        try {
            code = Main.dispatch(new String[] {"examples", file.toString(), flag});
        } finally {
            System.setOut(originalOut);
        }
        return new Ran(code, out.toString(StandardCharsets.UTF_8));
    }
}
