package souther.cli;

import org.junit.jupiter.api.Test;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;

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
}
