package souther.cli;

import org.junit.jupiter.api.Test;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * A row generated for a rewrite of an arm says which fork the rewrite is at.
 *
 * <p>The words a rewrite is named by carry no place, since a row's name stays in the source; two
 * forks with a {@code then} and an {@code else} each are rewritten under the same words. So such a
 * row is not named by them, and says over itself, with the fork's place, each rewrite it fills —
 * including two of the same words on one row, which are two things and not one said twice.
 */
class AGeneratedRowSaysWhichForkEachRewriteItFillsIsAtTest {

    /** Two {@code if}s, the second the first's {@code else}. */
    private static final String NESTED = """
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

    /** Two {@code if}s side by side, which one row with a negative `n` goes through the `then` of. */
    private static final String SIDE_BY_SIDE = """
            behavior f : (n: Int, a: Int) -> Int

            let f (n, a) = {
                let x = if n < 0 then a else 0
                let y = if n < 10 then a else 0
                x + y
            }

            example f
                | (-1, 0) -> 0
                | (5, 0) -> 0
                | (15, 0) -> 0
            """;

    @Test
    void eachRewriteOfTwoForksIsSaidAtItsOwnFork() throws Exception {
        String generated = generated("addon.sou", NESTED);

        assertEquals(List.of(
                        "// fills then answering as else (7:5)",
                        "// fills else answering as then (7:5)",
                        "// fills then answering as else (8:10)",
                        "// fills else answering as then (8:10)"),
                generated.lines().filter(line -> line.startsWith("// fills")).toList(),
                generated);
        assertFalse(generated.contains("\"then answering as else\""),
                "and no row is named by words the other fork's rewrite has too: " + generated);
    }

    @Test
    void twoRewritesOfTheSameWordsOnOneRowAreBothSaid() throws Exception {
        String generated = generated("twin.sou", SIDE_BY_SIDE);

        List<String> lines = generated.lines().toList();
        int first = lines.indexOf("// fills then answering as else (4:13)");
        assertEquals("// fills then answering as else (5:13)", lines.get(first + 1),
                "one row for both, and both over it: " + generated);
    }

    /** {@code souther examples --generate} over {@code source}, and what it printed. */
    private static String generated(String name, String source) throws Exception {
        Path file = Files.createTempDirectory("souther-generate").resolve(name);
        Files.writeString(file, source);
        PrintStream originalOut = System.out;
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        System.setOut(new PrintStream(out, true, StandardCharsets.UTF_8));
        try {
            Main.dispatch(new String[] {"examples", "--generate", file.toString()});
        } finally {
            System.setOut(originalOut);
        }
        return out.toString(StandardCharsets.UTF_8);
    }
}
