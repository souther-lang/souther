package souther.cli;

import org.junit.jupiter.api.Test;

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

    /**
     * Two {@code if}s side by side on one condition, so every row goes through the {@code then}
     * of both or the {@code else} of both: whichever row a block hands for one rewrite of a
     * {@code then} is the row for the other.
     */
    private static final String SIDE_BY_SIDE = """
            behavior f : (n: Int, a: Int) -> Int

            let f (n, a) = {
                let x = if n < 0 then a else 0
                let y = if n < 0 then a else 0
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

    /**
     * Two forks of code this build holds no source of, in two definitions: the rewrite of each is
     * said with the definition that wrote it, so the two rows for them are two rows for two
     * things.
     */
    @Test
    void eachRewriteOfALibraryForkIsSaidByTheDefinitionThatWroteIt() throws Exception {
        String generated = generated("spread.sou", """
                behavior spread : (a: Int, b: Int) -> Int

                let spread (a, b) = Int.max(a, b) - Int.min(a, b)

                example spread
                    | (0, 0) -> 0
                    | (3, 3) -> 0
                """);

        assertEquals(List.of(
                        "// fills else answering as then (in a fork of `souther.int.max` this build"
                                + " holds no source of)",
                        "// fills else answering as then (in a fork of `souther.int.min` this build"
                                + " holds no source of)"),
                generated.lines().filter(line -> line.startsWith("// fills")).toList(),
                generated);
        assertFalse(generated.contains("\"else answering as then\""),
                "and neither row is named by words the other has too: " + generated);
    }

    /**
     * Two forks of one definition this build holds no source of are said in the same words and at
     * the same place, which is all this build can say of them. They are still two, so neither is
     * dropped as a repeat of the other and no row is named by words that are both of theirs.
     */
    @Test
    void twoForksOfOneLibraryDefinitionAreTwoThingsThoughTheyAreSaidAlike() throws Exception {
        String generated = generated("clamp.sou", """
                data Ok = { n: Int }
                data Err
                data Outcome = Ok | Err

                behavior kept : (n: Int) -> Outcome

                let kept (n) = Ok { n = Int.clamp(0, 10, n) }

                example kept
                    | (-5) -> Ok
                    | (5) -> Ok
                    | (15) -> Ok
                """);

        assertEquals(2, generated.lines().filter(line -> line.startsWith(
                        "// no row for `then answering as else` (in a fork of `souther.int.clamp`"))
                        .count(),
                "the rewrite of each fork's `then` is said, once each: " + generated);
        assertFalse(generated.contains("\"else answering as then\""),
                "and the row for one fork's `else` is not named by words the other's has: "
                        + generated);
    }

    /** {@code souther examples --generate} over {@code source}, and what it printed. */
    private static String generated(String name, String source) throws Exception {
        Path file = Files.createTempDirectory("souther-generate").resolve(name);
        Files.writeString(file, source);
        return CliInProcess.run("examples", "--generate", file.toString()).out();
    }
}
