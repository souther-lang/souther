package souther.cli;

import org.junit.jupiter.api.Test;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What the block under a module's declarations prints for a point read at several positions.
 *
 * <p>One clause under the mark for what the readings met, and one line under it per reading. The
 * two counts are different questions about the same point — a reason is a thing to act on and a
 * reading is where the line was read — and a sentence that said the reason once per reading would
 * leave a reader counting repetitions of a clause that identifies nothing
 * (spec §an-obligations-explanation-names-each-distinct-reason-once).
 *
 * <p>Held as the block whole rather than as the absence of a repeat. A report that said no reason
 * at all repeats nothing, and is the other way to get this wrong.
 */
class AnObligationSaysEachReasonOnceAndEveryReadingTest {

    /**
     * One clause of an author's, read at three positions, and past what an observation can hold.
     *
     * <p>Three behaviors take the same {@code Draft}, so the line {@code Amount} draws is read at
     * three positions and owed once for the module. The rows are too large to observe, so every one
     * of the three readings meets the same thing: a limit that stopped the observation.
     */
    private static final String READ_AT_THREE_POSITIONS = """
            module example.b

            data Amount = Int
                invariant value >= 0 && value <= 1000

            data Item = { a: String, b: String, c: String }
            data Group = { items: List<Item> }

            data Draft = { groups: List<Group>, cost: Amount }
            data Ok = { n: Int }

            behavior take : (request: Draft) -> Ok
                constructs Ok

            let take (request) = Ok { n = request.cost.value }

            behavior takeAgain : (request: Draft) -> Ok
                constructs Ok

            let takeAgain (request) = Ok { n = request.cost.value }

            behavior takeOnceMore : (request: Draft) -> Ok
                constructs Ok

            let takeOnceMore (request) = Ok { n = request.cost.value }

            let someItems (n: Int): List<Item> =
                List.map({ (i) -> Item { a = "x", b = "x", c = "x" } }, List.rangeInclusive(1, n))

            let someGroups (n: Int): List<Group> =
                List.map({ (i) -> Group { items = someItems(64) } }, List.rangeInclusive(1, n))

            example take
                | (Draft { groups = someGroups(64), cost = Amount(0) }) -> Ok { n = 0 }

            example takeAgain
                | (Draft { groups = someGroups(64), cost = Amount(0) }) -> Ok { n = 0 }

            example takeOnceMore
                | (Draft { groups = someGroups(64), cost = Amount(0) }) -> Ok { n = 0 }
            """;

    /**
     * The point's block, whole: the mark with one clause, and the three readings under it.
     *
     * <p>Written out rather than searched for, because what this fixes is the shape of the block
     * and not the presence of a word in it. The three readings differ only in the behavior that
     * read the line, which is what the reason said once is said about.
     */
    @Test
    void thePointSaysItsReasonOnceAndNamesEveryReading() throws Exception {
        Run run = examples(READ_AT_THREE_POSITIONS);

        assertTrue(run.out().contains("""
                      ? undecided whether a row is at the ON point value = 0 (invariant Amount #1)\
                , and the observation of it was stopped by a limit, so where it stands could not be\
                 read
                          · read as take/request.cost: = 0
                          · read as takeAgain/request.cost: = 0
                          · read as takeOnceMore/request.cost: = 0
                """),
                () -> "one reason under the mark and one line per reading:\n" + run.out());
    }

    /**
     * And the counts are what they are: four points, each with one clause, twelve readings.
     *
     * <p>Counted over the whole block, so that a clause repeated at any of the four is a failure
     * here whichever one it is.
     */
    @Test
    void noPointRepeatsAReasonAndNoReadingIsLeftOut() throws Exception {
        Run run = examples(READ_AT_THREE_POSITIONS);

        assertEquals(4, run.out().lines()
                        .filter(line -> line.contains("? undecided whether a row is at")).count(),
                () -> "the module's declarations owe four rows:\n" + run.out());
        assertEquals(4, run.out().lines()
                        .filter(line -> line.contains("the observation of it was stopped by a"
                                + " limit, so where it stands could not be read")).count(),
                () -> "and each says what its readings met once:\n" + run.out());
        assertEquals(12, run.out().lines()
                        .filter(line -> line.contains("· read as ")).count(),
                () -> "while every reading of every point is still named:\n" + run.out());
    }

    private record Run(int code, String out, String err) {}

    private static Run examples(String model, String... extra) throws Exception {
        Path file = Files.createTempDirectory("souther-one-reason").resolve("model.sou");
        Files.writeString(file, model);
        List<String> args = new ArrayList<>(List.of("examples", file.toString()));
        args.addAll(List.of(extra));
        PrintStream wasOut = System.out;
        PrintStream wasErr = System.err;
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        ByteArrayOutputStream err = new ByteArrayOutputStream();
        System.setOut(new PrintStream(out, true, StandardCharsets.UTF_8));
        System.setErr(new PrintStream(err, true, StandardCharsets.UTF_8));
        int code;
        try {
            code = Main.dispatch(args.toArray(String[]::new));
        } finally {
            System.setOut(wasOut);
            System.setErr(wasErr);
        }
        return new Run(code, out.toString(StandardCharsets.UTF_8),
                err.toString(StandardCharsets.UTF_8));
    }
}
