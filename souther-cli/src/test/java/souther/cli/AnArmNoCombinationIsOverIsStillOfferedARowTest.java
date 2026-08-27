package souther.cli;

import org.junit.jupiter.api.Test;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * An arm a strict build refuses over is one something composes a row for.
 *
 * <p>The whole way through, because that is where it went wrong: the measure found the arms, the
 * generation was asked about them, and what it was asked of was the combinations the body settles
 * together — which this body has none of. A state transition written as one {@code match} inside
 * another consumes no two decided values into one, so no group forms, and the answer read off the
 * absent entry was that nothing here composes a row for the arm. Both rows are one input pair away
 * and the classes of both positions were read (issue #1009).
 *
 * <p>Written against the command rather than against the search. What an author is handed is this
 * block, and the parts between the measure and the block are where the question was lost.
 */
class AnArmNoCombinationIsOverIsStillOfferedARowTest {

    /** Two positions, two matches, one nested in the other, and rows through four of the six pairs.
     *  The flattened form of the tutorial's stopwatch, whose second {@code match} is a `let`. */
    private static final String NESTED = """
            module example.min

            data State = Ready | Running | Paused
            data Button = Start | Reset

            behavior press : (state: State, button: Button) -> State

            let press (state, button) =
                match button with
                    | Start ->
                        match state with
                            | Ready -> Running
                            | Running -> Paused
                            | Paused -> Running
                    | Reset ->
                        match state with
                            | Ready -> Ready
                            | Running -> Running
                            | Paused -> Ready

            example press
                | "start from ready"    : (Ready, Start)   -> Running
                | "start while running" : (Running, Start) -> Paused
                | "start while paused"  : (Paused, Start)  -> Running
                | "reset while paused"  : (Paused, Reset)  -> Ready
            """;

    @Test
    void theTwoUnreachedArmsAreOfferedTheRowsThatGoThroughThem() throws Exception {
        Run run = examples(NESTED, "--generate");

        assertEquals(0, run.code(), run.out() + run.err());
        // The gaps are still gaps: what changed is what is offered for them, not what is found.
        assertTrue(run.out().contains("! no row goes through `case Ready`"), run.out());
        assertTrue(run.out().contains("! no row goes through `case Running`"), run.out());

        assertTrue(run.out().contains("2 rows to fill what nothing covers"), run.out());
        assertTrue(run.out().contains("| \"case Ready\"   : (Ready, Reset)"), run.out());
        assertTrue(run.out().contains("| \"case Running\" : (Running, Reset)"), run.out());
        assertFalse(run.out().contains("nothing offers a row for `case Ready`"),
                "and nothing says the body does not reach them: " + run.out());
    }

    /** A fork inside a block, which runs where something applies it. */
    private static final String IN_A_BLOCK = """
            module example.block

            data Flag = On | Off

            behavior mark : (flags: List<Flag>) -> List<Int>

            let mark (flags) = List.map(f ->
                match f with
                    | On -> 1
                    | Off -> 0, flags)

            example mark
                | "one on" : ([On]) -> [1]
            """;

    /**
     * An arm this compiler cannot state a way into is said nothing about where a row goes through it.
     *
     * <p>No search composes a value for such an arm: the block runs under whatever applies it, so
     * what steers a row there is not a class of this behavior's inputs. What is offered here is a
     * row composed for the class the arm's own value is in, and running it goes through the arm — so
     * the work is in front of the reader, and a line saying nothing offers a row for it would send
     * them after work they have been handed.
     *
     * <p>The measurement is untouched: the gap is still a gap until the row is written and answered.
     */
    @Test
    void anArmInsideABlockIsSaidNothingAboutWhereAnOfferedRowGoesThroughIt() throws Exception {
        Run run = examples(IN_A_BLOCK, "--generate");

        assertTrue(run.out().contains("no row goes through `case Off`"), run.out());
        assertTrue(run.out().contains("| \"flags[*]=Off\" : ([Off])"),
                "a row whose run goes through the arm is offered: " + run.out());
        assertFalse(run.out().contains("nothing offers a row for `case Off`"),
                "so nothing says the arm has none: " + run.out());
    }

    private record Run(int code, String out, String err) {}

    private static Run examples(String model, String... extraArgs) throws Exception {
        Path file = Files.createTempDirectory("souther-arm").resolve("min.sou");
        Files.writeString(file, model);
        String[] args = new String[extraArgs.length + 2];
        args[0] = "examples";
        args[1] = file.toString();
        System.arraycopy(extraArgs, 0, args, 2, extraArgs.length);

        PrintStream originalOut = System.out;
        PrintStream originalErr = System.err;
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        ByteArrayOutputStream err = new ByteArrayOutputStream();
        System.setOut(new PrintStream(out, true, StandardCharsets.UTF_8));
        System.setErr(new PrintStream(err, true, StandardCharsets.UTF_8));
        int code;
        try {
            code = Main.dispatch(args);
        } finally {
            System.setOut(originalOut);
            System.setErr(originalErr);
        }
        return new Run(code, out.toString(StandardCharsets.UTF_8),
                err.toString(StandardCharsets.UTF_8));
    }
}
