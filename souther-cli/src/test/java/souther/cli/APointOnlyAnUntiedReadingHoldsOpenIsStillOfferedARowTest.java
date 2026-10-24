package souther.cli;

import org.junit.jupiter.api.Test;

import souther.cli.CliProcess.Ran;

import java.nio.file.Files;
import java.nio.file.Path;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A point of a line that nothing but a reading no row can settle it through holds open is offered
 * the row that settles it.
 *
 * <p>{@code check(if a > 0 then a else 11)} reads {@code x <= 10} at {@code a = 10} and, where the
 * caller's choice turns, at {@code a = 0}: the second is evidence about the line that is counted
 * neither for a point of it nor against it. The rows written stand at neither of the points that
 * the first reading ties to the line, and the second reading keeps them undecided. What an author
 * is told is which rows to write, since none that is already written can be at the point through
 * the reading that holds it open.
 */
class APointOnlyAnUntiedReadingHoldsOpenIsStillOfferedARowTest {

    private static final String MODEL = """
            module example.overlap

            behavior admit : (a: Int) -> Bool

            let admit (a) = check(if a > 0 then a else 11)

            let check (x: Int): Bool = x <= 10

            example admit
                | (50) -> false
                | (5) -> true
            """;

    @Test
    void theRowsThatSettleThePointsAreOfferedAndThePointsStayUndecided() throws Exception {
        Path file = Files.createTempDirectory("souther-untied").resolve("overlap.sou");
        Files.writeString(file, MODEL);

        Ran run = CliInProcess.run(new String[] {"examples", file.toString(), "--generate"});

        assertEquals(0, run.code(), run.out() + run.err());
        assertTrue(run.out().contains("? undecided whether a row is at the ON point"),
                "the point is still undecided until a row stands at it: " + run.out());
        assertTrue(run.out().contains("// fills ON point of comparison@overlap.sou:7:30")
                        && run.out().contains("| (10)"),
                "and the row at it is offered: " + run.out());
        assertTrue(run.out().contains("// fills OFF point of comparison@overlap.sou:7:30")
                        && run.out().contains("| (11)"),
                "and so is the row beside it: " + run.out());
    }
}
