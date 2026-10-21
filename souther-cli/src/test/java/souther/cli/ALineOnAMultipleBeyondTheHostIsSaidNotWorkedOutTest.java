package souther.cli;

import org.junit.jupiter.api.Test;

import souther.cli.CliProcess.Ran;

import java.nio.file.Files;
import java.nio.file.Path;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A guard on a multiple of a position, whose values beside the line are past what the host writes
 * out, is reported as a rule the compiler could not read and not as an internal error.
 *
 * <p>Squaring a tenth sixty-two times puts a multiple at the far end of the exponents a ratio holds.
 * The line is placed and held exactly; what cannot be written out is the whole number beside it, on
 * the position's own carrier. That is a fact about the run, and the measurement says which rule it
 * stopped on.
 */
class ALineOnAMultipleBeyondTheHostIsSaidNotWorkedOutTest {

    private static String reported(String example, int code) throws Exception {
        StringBuilder model = new StringBuilder("""
                module probe.follow

                let sq (x: Decimal): Decimal = x * x

                let t0 = 0.1m
                """);
        for (int i = 1; i <= 62; i++) {
            model.append("let t").append(i).append(" = sq(t").append(i - 1).append(")\n");
        }
        model.append("""

                data A = Decimal
                data H = { a: A }
                data Ok
                data No
                data Verdict = Ok | No

                behavior take : (h: H) -> Verdict
                let take (h) = { guard t62 * h.a.value <= 1.0m else Ok
                    No }
                """);
        model.append(example);
        Path file = Files.createTempDirectory("souther-multiple").resolve("probe.sou");
        Files.writeString(file, model);

        Ran ran = CliInProcess.run("examples", file.toString());
        String said = ran.out() + ran.err();
        assertEquals(code, ran.code(), said);
        return said;
    }

    @Test
    void theMeasurementNamesTheRuleItCouldNotReadRatherThanFailing() throws Exception {
        String said = reported("", 0);

        assertFalse(said.contains("internal compiler error"), () -> "the run completes:\n" + said);
        assertTrue(said.contains(THE_SIDE),
                () -> "and says the side of the line was not worked out:\n" + said);
        assertFalse(said.contains(THE_LINE),
                () -> "and not that the line has no place:\n" + said);
    }

    @Test
    void theSameWhereAnExampleRunsTheModel() throws Exception {
        String said = reported("""

                example take
                    | "one" : (H { a = A(50.0m) }) -> No
                """, 1);

        assertFalse(said.contains("internal compiler error"), () -> "the run completes:\n" + said);
        assertTrue(said.contains(THE_SIDE),
                () -> "and says the side of the line was not worked out:\n" + said);
        assertFalse(said.contains(THE_LINE),
                () -> "and not that the line has no place:\n" + said);
    }

    private static final String THE_SIDE = "a value beside it is one this compiler could not write out";

    private static final String THE_LINE = "its line falls at a number this compiler has no exact"
            + " representation for";
}
