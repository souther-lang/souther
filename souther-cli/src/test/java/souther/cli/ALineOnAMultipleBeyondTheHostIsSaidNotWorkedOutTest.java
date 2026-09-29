package souther.cli;

import org.junit.jupiter.api.Test;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;

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

    private static String reported(String example) throws Exception {
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

        PrintStream wasOut = System.out;
        PrintStream wasErr = System.err;
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        ByteArrayOutputStream err = new ByteArrayOutputStream();
        System.setOut(new PrintStream(out, true, StandardCharsets.UTF_8));
        System.setErr(new PrintStream(err, true, StandardCharsets.UTF_8));
        try {
            Main.guarded(() -> Main.dispatch(new String[] {"examples", file.toString()}));
        } finally {
            System.setOut(wasOut);
            System.setErr(wasErr);
        }
        return out.toString(StandardCharsets.UTF_8) + err.toString(StandardCharsets.UTF_8);
    }

    @Test
    void theMeasurementNamesTheRuleItCouldNotReadRatherThanFailing() throws Exception {
        String said = reported("");

        assertFalse(said.contains("internal compiler error"), () -> "the run completes:\n" + said);
        assertTrue(said.contains("no exact representation"),
                () -> "and says the line could not be worked out:\n" + said);
    }

    @Test
    void theSameWhereAnExampleRunsTheModel() throws Exception {
        String said = reported("""

                example take
                    | "one" : (H { a = A(50.0m) }) -> No
                """);

        assertFalse(said.contains("internal compiler error"), () -> "the run completes:\n" + said);
        assertTrue(said.contains("no exact representation"),
                () -> "and says the line could not be worked out:\n" + said);
    }
}
