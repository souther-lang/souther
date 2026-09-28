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
 * A guard at a decimal whose scale is past what a {@code BigDecimal} has names the classes it parts
 * without writing the decimal out.
 *
 * <p>Squaring a tenth doubles its scale, so thirty-two squarings put it at a scale no {@code int}
 * holds. The analysis holds that value compactly and reads the rule without incident; the class
 * below the line is named by the line, and naming it is where the value used to be written out in
 * full — a power of ten with more digits than any number the host builds.
 */
class ALineAtAFineDecimalIsNamedWithoutWritingItOutTest {

    @Test
    void theExamplesRunSaysWhatItFoundRatherThanFailing() throws Exception {
        StringBuilder model = new StringBuilder("""
                module probe.crash

                let sq (x: Decimal): Decimal = x * x

                let t0 = 0.1m
                """);
        for (int i = 1; i <= 32; i++) {
            model.append("let t").append(i).append(" = sq(t").append(i - 1).append(")\n");
        }
        model.append("""

                data A = Decimal
                data H = { a: A }
                data Ok
                data No
                data Verdict = Ok | No

                behavior take : (h: H) -> Verdict
                let take (h) = { guard h.a.value <= t32 else Ok
                    No }

                example take
                    | "one" : (H { a = A(50.0m) }) -> No
                """);
        Path file = Files.createTempDirectory("souther-fine-line").resolve("crash.sou");
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
        String said = out.toString(StandardCharsets.UTF_8) + err.toString(StandardCharsets.UTF_8);

        assertFalse(said.contains("internal compiler error"), () -> "the run completes:\n" + said);
        // Reached the example at all, so the absence above is of a failure and not of a run.
        assertTrue(said.contains("This example does not hold"),
                () -> "the run reports on the example:\n" + said);
        assertTrue(said.length() < 100_000,
                () -> "and says it in space that does not grow with the scale: " + said.length());
    }
}
