package souther.cli;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A newtype rebuilt in a helper and read by an operation the running tree expands is reported as
 * the same body written inline is.
 *
 * <p>The newtype's invariant keeps {@code String.matches} standing as a call, while
 * {@code Decimal.abs} is expanded into a fork in the tree that runs. Giving the rebuild a name
 * changes what the report says of nothing.
 */
class ARebuiltNewtypeReadByAnExpandedOperationReportsAsIfWrittenInlineTest {

    @TempDir
    static Path sources;

    private static final String AMOUNT = """
            data Amount = Decimal
                invariant representable = String.matches("[0-9]+", String.fromDecimal(value))
            """;

    @Test
    void aHelperThatRebuildsTheValueReportsWhatTheSameBodyInlineReports() throws Exception {
        Run inline = examples("""
                module probe.i

                %s
                behavior result : (input: Amount) -> Decimal

                let result (input) = {
                    guard Amount(input.value) as amount else unreachable "same value"
                    Decimal.abs(amount.value)
                }
                """.formatted(AMOUNT));
        Run helper = examples("""
                module probe.i

                %s
                let rebuild (input: Amount): Amount = {
                    guard Amount(input.value) as amount else unreachable "same value"
                    amount
                }

                behavior result : (input: Amount) -> Decimal

                let result (input) = Decimal.abs(rebuild(input).value)
                """.formatted(AMOUNT));
        assertEquals(0, inline.code(), inline::toString);
        assertEquals(0, helper.code(), helper::toString);
        assertFalse(measured(inline.out()).isEmpty(), inline::toString);
        assertEquals(measured(inline.out()), measured(helper.out()),
                () -> "inline:\n" + inline + "\nhelper:\n" + helper);
        // Equal to the inline report is not yet a report: both say that the invariant is not
        // accounted for and that no row takes the decision.
        for (Run run : List.of(inline, helper)) {
            assertTrue(run.out().contains("measurement: partial"), run::toString);
            assertTrue(run.out().contains("adequacy: not satisfied"), run::toString);
        }
    }

    /** The helper alone, with nothing expanded over what it builds, is the control that the
     *  report was never the part that failed. */
    @Test
    void aHelperWhoseValueNothingExpandsReportsAsWell() throws Exception {
        Run helper = examples("""
                module probe.i

                %s
                let rebuild (input: Amount): Amount = {
                    guard Amount(input.value) as amount else unreachable "same value"
                    amount
                }

                behavior result : (input: Amount) -> Decimal

                let result (input) = rebuild(input).value
                """.formatted(AMOUNT));
        assertEquals(0, helper.code(), helper::toString);
        assertTrue(helper.out().contains("adequacy: not satisfied"), helper::toString);
    }

    /** What the report says about {@code result}; a place in it names its line and the helper it
     *  is in, which are about how the source is written and not about what is measured. */
    private static List<String> measured(String report) {
        List<String> out = new ArrayList<>();
        boolean inside = false;
        for (String line : report.split("\n")) {
            if (line.startsWith("  result ")) {
                inside = true;
            } else if (inside && !line.startsWith("    ")) {
                break;
            }
            if (inside) {
                out.add(line.replaceAll(" \\(\\d+:\\d+\\)( in \\S+)?", ""));
            }
        }
        return out;
    }

    private record Run(int code, String out, String err) {
        @Override
        public String toString() {
            return "exit " + code + "\n--- out\n" + out + "--- err\n" + err;
        }
    }

    private static Run examples(String source) throws Exception {
        Path file = Files.createTempDirectory(sources, "run").resolve("probe.sou");
        Files.writeString(file, source);
        PrintStream originalOut = System.out;
        PrintStream originalErr = System.err;
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        ByteArrayOutputStream err = new ByteArrayOutputStream();
        System.setOut(new PrintStream(out, true, StandardCharsets.UTF_8));
        System.setErr(new PrintStream(err, true, StandardCharsets.UTF_8));
        int code;
        try {
            code = Main.guarded(() -> Main.dispatch(new String[] {"examples", file.toString()}));
        } finally {
            System.setOut(originalOut);
            System.setErr(originalErr);
        }
        return new Run(code, out.toString(StandardCharsets.UTF_8),
                err.toString(StandardCharsets.UTF_8));
    }
}
