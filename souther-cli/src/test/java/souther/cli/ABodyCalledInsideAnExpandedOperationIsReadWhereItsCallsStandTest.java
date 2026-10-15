package souther.cli;

import org.junit.jupiter.api.BeforeAll;
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

/**
 * A behavior called inside an operation the running tree expands is read in the tree its own
 * analysis reads, where the language's operations stay standing as calls.
 *
 * <p>The examples report walks a body in the tree that runs, where {@code Int.max} is expanded
 * into a fork. A call inside that fork enters the called behavior's body, which keeps
 * {@code Rational.toInt} standing. Writing the same expression inline is the control: what the
 * report says of the caller does not depend on whether a part of its body was given a name.
 */
class ABodyCalledInsideAnExpandedOperationIsReadWhereItsCallsStandTest {

    @TempDir
    static Path sources;

    /** The report of the body written inline, which the called forms of it are compared with. */
    private static Run inline;

    @BeforeAll
    static void reportTheInlineForm() throws Exception {
        inline = examples("""
                module probe.i

                behavior after : (taxable: Int) -> Int

                let after (taxable) = Int.max(0, Rational.toInt(DOWN, taxable / 100))

                example after
                    | (1000000) -> 10000
                """);
    }

    @Test
    void aCalledBodyReportsWhatTheSameBodyWrittenInlineReports() throws Exception {
        agree(inline, examples("""
                module probe.i

                behavior tax : (taxable: Int) -> Int

                let tax (taxable) = Rational.toInt(DOWN, taxable / 100)

                behavior after : (taxable: Int) -> Int

                let after (taxable) = Int.max(0, tax(taxable))

                example after
                    | (1000000) -> 10000
                """));
    }

    /** A body reached through another call is read in the same tree as the first. */
    @Test
    void aBodyCalledFromACalledBodyIsReadTheSameWay() throws Exception {
        agree(inline, examples("""
                module probe.i

                behavior cut : (taxable: Int) -> Int

                let cut (taxable) = Rational.toInt(DOWN, taxable / 100)

                behavior tax : (taxable: Int) -> Int

                let tax (taxable) = cut(taxable)

                behavior after : (taxable: Int) -> Int

                let after (taxable) = Int.max(0, tax(taxable))

                example after
                    | (1000000) -> 10000
                """));
    }

    /** An argument that names no position is read where the call was written, not in the body. */
    @Test
    void anArgumentThatIsNoPositionIsReadWhereTheCallIs() throws Exception {
        agree(examples("""
                module probe.i

                behavior after : (taxable: Int) -> Int

                let after (taxable) = Int.max(0, Rational.toInt(DOWN, (taxable - 1000) / 100))

                example after
                    | (1000000) -> 9990
                """), examples("""
                module probe.i

                behavior tax : (taxable: Int) -> Int

                let tax (taxable) = Rational.toInt(DOWN, taxable / 100)

                behavior after : (taxable: Int) -> Int

                let after (taxable) = Int.max(0, tax(taxable - 1000))

                example after
                    | (1000000) -> 9990
                """));
    }

    /** Both reports ran to the end and say the same of {@code after}, which is not two reports
     *  that both said nothing of it. */
    private static void agree(Run written, Run called) {
        assertEquals(0, written.code(), written::toString);
        assertEquals(0, called.code(), called::toString);
        assertFalse(measured(written.out()).isEmpty(), written::toString);
        assertEquals(measured(written.out()), measured(called.out()),
                () -> "inline:\n" + written + "\ncalled:\n" + called);
    }

    /** What the report says about {@code after}. A place in it names its line, which is about the
     *  declarations written above it and not about what is measured. */
    private static List<String> measured(String report) {
        List<String> out = new ArrayList<>();
        boolean inside = false;
        for (String line : report.split("\n")) {
            if (line.startsWith("  after ")) {
                inside = true;
            } else if (inside && !line.startsWith("    ")) {
                break;
            }
            if (inside) {
                out.add(line.replaceAll("reached at \\d+:", "reached at "));
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
