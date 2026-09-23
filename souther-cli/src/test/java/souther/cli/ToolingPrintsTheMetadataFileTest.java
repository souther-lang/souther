package souther.cli;

import org.junit.jupiter.api.Test;
import souther.lsp.ToolingMetadata;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * {@code souther tooling} answers with the tooling metadata file, byte for byte, and not with an
 * answer of its own. Here that file is the one on the class path; whether the shipped jar still
 * carries it after the shade is {@link TheShippedJarAnswersFromWhatItCarriesIT}'s question.
 */
class ToolingPrintsTheMetadataFileTest {

    private record Said(int code, String err, String out) {}

    private Said run(String... args) {
        PrintStream originalErr = System.err;
        PrintStream originalOut = System.out;
        ByteArrayOutputStream err = new ByteArrayOutputStream();
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        System.setErr(new PrintStream(err, true, StandardCharsets.UTF_8));
        System.setOut(new PrintStream(out, true, StandardCharsets.UTF_8));
        try {
            int code = Main.dispatch(args);
            return new Said(code, err.toString(StandardCharsets.UTF_8),
                    out.toString(StandardCharsets.UTF_8));
        } finally {
            System.setErr(originalErr);
            System.setOut(originalOut);
        }
    }

    @Test
    void theCommandPrintsTheFile() {
        Said said = run("tooling");

        assertEquals(0, said.code(), said.err());
        assertEquals("", said.err());
        assertEquals(ToolingMetadata.text(), said.out());
    }

    @Test
    void anArgumentIsRefusedAndNothingIsPrinted() {
        Said said = run("tooling", "--json");

        assertEquals(2, said.code());
        assertEquals("", said.out());
        assertTrue(said.err().contains("souther tooling"), said.err());
    }
}
