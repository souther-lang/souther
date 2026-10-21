package souther.cli;

import org.junit.jupiter.api.Test;
import souther.cli.CliProcess.Ran;
import souther.lsp.ToolingMetadata;

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
        Ran ran = CliInProcess.run(args);
        return new Said(ran.code(), ran.err(), ran.out());
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
