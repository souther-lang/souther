package souther.cli;

import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

import java.nio.file.Files;
import java.nio.file.Path;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A unit's derived Decoder answers the unit's one value and does not look at what it is given
 * (spec §decoder-derivation). So an input that is not the {@code {}} the Encoder writes still reads
 * as the unit, and writing it back gives {@code {}}.
 *
 * <p>This holds what the decoder accepts, and nothing about what the encoder writes in each
 * position; that is {@link AUnitIsWrittenByThePositionItStandsInTest}.
 */
class AUnitDecoderDoesNotReadItsInputTest {

    private static final String MODEL = """
            module demo

            data Closed

            behavior alone : (c: Closed) -> Closed
            let alone (c) = c
            """;

    /** {@link #MODEL}, compiled once and handed each input in turn. */
    private static Runner.Program demo;

    @BeforeAll
    static void compile(@TempDir Path dir) throws Exception {
        Path file = dir.resolve("demo.sou");
        Files.writeString(file, MODEL);
        demo = Runner.compile(file);
    }

    private static String run(String input) {
        return demo.run("alone", input).trim();
    }

    @Test
    void aNumberReadsAsTheUnit() throws Exception {
        assertEquals("{}", run("17"));
    }

    @Test
    void anObjectWithMembersReadsAsTheUnit() throws Exception {
        assertEquals("{}", run("{\"x\":1}"));
    }
}
