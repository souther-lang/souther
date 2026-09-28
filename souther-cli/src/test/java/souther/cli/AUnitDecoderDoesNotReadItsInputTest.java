package souther.cli;

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

    @TempDir
    Path dir;

    private static final String MODEL = """
            module demo

            data Closed

            behavior alone : (c: Closed) -> Closed
            let alone (c) = c
            """;

    private String run(String input) throws Exception {
        Path file = dir.resolve("demo.sou");
        Files.writeString(file, MODEL);
        return Runner.run(file, "alone", input).trim();
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
