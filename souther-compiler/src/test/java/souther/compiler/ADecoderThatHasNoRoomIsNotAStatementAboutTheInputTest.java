package souther.compiler;

import org.junit.jupiter.api.Test;
import souther.compiler.generated.JsonBoundary;
import souther.runtime.OutOfRoom;

import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What the boundary reads is answered as a value or as issues; what the platform has no room for is
 * neither.
 *
 * <p>A decoder refuses every input it refuses by returning issues — an array where an object
 * belongs, a null, a string for a number — so a decoder that throws is not saying anything about the
 * input. An invariant on a decoded data is computed, and its arithmetic can pass what a
 * {@code BigDecimal} keeps; that is {@code OutOfRoom}, the platform short of room, and reading it as
 * an input that is not shaped like its type tells the author to look at a value that was fine.
 */
class ADecoderThatHasNoRoomIsNotAStatementAboutTheInputTest {

    private static final String SOURCE = """
            module demo

            data Wide = { v: Decimal }
              invariant squares = v * v >= 0.0m

            behavior keep : (w: Wide) -> Wide
            let keep (w) = w
            """;

    @Test
    void aValueTheInvariantHasRoomForIsRead() throws Exception {
        assertInstanceOf(JsonBoundary.Read.Value.class,
                Crossing.reading(SOURCE, "demo", "keep", "{\"v\":2}"));
    }

    @Test
    void anInvariantWithNoRoomForItsArithmeticReachesTheCallerAsTheShortage() {
        OutOfRoom thrown = assertThrows(OutOfRoom.class,
                () -> Crossing.readingExactly(SOURCE, "demo", "keep", "{\"v\":1E-2000000000}"));
        assertTrue(thrown.getMessage().contains("no room"), thrown.getMessage());
    }

    @Test
    void anInputThatIsNotTheShapeIsStillRefusedAsIssues() throws Exception {
        for (String input : new String[] {"[]", "\"x\"", "null", "{\"v\":\"x\"}", "{}"}) {
            Crossing.refusalOf(SOURCE, "demo", "keep", input);
        }
    }
}
