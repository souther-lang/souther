package souther.lsp.transport;

import org.junit.jupiter.api.Test;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.nio.charset.StandardCharsets;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/** The length and the header lines come off the wire, so they are bounded before they size anything. */
class MessageConnectionLimitsTest {

    private static MessageConnection reading(String wire) {
        return new MessageConnection(
                new ByteArrayInputStream(wire.getBytes(StandardCharsets.US_ASCII)), new ByteArrayOutputStream());
    }

    @Test
    void aMessageWithinTheLimitIsRead() {
        assertEquals("{}", reading("Content-Length: 2\r\n\r\n{}").read());
    }

    @Test
    void aContentLengthPastTheLimitIsRefusedBeforeAnythingIsAllocated() {
        assertThrows(IllegalStateException.class,
                () -> reading("Content-Length: 2000000000\r\n\r\n").read());
    }

    @Test
    void aNegativeContentLengthIsRefused() {
        assertThrows(IllegalStateException.class, () -> reading("Content-Length: -1\r\n\r\n").read());
    }

    @Test
    void aContentLengthThatIsNotANumberIsRefusedAsAFramingError() {
        assertThrows(IllegalStateException.class, () -> reading("Content-Length: many\r\n\r\n").read());
    }

    @Test
    void aHeaderLineWithoutAnEndIsRefusedRatherThanBufferedWithoutBound() {
        String endless = "X-Filler: " + "a".repeat(MessageConnection.MAX_HEADER_LINE_CHARS + 1);

        assertThrows(IllegalStateException.class, () -> reading(endless).read());
    }
}
