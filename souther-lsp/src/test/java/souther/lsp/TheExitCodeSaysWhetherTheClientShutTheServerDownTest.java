package souther.lsp;

import souther.lsp.transport.MessageConnection;
import org.junit.jupiter.api.Test;
import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.OutputStream;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The protocol has a session end on it — {@code shutdown}, then {@code exit} — and says the process
 * ends zero when that is how it ended and one when it is not. A server that answered zero either
 * way would report a client that died mid-session as an editor closing a file.
 */
class TheExitCodeSaysWhetherTheClientShutTheServerDownTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    @Test
    void exitAfterShutdownIsTheSessionEndingAsItWasMeantTo() {
        assertEquals(0, serve(message(1, "initialize"), message(null, "initialized"),
                message(2, "shutdown"), message(null, "exit")));
    }

    @Test
    void aClientThatClosedTheStreamOnceItHadShutTheServerDownEndedItTheSameWay() {
        assertEquals(0, serve(message(1, "initialize"), message(null, "initialized"),
                        message(2, "shutdown")),
                "the notification is what the process ends on, not what the session ends on");
    }

    @Test
    void exitWithoutShutdownIsAClientLeavingRatherThanFinishing() {
        assertEquals(1, serve(message(1, "initialize"), message(null, "initialized"),
                message(null, "exit")));
    }

    @Test
    void aShutdownNobodyAskedIsNotOneTheCodeCanAnswerFor() {
        assertEquals(1, serve(message(1, "initialize"), message(null, "initialized"),
                        message(null, "shutdown"), message(null, "exit")),
                "`shutdown` is a request; written as a notification it asked nothing, and what "
                        + "asked nothing cannot be what the session ended on");
    }

    @Test
    void andIsNotRepliedToEither() {
        List<JsonNode> replies = repliesTo(message(1, "initialize"), message(null, "initialized"),
                message(null, "shutdown"), message(null, "exit"));

        assertTrue(replies.stream().noneMatch(m -> m.has("id") && m.get("id").isNull()),
                "a reply carrying a null id answers a request the client never wrote: " + replies);
    }

    @Test
    void anInputThatStopsMidSessionIsNotAnEndingAtAll() {
        assertEquals(1, serve(message(1, "initialize")),
                "the stream ran out where an answer was expected, which nothing here can name");
    }

    private static int serve(String... messages) {
        return session(new ByteArrayOutputStream(), messages);
    }

    private static int session(ByteArrayOutputStream wrote, String... messages) {
        ByteArrayOutputStream framed = new ByteArrayOutputStream();
        MessageConnection writer =
                new MessageConnection(new ByteArrayInputStream(new byte[0]), framed);
        for (String m : messages) {
            writer.write(m);
        }
        return LspServer.serve(new ByteArrayInputStream(framed.toByteArray()), wrote);
    }

    /** What the server wrote back, as the messages a client would read off the wire. */
    private static List<JsonNode> repliesTo(String... messages) {
        ByteArrayOutputStream wrote = new ByteArrayOutputStream();
        session(wrote, messages);
        MessageConnection reader = new MessageConnection(
                new ByteArrayInputStream(wrote.toByteArray()), OutputStream.nullOutputStream());
        List<JsonNode> read = new ArrayList<>();
        String s;
        while ((s = reader.read()) != null) {
            read.add(JSON.readTree(s));
        }
        return read;
    }

    private static String message(Integer id, String method) {
        Map<String, Object> m = new LinkedHashMap<>();
        m.put("jsonrpc", "2.0");
        if (id != null) {
            m.put("id", id);
        }
        m.put("method", method);
        m.put("params", Map.of());
        return JSON.writeValueAsString(m);
    }
}
