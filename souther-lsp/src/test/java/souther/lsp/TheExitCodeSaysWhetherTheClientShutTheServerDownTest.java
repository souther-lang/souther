package souther.lsp;

import souther.lsp.transport.MessageConnection;
import org.junit.jupiter.api.Test;
import tools.jackson.databind.json.JsonMapper;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.OutputStream;
import java.util.LinkedHashMap;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * The protocol has a session end on it — {@code shutdown}, then {@code exit} — and says the process
 * ends zero when that is how it ended and one when it is not. A server that answered zero either
 * way would report a client that died mid-session as an editor closing a file.
 */
class TheExitCodeSaysWhetherTheClientShutTheServerDownTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    @Test
    void exitAfterShutdownIsTheSessionEndingAsItWasMeantTo() {
        assertEquals(0, serve(message(1, "shutdown"), message(null, "exit")));
    }

    @Test
    void aClientThatCloseTheStreamOnceItHadShutTheServerDownEndedItTheSameWay() {
        assertEquals(0, serve(message(1, "shutdown")),
                "the notification is what the process ends on, not what the session ends on");
    }

    @Test
    void exitWithoutShutdownIsAClientLeavingRatherThanFinishing() {
        assertEquals(1, serve(message(null, "exit")));
    }

    @Test
    void anInputThatStopsMidSessionIsNotAnEndingAtAll() {
        assertEquals(1, serve(message(1, "initialize")),
                "the stream ran out where an answer was expected, which nothing here can name");
    }

    private static int serve(String... messages) {
        ByteArrayOutputStream framed = new ByteArrayOutputStream();
        MessageConnection writer =
                new MessageConnection(new ByteArrayInputStream(new byte[0]), framed);
        for (String m : messages) {
            writer.write(m);
        }
        return LspServer.serve(new ByteArrayInputStream(framed.toByteArray()),
                OutputStream.nullOutputStream());
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
