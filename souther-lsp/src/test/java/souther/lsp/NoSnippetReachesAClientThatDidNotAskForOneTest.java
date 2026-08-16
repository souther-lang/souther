package souther.lsp;

import souther.lsp.transport.MessageConnection;
import org.junit.jupiter.api.Test;
import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A skeleton is sent as one only to a client that said it reads them.
 *
 * <p>Placeholders are not text a client falls back to reading: one that was not told the insertion
 * is a snippet puts {@code ${1:name}} in the buffer as it stands. The protocol says a client
 * declares {@code snippetSupport} and that the default is false, and this server read nothing the
 * client sent at the handshake — it answered with its own capabilities and looked at none of theirs.
 *
 * <p>So the same declaration goes out two ways, and both are written from the one value the analyzer
 * built: with its holes marked for a client that reads them, and with the holes standing as their
 * own text for a client that does not. What the second inserts is what the first inserts if every
 * placeholder is left alone.
 */
class NoSnippetReachesAClientThatDidNotAskForOneTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    private static final String MODULE = """
            module m

            data MemberId = String

            behavior findMember : (id: MemberId) -> MemberId
            """;

    @Test
    void aClientThatSaidNothingIsSentNoSnippet() {
        List<JsonNode> items = completionsFor(null);
        assertFalse(items.isEmpty(), "the server offered nothing to check");
        for (JsonNode item : items) {
            assertFalse(item.has("insertTextFormat"),
                    "a snippet format reached a client that did not ask for one: " + item);
            if (item.has("insertText")) {
                assertFalse(item.get("insertText").asString().contains("${"),
                        "a placeholder reached a client that reads it as text: " + item);
            }
        }
    }

    /** And what it is sent instead is the declaration with its holes standing as their own text. */
    @Test
    void aClientThatSaidNothingIsSentTheDeclarationAsText() {
        JsonNode offered = itemLabelled(completionsFor(null), "let findMember");
        assertEquals("let findMember (id) = body\n", offered.get("insertText").asString());
    }

    /**
     * A client that said it reads them is sent the holes as placeholders, numbered in order.
     *
     * <p>The name is not among them. What implements a behavior is the {@code let} of the same name,
     * so the one thing about this declaration that is not the author's is what it is called.
     */
    @Test
    void aClientThatAskedIsSentTheHolesAsPlaceholders() {
        JsonNode offered = itemLabelled(completionsFor(true), "let findMember");
        assertEquals(2, offered.get("insertTextFormat").asInt(), "the snippet format");
        assertEquals("let findMember (${1:id}) = ${2:body}\n",
                offered.get("insertText").asString());
    }

    /** A name is a name to either of them: it inserts what it says, and says so by carrying nothing. */
    @Test
    void anItemThatWritesWhatItSaysCarriesNoInsertion() {
        JsonNode offered = itemLabelled(completionsFor(true), "MemberId");
        assertFalse(offered.has("insertText"), "a name was sent an insertion: " + offered);
        assertFalse(offered.has("insertTextFormat"), "a name was sent a format: " + offered);
    }

    /**
     * The client's own words, or nothing at all.
     *
     * <p>{@code snippetSupport} is written at
     * {@code capabilities.textDocument.completion.completionItem}, and a client that declares
     * nothing along that path has declared false — which the protocol says, and which is the
     * difference between reading what a client sent and assuming it.
     */
    private static List<JsonNode> completionsFor(Boolean snippetSupport) {
        Map<String, Object> initialize = new LinkedHashMap<>();
        if (snippetSupport != null) {
            initialize.put("capabilities", Map.of("textDocument", Map.of("completion",
                    Map.of("completionItem", Map.of("snippetSupport", snippetSupport)))));
        }
        byte[] input = frames(
                message(1, "initialize", initialize),
                message(null, "initialized", Map.of()),
                message(null, "textDocument/didOpen", Map.of(
                        "textDocument", Map.of("uri", "file:///m.sou", "text", MODULE))),
                message(2, "textDocument/completion", Map.of(
                        "textDocument", Map.of("uri", "file:///m.sou"),
                        "position", Map.of("line", (int) MODULE.lines().count(), "character", 0))));

        ByteArrayOutputStream out = new ByteArrayOutputStream();
        new LspServer(new MessageConnection(new ByteArrayInputStream(input), out)).run();

        JsonNode response = readFrames(out.toByteArray()).stream()
                // The server asks the client things of its own, under an id of its own spelling.
                .filter(m -> m.has("id") && m.get("id").isNumber() && m.get("id").asInt() == 2)
                .findFirst().orElseThrow(() -> new AssertionError("no completion response"));
        List<JsonNode> items = new ArrayList<>();
        response.get("result").forEach(items::add);
        return items;
    }

    private static JsonNode itemLabelled(List<JsonNode> items, String label) {
        for (JsonNode item : items) {
            if (item.get("label").asString().equals(label)) {
                return item;
            }
        }
        throw new AssertionError("nothing labelled " + label + " among "
                + items.stream().map(i -> i.get("label").asString()).toList());
    }

    private static String message(Integer id, String method, Map<String, Object> params) {
        Map<String, Object> m = new LinkedHashMap<>();
        m.put("jsonrpc", "2.0");
        if (id != null) {
            m.put("id", id);
        }
        m.put("method", method);
        m.put("params", params);
        return JSON.writeValueAsString(m);
    }

    private static byte[] frames(String... messages) {
        StringBuilder sb = new StringBuilder();
        for (String body : messages) {
            byte[] bytes = body.getBytes(StandardCharsets.UTF_8);
            sb.append("Content-Length: ").append(bytes.length).append("\r\n\r\n").append(body);
        }
        return sb.toString().getBytes(StandardCharsets.UTF_8);
    }

    private static List<JsonNode> readFrames(byte[] bytes) {
        List<JsonNode> out = new ArrayList<>();
        String all = new String(bytes, StandardCharsets.UTF_8);
        int at = 0;
        while (true) {
            int header = all.indexOf("Content-Length: ", at);
            if (header < 0) {
                return out;
            }
            int eol = all.indexOf("\r\n", header);
            int length = Integer.parseInt(all.substring(header + 16, eol).trim());
            int body = all.indexOf("\r\n\r\n", eol) + 4;
            out.add(JSON.readTree(all.substring(body, body + length)));
            at = body + length;
        }
    }

    /** Asserts the harness itself found something, so an empty response cannot pass as agreement. */
    @Test
    void theHarnessReachesTheServer() {
        assertNotNull(itemLabelled(completionsFor(true), "let"));
        assertTrue(completionsFor(null).size() > 5, "the server answered with almost nothing");
    }
}
