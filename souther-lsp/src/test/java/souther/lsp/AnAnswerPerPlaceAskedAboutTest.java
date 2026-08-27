package souther.lsp;

import org.junit.jupiter.api.Test;
import souther.lsp.transport.MessageConnection;
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
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * {@code selectionRange} pairs an answer with a place by where it sits in the list, so a place with
 * nothing written on it is answered rather than left out. Left out, every place after it is given
 * another place's widening — a wrong answer, where dropping the one is merely no answer.
 */
class AnAnswerPerPlaceAskedAboutTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    private static final String URI = "file:///t.sou";

    /** A blank line between two declarations, and a name on the line after it. */
    private static final String SOURCE = "module m\n\ndata D = { v: Int }\n";

    @Test
    void aPlaceWithNothingWrittenOnItIsStillAnswered() {
        List<JsonNode> answers = selectionRanges(
                position(1, 0),      // the blank line
                position(2, 5));     // the `D` of `data D`

        assertEquals(2, answers.size(), "one answer for each place asked about");
        assertEquals(1, answers.get(0).get("range").get("start").get("line").asInt(),
                "the blank line is answered about the blank line");
        assertFalse(answers.get(0).has("parent"), "nothing is written there to widen into");
        assertEquals(2, answers.get(1).get("range").get("start").get("line").asInt(),
                "and the name after it is answered about the name, not about the blank line");
        assertTrue(answers.get(1).has("parent"), "which widens into what holds it");
    }

    @Test
    void aPlaceWithNothingWrittenOnItWidensToNothing() {
        JsonNode answer = selectionRanges(position(1, 0)).getFirst();

        assertEquals(answer.get("range").get("start"), answer.get("range").get("end"),
                "a range over no characters, which is what is written there");
    }

    private static Map<String, Object> position(int line, int character) {
        return Map.of("line", line, "character", character);
    }

    private static List<JsonNode> selectionRanges(Map<String, Object> first) {
        return selectionRanges(List.of(first));
    }

    private static List<JsonNode> selectionRanges(Map<String, Object> first,
                                                  Map<String, Object> second) {
        return selectionRanges(List.of(first, second));
    }

    private static List<JsonNode> selectionRanges(List<Map<String, Object>> positions) {
        byte[] input = frames(
                message(1, "initialize", Map.of()),
                message(null, "initialized", Map.of()),
                message(null, "textDocument/didOpen", Map.of(
                        "textDocument", Map.of("uri", URI, "text", SOURCE))),
                message(2, "textDocument/selectionRange", Map.of(
                        "textDocument", Map.of("uri", URI),
                        "positions", positions)));

        ByteArrayOutputStream out = new ByteArrayOutputStream();
        new LspServer(new MessageConnection(new ByteArrayInputStream(input), out)).run();

        // By a numeric id: the server sends requests of its own — the file watcher's registration —
        // and those carry an id it spells itself.
        JsonNode answered = readFrames(out.toByteArray()).stream()
                .filter(m -> m.has("id") && m.get("id").isNumber() && m.get("id").asInt() == 2)
                .findFirst().orElseThrow(() -> new AssertionError("no answer to the request"))
                .get("result");
        List<JsonNode> out2 = new ArrayList<>();
        answered.forEach(out2::add);
        return out2;
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
        for (String each : messages) {
            byte[] body = each.getBytes(StandardCharsets.UTF_8);
            sb.append("Content-Length: ").append(body.length).append("\r\n\r\n").append(each);
        }
        return sb.toString().getBytes(StandardCharsets.UTF_8);
    }

    private static List<JsonNode> readFrames(byte[] bytes) {
        List<JsonNode> out = new ArrayList<>();
        String text = new String(bytes, StandardCharsets.UTF_8);
        int at = 0;
        while (true) {
            int header = text.indexOf("Content-Length: ", at);
            if (header < 0) {
                return out;
            }
            int eol = text.indexOf("\r\n", header);
            int length = Integer.parseInt(text.substring(header + 16, eol).trim());
            int body = text.indexOf("\r\n\r\n", eol) + 4;
            out.add(JSON.readTree(text.substring(body, body + length)));
            at = body + length;
        }
    }
}
