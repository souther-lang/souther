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
 * What the protocol makes of an answer, held to over the wire.
 *
 * <p>An answer's meaning is not this server's to decide. What a value in a reply comes to is the
 * protocol's, and reasoning about what it ought to mean instead of reading what it does mean has
 * been wrong twice here: a place with no answer was dropped from a list the protocol pairs by index,
 * and an active parameter was pointed past the end of the parameters as a way of saying "none of
 * them". Both were sound as reasoning and neither was the rule.
 *
 * <p>So a rule this server rests on is written down here, in the wire's own terms, and checked
 * against what the server actually sends. {@code WhatTheServerAdvertisesIsWhatItAnswersTest} is the
 * same thing for the handshake — what a client is told a method is — and this is it for what a
 * method answers with.
 */
class EveryRuleThisServerRestsOnIsCheckedAtTheWireTest {

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

    /**
     * An active parameter names one of the parameters sent with it.
     *
     * <p>The protocol reads one outside the list as none given and marks the first, so a mark past
     * the end does not say "none of these" — it says the first, which is the one furthest from what
     * is being written. Where an author has written more arguments than the declaration takes there
     * is nothing true to say, and what goes over the wire is no help rather than a wrong mark.
     */
    @Test
    void anActiveParameterNamesOneOfTheParametersSentWithIt() {
        // the cursor at the end of the line the call is written on
        JsonNode within = signatureHelp("submit(d,\n", position(6, "let run (d) = submit(d,".length()));
        assertEquals(2, within.get("signatures").get(0).get("parameters").size());
        assertTrue(within.get("activeParameter").asInt()
                        < within.get("signatures").get(0).get("parameters").size(),
                "the mark is on a parameter that was sent");

        assertTrue(signatureHelp("submit(d, s,\n",
                        position(6, "let run (d) = submit(d, s,".length())).isNull(),
                "and where none of them is being written, nothing is answered");
    }

    /** The server's reply to a signature help asked at {@code at}, on a document ending in
     *  {@code body}. */
    private static JsonNode signatureHelp(String body, Map<String, Object> at) {
        String text = """
                module m

                data D = { v: Int }

                behavior submit : (a: D, b: D) -> Int
                behavior run : (d: D) -> Int
                let run (d) = \
                """ + body;
        byte[] input = frames(
                message(1, "initialize", Map.of()),
                message(null, "initialized", Map.of()),
                message(null, "textDocument/didOpen", Map.of(
                        "textDocument", Map.of("uri", URI, "text", text))),
                message(2, "textDocument/signatureHelp", Map.of(
                        "textDocument", Map.of("uri", URI), "position", at)));

        ByteArrayOutputStream out = new ByteArrayOutputStream();
        new LspServer(new MessageConnection(new ByteArrayInputStream(input), out)).run();

        return readFrames(out.toByteArray()).stream()
                .filter(m -> m.has("id") && m.get("id").isNumber() && m.get("id").asInt() == 2)
                .findFirst().orElseThrow(() -> new AssertionError("no answer to the request"))
                .get("result");
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
