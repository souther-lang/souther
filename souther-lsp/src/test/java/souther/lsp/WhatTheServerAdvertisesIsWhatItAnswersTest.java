package souther.lsp;

import souther.lsp.transport.MessageConnection;
import org.junit.jupiter.api.Test;
import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.OutputStream;
import java.util.ArrayList;
import java.util.EnumSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a client is told it may call, held against what the server does when it calls it.
 *
 * <p>That the two describe one set is a property of {@link LspMethod}: the handshake is built from
 * the methods and there is no way to answer one that is not among them. What is left to observe is
 * that the property survives the wire — that a method the handshake invites is not met with
 * {@code method not found} at the connection, which is what a client actually depends on.
 *
 * <p>Which method a capability announces is a different question, and one the server cannot answer
 * about itself: that {@code hoverProvider} is the field a client reads before sending
 * {@code textDocument/hover} is the protocol's, not ours. {@link #everyMethodIsAnnouncedTheWayTheProtocolSaysItIs}
 * writes that relation out. It is deliberately a second copy of what {@link LspMethod} declares,
 * for the reason the protocol-facing tests keep their method literals: one side says what this
 * server believes and the other says what the protocol defines, and only holding them together
 * catches a capability announcing a method it does not name.
 *
 * <p>Everywhere else the methods are read from {@link LspMethod} rather than listed. Which methods
 * exist is settled there, and a list of them written here would be a third copy of that set.
 */
class WhatTheServerAdvertisesIsWhatItAnswersTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    private static final int METHOD_NOT_FOUND = -32601;

    private static final String URI = "file:///a.sou";

    private static final String TEXT = "module demo\ndata X = { a: Int }\n";

    /** Enough of every request shape for any handler's decoder to read what it looks for, so that a
     * method answering nothing in particular still answers rather than failing to be understood. */
    private static Map<String, Object> everyShape() {
        Map<String, Object> params = new LinkedHashMap<>();
        params.put("textDocument", Map.of("uri", URI, "text", TEXT));
        params.put("contentChanges", List.of(Map.of("text", TEXT)));
        params.put("position", Map.of("line", 1, "character", 5));
        params.put("range", Map.of("start", Map.of("line", 1, "character", 5),
                "end", Map.of("line", 1, "character", 6)));
        params.put("context", Map.of("diagnostics", List.of()));
        params.put("newName", "y");
        params.put("options", Map.of("tabSize", 4, "insertSpaces", true));
        return params;
    }

    /**
     * No method a capability announces comes back as one the server does not have.
     *
     * <p>Only that. What a handler answers with, and whether it answers at all rather than failing
     * on the way, is each method's own behaviour and is tested where that behaviour is. A
     * notification has no reply to be refused in, so for the three that share full document sync
     * there is nothing here to observe; they are walked with the rest because which methods a
     * capability announces is not this test's to decide.
     */
    @Test
    void noAdvertisedMethodIsRefusedAsNotFound() {
        for (LspMethod method : LspMethod.values()) {
            if (!(method.advertisement() instanceof Advertisement.StaticCapability capability)) {
                continue;
            }
            JsonNode error = errorFrom(exchange(
                    message(1, "initialize", Map.of()),
                    message(null, "initialized", Map.of()),
                    message(null, "textDocument/didOpen", Map.of(
                            "textDocument", Map.of("uri", URI, "text", TEXT))),
                    message(2, method.wire(), everyShape())), 2);
            if (error != null) {
                assertNotEquals(METHOD_NOT_FOUND, error.get("code").asInt(),
                        capability.key() + " invites " + method.wire() + ", which is refused");
            }
        }
    }

    /**
     * How each method is announced, written from the protocol rather than read from the server.
     *
     * <p>A capability key is what the protocol says a client reads before sending that method. The
     * value under the key is not here: whether a provider is spelled {@code true} or an options
     * object is this server's to decide, and repeating it would copy a decision rather than witness
     * an agreement.
     */
    @Test
    void everyMethodIsAnnouncedTheWayTheProtocolSaysItIs() {
        Map<LspMethod, String> byCapability = new LinkedHashMap<>();
        byCapability.put(LspMethod.DID_OPEN, "textDocumentSync");
        byCapability.put(LspMethod.DID_CHANGE, "textDocumentSync");
        byCapability.put(LspMethod.DID_CLOSE, "textDocumentSync");
        byCapability.put(LspMethod.DOCUMENT_SYMBOL, "documentSymbolProvider");
        byCapability.put(LspMethod.SEMANTIC_TOKENS_FULL, "semanticTokensProvider");
        byCapability.put(LspMethod.HOVER, "hoverProvider");
        byCapability.put(LspMethod.DEFINITION, "definitionProvider");
        byCapability.put(LspMethod.REFERENCES, "referencesProvider");
        byCapability.put(LspMethod.COMPLETION, "completionProvider");
        byCapability.put(LspMethod.CODE_ACTION, "codeActionProvider");
        byCapability.put(LspMethod.CODE_LENS, "codeLensProvider");
        byCapability.put(LspMethod.RENAME, "renameProvider");
        byCapability.put(LspMethod.FORMATTING, "documentFormattingProvider");

        Set<LspMethod> registeredAfterTheHandshake = EnumSet.of(LspMethod.DID_CHANGE_WATCHED_FILES);

        Map<LspMethod, Advertisement.Reason> announcedByNothing = new LinkedHashMap<>();
        announcedByNothing.put(LspMethod.INITIALIZE, Advertisement.Reason.LIFECYCLE);
        announcedByNothing.put(LspMethod.INITIALIZED, Advertisement.Reason.LIFECYCLE);
        announcedByNothing.put(LspMethod.SHUTDOWN, Advertisement.Reason.LIFECYCLE);
        announcedByNothing.put(LspMethod.EXIT, Advertisement.Reason.LIFECYCLE);
        announcedByNothing.put(LspMethod.SET_TRACE,
                Advertisement.Reason.UNADVERTISED_PROTOCOL_METHOD);
        announcedByNothing.put(LspMethod.DID_CHANGE_CONFIGURATION,
                Advertisement.Reason.UNADVERTISED_PROTOCOL_METHOD);

        Set<LspMethod> written = EnumSet.noneOf(LspMethod.class);
        for (LspMethod method : byCapability.keySet()) {
            assertTrue(written.add(method), method + " is written more than once");
        }
        for (LspMethod method : registeredAfterTheHandshake) {
            assertTrue(written.add(method), method + " is written more than once");
        }
        for (LspMethod method : announcedByNothing.keySet()) {
            assertTrue(written.add(method), method + " is written more than once");
        }
        assertEquals(EnumSet.allOf(LspMethod.class), written,
                "every method the server answers says here how a client hears about it");

        for (Map.Entry<LspMethod, String> row : byCapability.entrySet()) {
            Advertisement.StaticCapability capability = assertInstanceOf(
                    Advertisement.StaticCapability.class, row.getKey().advertisement(),
                    row.getKey() + " is announced by a capability");
            assertEquals(row.getValue(), capability.key(),
                    "the capability a client reads before sending " + row.getKey().wire());
        }
        for (LspMethod method : registeredAfterTheHandshake) {
            assertInstanceOf(Advertisement.DynamicRegistration.class, method.advertisement(),
                    method + " is registered rather than carried by a capability");
        }
        for (Map.Entry<LspMethod, Advertisement.Reason> row : announcedByNothing.entrySet()) {
            Advertisement.None none = assertInstanceOf(Advertisement.None.class,
                    row.getKey().advertisement(), row.getKey() + " is announced by nothing");
            assertEquals(row.getValue(), none.reason(), "why " + row.getKey() + " is not announced");
        }
    }

    @Test
    void theHandshakeCarriesEveryAdvertisedCapabilityAndNoOther() {
        JsonNode capabilities = responseFor(
                exchange(message(1, "initialize", Map.of())), 1).get("capabilities");

        Set<String> announced = new LinkedHashSet<>();
        for (LspMethod method : LspMethod.values()) {
            if (method.advertisement() instanceof Advertisement.StaticCapability capability) {
                announced.add(capability.key());
            }
        }

        Set<String> sent = new LinkedHashSet<>();
        for (String key : capabilities.propertyNames()) {
            sent.add(key);
        }

        assertEquals(announced, sent,
                "the handshake is the methods' advertisements and nothing written beside them");
    }

    @Test
    void theRegistrationNamesTheMethodThatCarriesIt() {
        for (Map<String, Object> registration : LspMethod.dynamicRegistrations()) {
            String registered = (String) registration.get("method");
            assertTrue(LspMethod.of(registered).isPresent(),
                    "registers a method the server answers: " + registered);
            assertSame(LspMethod.of(registered).orElseThrow().advertisement().getClass(),
                    Advertisement.DynamicRegistration.class,
                    registered + " is registered, so that is how it is announced");
        }
    }

    @Test
    void aMethodIsFoundByTheSpellingItDeclares() {
        for (LspMethod method : LspMethod.values()) {
            assertSame(method, LspMethod.of(method.wire()).orElse(null),
                    method + " is what its own spelling names");
        }
    }

    @Test
    void anUnknownRequestIsRefusedAsNotFound() {
        JsonNode error = errorFrom(exchange(
                message(1, "initialize", Map.of()),
                message(2, "textDocument/inlayHint", Map.of())), 2);
        assertNotNull(error, "a request naming no method is refused");
        assertEquals(METHOD_NOT_FOUND, error.get("code").asInt());
    }

    @Test
    void anUnknownNotificationIsDroppedRatherThanRefused() {
        List<JsonNode> answers = exchange(
                message(1, "initialize", Map.of()),
                message(null, "textDocument/willSave", Map.of()),
                message(2, "shutdown", Map.of()));

        assertNull(errorFrom(answers, 2), "the session reads on past a notification it does not know");
        assertNotNull(responseFor(answers, 2), "and still answers what comes after it");
        for (JsonNode answer : answers) {
            assertTrue(!answer.has("error") || answer.get("error").get("code").asInt() != METHOD_NOT_FOUND,
                    "a notification has no reply to be refused in: " + answer);
        }
    }

    // --- helpers: run one session over an in-memory connection ---

    private static List<JsonNode> exchange(String... requests) {
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        new LspServer(new MessageConnection(new ByteArrayInputStream(frames(requests)), out)).run();
        return readFrames(out.toByteArray());
    }

    /** The {@code error} of the reply to request {@code id}, or null when it was not refused. */
    private static JsonNode errorFrom(List<JsonNode> messages, int id) {
        return messages.stream()
                .filter(m -> m.has("id") && m.get("id").isNumber() && m.get("id").asInt() == id)
                .filter(m -> m.has("error"))
                .findFirst().map(m -> m.get("error")).orElse(null);
    }

    /** The {@code result} of the reply to request {@code id}, or null when there was none. */
    private static JsonNode responseFor(List<JsonNode> messages, int id) {
        return messages.stream()
                .filter(m -> m.has("result") && m.has("id") && m.get("id").isNumber()
                        && m.get("id").asInt() == id)
                .findFirst().map(m -> m.get("result")).orElse(null);
    }

    private static String message(Integer id, String method, Object params) {
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
        ByteArrayOutputStream buffer = new ByteArrayOutputStream();
        MessageConnection writer = new MessageConnection(new ByteArrayInputStream(new byte[0]), buffer);
        for (String m : messages) {
            writer.write(m);
        }
        return buffer.toByteArray();
    }

    private static List<JsonNode> readFrames(byte[] bytes) {
        MessageConnection reader = new MessageConnection(
                new ByteArrayInputStream(bytes), OutputStream.nullOutputStream());
        List<JsonNode> out = new ArrayList<>();
        String s;
        while ((s = reader.read()) != null) {
            out.add(JSON.readTree(s));
        }
        return out;
    }
}
