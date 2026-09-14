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
import java.util.function.Predicate;

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

    /** What a client must read under a capability's key to be told the method is offered. */
    private sealed interface Told {

        /**
         * A field of the capabilities object, and what its value has to say.
         *
         * <p>Which value to send is this server's to choose — a bare {@code true} and an options
         * object are both legitimate answers, and copying the one we chose would witness nothing.
         * Whether the value offers the method is not a choice: {@code hoverProvider: false} and
         * {@code semanticTokensProvider: { full: false }} are well-formed capabilities that decline
         * the very request behind them, and a server sending one while answering that request is
         * back to answering what it did not advertise.
         */
        record Capability(String key, Predicate<JsonNode> offers, String offering) implements Told {
        }

        /** Announced after the handshake by {@code client/registerCapability}. */
        record Registration() implements Told {
        }

        /** Announced by nothing, for the reason given. */
        record Nothing(Advertisement.Reason reason) implements Told {
        }
    }

    /** One method as the protocol defines it: the name a client sends, and how it is told. */
    private record Protocol(LspMethod method, String wire, Told told) {
    }

    /** {@code true}, or an options object; {@code false} or an absent field declines the request. */
    private static boolean trueOrOptions(JsonNode value) {
        return (value.isBoolean() && value.booleanValue()) || value.isObject();
    }

    /** An options object and nothing else — these two capabilities have no boolean form. */
    private static final Predicate<JsonNode> OPTIONS = JsonNode::isObject;

    /**
     * The shorthand form of {@code textDocumentSync}, when it says documents are synced at all.
     *
     * <p>{@code TextDocumentSyncKind} is {@code None}, {@code Full} or {@code Incremental}, so a
     * number outside those three says nothing rather than something permissive.
     */
    private static boolean syncedByKind(JsonNode value) {
        return value.isNumber() && (value.intValue() == 1 || value.intValue() == 2);
    }

    /**
     * Opening and closing a document, which the options form puts behind its own {@code openClose}.
     *
     * <p>The shorthand carries it; the long form does not unless it says so, and a client reading
     * options without {@code openClose} sends neither notification.
     */
    private static boolean openCloseSync(JsonNode value) {
        if (syncedByKind(value)) {
            return true;
        }
        JsonNode openClose = value.isObject() ? value.get("openClose") : null;
        return openClose != null && openClose.isBoolean() && openClose.booleanValue();
    }

    /**
     * Changing a document, which the options form puts behind its own {@code change}.
     *
     * <p>A sync that opens and closes documents is not one that reports edits: {@code change} is
     * absent or {@code None} in options that say nothing about them, and either way no
     * {@code didChange} arrives.
     */
    private static boolean changeSync(JsonNode value) {
        if (syncedByKind(value)) {
            return true;
        }
        JsonNode change = value.isObject() ? value.get("change") : null;
        return change != null && syncedByKind(change);
    }

    /** Semantic tokens for a whole document are behind the options' own {@code full}. */
    private static boolean fullDocumentTokens(JsonNode value) {
        JsonNode full = value.isObject() ? value.get("full") : null;
        return full != null && (full.isObject() || (full.isBoolean() && full.booleanValue()));
    }

    private static Protocol offered(LspMethod method, String wire, String key) {
        return new Protocol(method, wire,
                new Told.Capability(key, WhatTheServerAdvertisesIsWhatItAnswersTest::trueOrOptions,
                        "true or an options object"));
    }

    private static Protocol lifecycle(LspMethod method, String wire) {
        return new Protocol(method, wire, new Told.Nothing(Advertisement.Reason.LIFECYCLE));
    }

    private static Protocol protocolNotification(LspMethod method, String wire) {
        return new Protocol(method, wire,
                new Told.Nothing(Advertisement.Reason.UNADVERTISED_PROTOCOL_METHOD));
    }

    /**
     * The protocol, written out rather than read from the server.
     *
     * <p>Every method has a row, so a method added to {@link LspMethod} is one this file has to say
     * something about. What a row says is what the specification says: the name a client sends, and
     * what a client reads to know it may send it.
     */
    private static final List<Protocol> PROTOCOL = List.of(
            lifecycle(LspMethod.INITIALIZE, "initialize"),
            lifecycle(LspMethod.INITIALIZED, "initialized"),
            lifecycle(LspMethod.SHUTDOWN, "shutdown"),
            lifecycle(LspMethod.EXIT, "exit"),
            protocolNotification(LspMethod.SET_TRACE, "$/setTrace"),
            protocolNotification(LspMethod.DID_CHANGE_CONFIGURATION,
                    "workspace/didChangeConfiguration"),
            new Protocol(LspMethod.DID_OPEN, "textDocument/didOpen",
                    new Told.Capability("textDocumentSync",
                            WhatTheServerAdvertisesIsWhatItAnswersTest::openCloseSync,
                            "a sync kind that syncs, or options whose `openClose` is on")),
            new Protocol(LspMethod.DID_CHANGE, "textDocument/didChange",
                    new Told.Capability("textDocumentSync",
                            WhatTheServerAdvertisesIsWhatItAnswersTest::changeSync,
                            "a sync kind that syncs, or options whose `change` is not None")),
            new Protocol(LspMethod.DID_CLOSE, "textDocument/didClose",
                    new Told.Capability("textDocumentSync",
                            WhatTheServerAdvertisesIsWhatItAnswersTest::openCloseSync,
                            "a sync kind that syncs, or options whose `openClose` is on")),
            new Protocol(LspMethod.DID_CHANGE_WATCHED_FILES, "workspace/didChangeWatchedFiles",
                    new Told.Registration()),
            offered(LspMethod.DOCUMENT_SYMBOL, "textDocument/documentSymbol",
                    "documentSymbolProvider"),
            new Protocol(LspMethod.SEMANTIC_TOKENS_FULL, "textDocument/semanticTokens/full",
                    new Told.Capability("semanticTokensProvider",
                            WhatTheServerAdvertisesIsWhatItAnswersTest::fullDocumentTokens,
                            "options whose `full` offers whole-document tokens")),
            offered(LspMethod.HOVER, "textDocument/hover", "hoverProvider"),
            offered(LspMethod.DEFINITION, "textDocument/definition", "definitionProvider"),
            offered(LspMethod.REFERENCES, "textDocument/references", "referencesProvider"),
            new Protocol(LspMethod.COMPLETION, "textDocument/completion",
                    new Told.Capability("completionProvider", OPTIONS, "an options object")),
            offered(LspMethod.INLAY_HINT, "textDocument/inlayHint", "inlayHintProvider"),
            offered(LspMethod.DOCUMENT_HIGHLIGHT, "textDocument/documentHighlight",
                    "documentHighlightProvider"),
            offered(LspMethod.SELECTION_RANGE, "textDocument/selectionRange",
                    "selectionRangeProvider"),
            offered(LspMethod.WORKSPACE_SYMBOL, "workspace/symbol", "workspaceSymbolProvider"),
            new Protocol(LspMethod.SIGNATURE_HELP, "textDocument/signatureHelp",
                    new Told.Capability("signatureHelpProvider", OPTIONS, "an options object")),
            new Protocol(LspMethod.CODE_ACTION, "textDocument/codeAction",
                    new Told.Capability("codeActionProvider", OPTIONS, "an options object")),
            // Announced by a flag inside the capability above rather than by one of its own: a
            // client learns that an action can be resolved from the method it completes.
            new Protocol(LspMethod.CODE_ACTION_RESOLVE, "codeAction/resolve",
                    new Told.Nothing(Advertisement.Reason.UNDER_ANOTHER_METHODS_CAPABILITY)),
            new Protocol(LspMethod.CODE_LENS, "textDocument/codeLens",
                    new Told.Capability("codeLensProvider", OPTIONS, "an options object")),
            offered(LspMethod.RENAME, "textDocument/rename", "renameProvider"),
            offered(LspMethod.FORMATTING, "textDocument/formatting", "documentFormattingProvider"));

    @Test
    void everyMethodIsAnnouncedTheWayTheProtocolSaysItIs() {
        JsonNode capabilities = responseFor(
                exchange(message(1, "initialize", Map.of())), 1).get("capabilities");

        Set<LspMethod> written = EnumSet.noneOf(LspMethod.class);
        for (Protocol row : PROTOCOL) {
            assertTrue(written.add(row.method()), row.method() + " is written more than once");
            assertEquals(row.wire(), row.method().wire(),
                    "the name a client sends for " + row.method());
            switch (row.told()) {
                case Told.Capability told -> {
                    Advertisement.StaticCapability declared = assertInstanceOf(
                            Advertisement.StaticCapability.class, row.method().advertisement(),
                            row.method() + " is announced by a capability");
                    assertEquals(told.key(), declared.key(),
                            "the capability a client reads before sending " + row.wire());
                    JsonNode sent = capabilities.get(told.key());
                    assertNotNull(sent, told.key() + " is in the handshake");
                    assertTrue(told.offers().test(sent), told.key() + " has to be "
                            + told.offering() + " to offer " + row.wire() + ", and is " + sent);
                }
                case Told.Registration _ -> assertInstanceOf(
                        Advertisement.DynamicRegistration.class, row.method().advertisement(),
                        row.method() + " is registered rather than carried by a capability");
                case Told.Nothing told -> {
                    Advertisement.None none = assertInstanceOf(Advertisement.None.class,
                            row.method().advertisement(), row.method() + " is announced by nothing");
                    assertEquals(told.reason(), none.reason(),
                            "why " + row.method() + " is not announced");
                }
            }
        }
        assertEquals(EnumSet.allOf(LspMethod.class), written,
                "every method the server answers says here how a client hears about it");
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

    /**
     * A method of the protocol this server does not answer.
     *
     * <p>{@code foldingRange} rather than something invented: what is being checked is that a real
     * request for something real is refused, and a spelling nobody would send is refused by a route
     * a client never takes. It is one this server has decided against — an editor folds on
     * indentation and Souther's blocks are indented the way that expects — so it stays unanswered,
     * which is what a fixture has to be able to rely on.
     */
    @Test
    void anUnknownRequestIsRefusedAsNotFound() {
        JsonNode error = errorFrom(exchange(
                message(1, "initialize", Map.of()),
                message(2, "textDocument/foldingRange", Map.of())), 2);
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
