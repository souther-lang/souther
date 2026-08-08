package souther.lsp;

import souther.lsp.analysis.Analyzer;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;

/**
 * Every request and notification this server answers, and what tells a client about each.
 *
 * <p>The set lives here rather than in the case labels of a switch because the rest of the server
 * has to read it. What the handshake advertises and what is registered after it are both built from
 * these values, so the two cannot say something the server does not answer; and a method cannot be
 * answered without being one of these values, because {@link LspServer} reaches its handlers only
 * through {@link #of}. A method nobody was told about is then not something to test for — it is
 * something there is no way to write.
 *
 * <p>What a method is advertised by is not a name derived from the method's own: three notifications
 * share one capability, one method is registered after the handshake instead, and the lifecycle is
 * announced by nothing. Each of those is a value here rather than a row missing from a table.
 */
public enum LspMethod {

    INITIALIZE("initialize", Announced.LIFECYCLE),
    INITIALIZED("initialized", Announced.LIFECYCLE),
    SET_TRACE("$/setTrace", Announced.PROTOCOL_DEFINED),
    DID_CHANGE_CONFIGURATION("workspace/didChangeConfiguration", Announced.PROTOCOL_DEFINED),
    DID_OPEN("textDocument/didOpen", Announced.TEXT_DOCUMENT_SYNC),
    DID_CHANGE("textDocument/didChange", Announced.TEXT_DOCUMENT_SYNC),
    DID_CLOSE("textDocument/didClose", Announced.TEXT_DOCUMENT_SYNC),
    DID_CHANGE_WATCHED_FILES("workspace/didChangeWatchedFiles", Announced.SOU_FILE_WATCHER),
    DOCUMENT_SYMBOL("textDocument/documentSymbol",
            new Advertisement.StaticCapability("documentSymbolProvider", true)),
    SEMANTIC_TOKENS_FULL("textDocument/semanticTokens/full", Announced.SEMANTIC_TOKENS),
    HOVER("textDocument/hover", new Advertisement.StaticCapability("hoverProvider", true)),
    DEFINITION("textDocument/definition", new Advertisement.StaticCapability("definitionProvider", true)),
    REFERENCES("textDocument/references", new Advertisement.StaticCapability("referencesProvider", true)),
    // invoked completion; no trigger characters
    COMPLETION("textDocument/completion", new Advertisement.StaticCapability("completionProvider", Map.of())),
    CODE_ACTION("textDocument/codeAction", new Advertisement.StaticCapability("codeActionProvider", true)),
    CODE_LENS("textDocument/codeLens",
            new Advertisement.StaticCapability("codeLensProvider", Map.of("resolveProvider", false))),
    RENAME("textDocument/rename", new Advertisement.StaticCapability("renameProvider", true)),
    FORMATTING("textDocument/formatting",
            new Advertisement.StaticCapability("documentFormattingProvider", true)),
    SHUTDOWN("shutdown", Announced.LIFECYCLE),
    EXIT("exit", Announced.LIFECYCLE);

    /** Advertisements shared by more than one method, or whose value is built rather than written. */
    private static final class Announced {

        static final Advertisement LIFECYCLE =
                new Advertisement.None(Advertisement.Reason.LIFECYCLE);

        static final Advertisement PROTOCOL_DEFINED =
                new Advertisement.None(Advertisement.Reason.UNADVERTISED_PROTOCOL_METHOD);

        /** 1 = full document sync. Opening, changing and closing a document are the three
         * notifications this one capability admits, and none of them names it. */
        static final Advertisement TEXT_DOCUMENT_SYNC =
                new Advertisement.StaticCapability("textDocumentSync", 1);

        static final Advertisement SEMANTIC_TOKENS =
                new Advertisement.StaticCapability("semanticTokensProvider", semanticTokens());

        static final Advertisement SOU_FILE_WATCHER = new Advertisement.DynamicRegistration(
                "souther-sou-watcher",
                Map.of("watchers", List.of(Map.of("globPattern", "**/*.sou"))));

        private static Map<String, Object> semanticTokens() {
            Map<String, Object> options = new LinkedHashMap<>();
            options.put("legend", Map.of("tokenTypes", Analyzer.TOKEN_TYPES,
                    "tokenModifiers", List.of()));
            options.put("full", true);
            return options;
        }

        private Announced() {
        }
    }

    private static final Map<String, LspMethod> BY_WIRE = byWire();

    private final String wire;
    private final Advertisement advertisement;

    LspMethod(String wire, Advertisement advertisement) {
        this.wire = wire;
        this.advertisement = advertisement;
    }

    /** How this method is spelled in a JSON-RPC {@code method} field. */
    public String wire() {
        return wire;
    }

    /** What tells a client this method can be called. */
    public Advertisement advertisement() {
        return advertisement;
    }

    /** The method a client named, or empty when the server answers no such method. */
    public static Optional<LspMethod> of(String wire) {
        return Optional.ofNullable(BY_WIRE.get(wire));
    }

    /**
     * The {@code capabilities} object of the initialize result.
     *
     * <p>Built from the methods rather than beside them, so a client is told about what is answered
     * and nothing else. A capability several methods share is one field, and one they disagree
     * about is a contradiction rather than a last-writer-wins.
     */
    public static Map<String, Object> serverCapabilities() {
        Map<String, Object> capabilities = new LinkedHashMap<>();
        for (LspMethod method : values()) {
            if (!(method.advertisement instanceof Advertisement.StaticCapability capability)) {
                continue;
            }
            Object already = capabilities.put(capability.key(), capability.value());
            if (already != null && !already.equals(capability.value())) {
                throw new IllegalStateException(
                        "two values advertised under " + capability.key() + ": " + already
                                + " and " + capability.value());
            }
        }
        return capabilities;
    }

    /**
     * The registrations to send once the client reports {@code initialized}, in the shape the
     * protocol's {@code Registration} takes. The method each one registers is the method that holds
     * it, so what is registered and what is answered cannot name different things.
     */
    public static List<Map<String, Object>> dynamicRegistrations() {
        List<Map<String, Object>> registrations = new ArrayList<>();
        for (LspMethod method : values()) {
            if (!(method.advertisement instanceof Advertisement.DynamicRegistration registration)) {
                continue;
            }
            Map<String, Object> entry = new LinkedHashMap<>();
            entry.put("id", registration.id());
            entry.put("method", method.wire);
            entry.put("registerOptions", registration.registerOptions());
            registrations.add(entry);
        }
        return registrations;
    }

    /**
     * Indexes the methods by their spelling, refusing two that are spelled the same.
     *
     * <p>A repeated spelling would leave one of the two unreachable and say nothing about it, and
     * the one left out would be the one that keeps its advertisement — a capability announcing a
     * method that answers as something else.
     */
    private static Map<String, LspMethod> byWire() {
        Map<String, LspMethod> index = new LinkedHashMap<>();
        for (LspMethod method : values()) {
            LspMethod clash = index.put(method.wire, method);
            if (clash != null) {
                throw new IllegalStateException(
                        clash + " and " + method + " are both spelled " + method.wire);
            }
        }
        return index;
    }
}
