package souther.lsp;

import souther.compiler.cst.LineIndex;
import souther.lsp.analysis.Analyzer;
import souther.lsp.analysis.DocumentStore;
import souther.lsp.analysis.ModuleGraph;
import souther.lsp.analysis.Workspace;
import souther.compiler.query.Adequacy;
import souther.lsp.protocol.CodeAction;
import souther.lsp.protocol.CodeLens;
import souther.lsp.protocol.CompletionItem;
import souther.lsp.protocol.DocumentSymbol;
import souther.lsp.protocol.Hover;
import souther.lsp.protocol.Location;
import souther.lsp.protocol.LspDiagnostic;
import souther.lsp.protocol.Position;
import souther.lsp.protocol.Range;
import souther.lsp.rpc.InboundDecoders;
import souther.lsp.rpc.Params;
import souther.lsp.transport.MessageConnection;
import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * A hand-rolled LSP server over a {@link MessageConnection}. It reads JSON-RPC messages, dispatches
 * by method, and answers requests / publishes diagnostics. Inbound payloads are decoded with Raoh
 * ({@link InboundDecoders}); outbound trees are built as maps and serialised with Jackson. The
 * language work is delegated to the {@link Analyzer}, which knows nothing of the protocol.
 */
public final class LspServer {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    private final MessageConnection conn;
    private final DocumentStore documents = new DocumentStore();
    private final Analyzer analyzer = new Analyzer();
    private final Workspace workspace = new Workspace();
    private int nextRequestId = 1;

    public LspServer(MessageConnection conn) {
        this.conn = conn;
    }

    public static void main(String[] args) {
        new LspServer(new MessageConnection(System.in, System.out)).run();
    }

    /** Reads and dispatches messages until end of input or an {@code exit} notification. */
    public void run() {
        String message;
        while ((message = conn.read()) != null) {
            JsonNode m;
            try {
                m = JSON.readTree(message);
            } catch (RuntimeException _) {
                continue;   // a malformed frame is dropped, not fatal
            }
            JsonNode methodNode = m.get("method");
            if (methodNode == null || methodNode.isNull()) {
                continue;   // a response to a server-initiated request; nothing to do
            }
            boolean stop;
            try {
                stop = dispatch(methodNode.asString(), m.get("id"), m.get("params"));
            } catch (RuntimeException | StackOverflowError e) {
                // One request the server cannot answer must cost that request, not the session. The
                // analysis layer catches what it can so it can publish a marker instead, but that is
                // a promise made inside it; this is the one that holds whatever it does. A request
                // gets an error reply so the client stops waiting; a notification has no reply to
                // send, so it is simply dropped and the loop reads on.
                failed(m.get("id"), e);
                continue;
            }
            if (stop) {
                return;     // exit
            }
        }
    }

    /** Replies to a request the server could not answer. A notification (no id) has no reply. */
    private void failed(JsonNode id, Throwable cause) {
        if (id == null || id.isNull()) {
            return;
        }
        respondError(id, -32603,   // JSON-RPC InternalError
                "the request could not be completed (" + cause.getClass().getSimpleName() + ")");
    }

    /** Returns true when the server should stop (on {@code exit}). */
    private boolean dispatch(String method, JsonNode id, JsonNode params) {
        switch (method) {
            case "initialize" -> { captureRoots(params); respond(id, initializeResult()); }
            case "initialized" -> registerFileWatchers();
            case "$/setTrace", "workspace/didChangeConfiguration" -> { /* no-op */ }
            case "textDocument/didOpen" -> InboundDecoders.decode(InboundDecoders.DID_OPEN, params)
                    .ifPresent(p -> { documents.open(p.uri(), p.text()); publishAll(); });
            case "textDocument/didChange" -> InboundDecoders.decode(InboundDecoders.DID_CHANGE, params)
                    .ifPresent(p -> { documents.change(p.uri(), p.text()); publishAll(); });
            case "textDocument/didClose" -> InboundDecoders.decode(InboundDecoders.DOC_REF, params)
                    .ifPresent(p -> { documents.close(p.uri()); clearDiagnostics(p.uri()); });
            case "workspace/didChangeWatchedFiles" -> {
                workspace.markChanged();   // a file changed on disk; drop the cached scan and re-read
                publishAll();
            }
            case "textDocument/documentSymbol" -> respond(id, documentSymbols(params));
            case "textDocument/semanticTokens/full" -> respond(id, semanticTokens(params));
            case "textDocument/hover" -> respond(id, hover(params));
            case "textDocument/definition" -> respond(id, definition(params));
            case "textDocument/references" -> respond(id, references(params));
            case "textDocument/completion" -> respond(id, completion(params));
            case "textDocument/codeAction" -> respond(id, codeActions(params));
            case "textDocument/codeLens" -> respond(id, codeLenses(params));
            case "textDocument/rename" -> respond(id, rename(params));
            case "textDocument/formatting" -> respond(id, formatting(params));
            case "shutdown" -> respond(id, null);
            case "exit" -> { return true; }
            default -> {
                if (id != null && !id.isNull()) {
                    respondError(id, -32601, "method not found: " + method);
                }
            }
        }
        return false;
    }

    // --- capabilities ---

    /** Records the workspace roots the client announces, from {@code workspaceFolders} (preferred) or
     * the legacy {@code rootUri}, so the analyzer can resolve names across the whole module set. */
    private void captureRoots(JsonNode params) {
        if (params == null || params.isNull()) {
            return;
        }
        List<String> roots = new ArrayList<>();
        JsonNode folders = params.get("workspaceFolders");
        if (folders != null && folders.isArray()) {
            for (JsonNode folder : folders) {
                JsonNode uri = folder.get("uri");
                if (uri != null && !uri.isNull()) {
                    roots.add(uri.asString());
                }
            }
        }
        JsonNode rootUri = params.get("rootUri");
        if (roots.isEmpty() && rootUri != null && !rootUri.isNull()) {
            roots.add(rootUri.asString());
        }
        workspace.setRoots(roots);
        analyzer.measure(adequacyAsked(params));
    }

    /**
     * How much of what the rows cover this client asked to be told, from
     * {@code initializationOptions.souther.adequacy}: {@code off}, {@code witness} or {@code all}.
     *
     * <p>Off unless asked, and one setting rather than one per measure. What separates them is what
     * they cost: {@code witness} reads what the compile already ran, and {@code all} generates a
     * second set of classes and runs every row again — on every save, in an editor. Nothing that
     * costs that should arrive by default.
     */
    private static Adequacy.Asked adequacyAsked(JsonNode params) {
        JsonNode options = params.get("initializationOptions");
        JsonNode souther = options == null ? null : options.get("souther");
        JsonNode asked = souther == null ? null : souther.get("adequacy");
        if (asked == null || asked.isNull()) {
            return Adequacy.Asked.NOTHING;
        }
        return switch (asked.asString()) {
            case "witness" -> Adequacy.Asked.reportOnly(Adequacy.Level.WITNESS);
            case "all" -> Adequacy.Asked.reportOnly(Adequacy.Level.ALL);
            default -> Adequacy.Asked.NOTHING;
        };
    }

    private Map<String, Object> initializeResult() {
        Map<String, Object> capabilities = new LinkedHashMap<>();
        capabilities.put("textDocumentSync", 1);   // 1 = full document sync
        capabilities.put("documentSymbolProvider", true);
        capabilities.put("hoverProvider", true);
        capabilities.put("definitionProvider", true);
        capabilities.put("referencesProvider", true);
        capabilities.put("renameProvider", true);
        capabilities.put("completionProvider", Map.of());   // invoked completion; no trigger characters
        capabilities.put("codeActionProvider", true);
        capabilities.put("codeLensProvider", Map.of("resolveProvider", false));
        capabilities.put("documentFormattingProvider", true);
        Map<String, Object> semanticTokens = new LinkedHashMap<>();
        semanticTokens.put("legend", Map.of("tokenTypes", Analyzer.TOKEN_TYPES,
                "tokenModifiers", List.of()));
        semanticTokens.put("full", true);
        capabilities.put("semanticTokensProvider", semanticTokens);
        Map<String, Object> result = new LinkedHashMap<>();
        result.put("capabilities", capabilities);
        result.put("serverInfo", Map.of("name", "souther-lsp", "version", "0.1.0"));
        return result;
    }

    // --- document symbols ---

    private List<Object> documentSymbols(JsonNode params) {
        String uri = InboundDecoders.decode(InboundDecoders.DOC_REF, params)
                .map(Params.DocRef::uri).orElse(null);
        String text = uri == null ? null : documents.get(uri);
        if (text == null) {
            return List.of();
        }
        List<Object> out = new ArrayList<>();
        for (DocumentSymbol s : analyzer.documentSymbols(text)) {
            out.add(symbolJson(s));
        }
        return out;
    }

    private Object symbolJson(DocumentSymbol s) {
        Map<String, Object> m = new LinkedHashMap<>();
        m.put("name", s.name());
        m.put("kind", s.kind());
        m.put("range", rangeJson(s.range()));
        m.put("selectionRange", rangeJson(s.selectionRange()));
        if (!s.children().isEmpty()) {
            List<Object> children = new ArrayList<>();
            for (DocumentSymbol child : s.children()) {
                children.add(symbolJson(child));
            }
            m.put("children", children);
        }
        return m;
    }

    // --- hover / definition ---

    private Object hover(JsonNode params) {
        Params.PositionParams p = InboundDecoders.decode(InboundDecoders.POSITION_PARAMS, params)
                .orElse(null);
        String text = p == null ? null : documents.get(p.uri());
        if (text == null) {
            return null;
        }
        ModuleGraph graph = workspace.snapshot(documents.openDocuments());
        Hover h = analyzer.hover(p.uri(), text, p.position(), graph).orElse(null);
        if (h == null) {
            return null;
        }
        Map<String, Object> m = new LinkedHashMap<>();
        m.put("contents", Map.of("kind", "markdown", "value", h.contents()));
        m.put("range", rangeJson(h.range()));
        return m;
    }

    private Object definition(JsonNode params) {
        Params.PositionParams p = InboundDecoders.decode(InboundDecoders.POSITION_PARAMS, params)
                .orElse(null);
        if (p == null || documents.get(p.uri()) == null) {
            return null;
        }
        ModuleGraph graph = workspace.snapshot(documents.openDocuments());
        return analyzer.definition(p.uri(), p.position(), graph)
                .<Object>map(loc -> Map.of("uri", loc.uri(), "range", rangeJson(loc.range())))
                .orElse(null);
    }

    private Object references(JsonNode params) {
        Params.PositionParams p = InboundDecoders.decode(InboundDecoders.POSITION_PARAMS, params)
                .orElse(null);
        if (p == null || documents.get(p.uri()) == null) {
            return List.of();
        }
        boolean includeDeclaration = includeDeclaration(params);
        ModuleGraph graph = workspace.snapshot(documents.openDocuments());
        List<Object> out = new ArrayList<>();
        for (Location loc : analyzer.references(p.uri(), p.position(), graph, includeDeclaration)) {
            out.add(Map.of("uri", loc.uri(), "range", rangeJson(loc.range())));
        }
        return out;
    }

    /** The {@code context.includeDeclaration} flag of a references request; defaults to true. */
    private static boolean includeDeclaration(JsonNode params) {
        if (params == null) {
            return true;
        }
        JsonNode context = params.get("context");
        if (context == null || context.get("includeDeclaration") == null) {
            return true;
        }
        return context.get("includeDeclaration").asBoolean();
    }

    // --- completion ---

    private Object completion(JsonNode params) {
        Params.PositionParams p = InboundDecoders.decode(InboundDecoders.POSITION_PARAMS, params)
                .orElse(null);
        String text = p == null ? null : documents.get(p.uri());
        if (text == null) {
            return List.of();
        }
        List<Object> items = new ArrayList<>();
        for (CompletionItem item : analyzer.completions(text, p.position())) {
            items.add(Map.of("label", item.label(), "kind", item.kind()));
        }
        return items;
    }

    // --- code lenses ---

    /**
     * The line above each behavior saying what its rows cover of it.
     *
     * <p>Answered from the workspace snapshot rather than from this document alone: a behavior's rows
     * are written across its module's source and any attached files, and one file cannot say what the
     * others cover. Empty unless the client asked to be measured, which it does through
     * {@code souther.adequacy} at initialization.
     */
    private Object codeLenses(JsonNode params) {
        String uri = InboundDecoders.decode(InboundDecoders.DOC_REF, params)
                .map(Params.DocRef::uri).orElse(null);
        if (uri == null || documents.get(uri) == null) {
            return List.of();
        }
        ModuleGraph graph = workspace.snapshot(documents.openDocuments());
        List<Object> out = new ArrayList<>();
        for (CodeLens lens : analyzer.codeLenses(uri, graph)) {
            out.add(Map.of("range", rangeJson(lens.range()),
                    "command", Map.of("title", lens.title(), "command", "")));
        }
        return out;
    }

    // --- code actions ---

    private Object codeActions(JsonNode params) {
        Params.CodeActionParams p = InboundDecoders.decode(InboundDecoders.CODE_ACTION, params)
                .orElse(null);
        String text = p == null ? null : documents.get(p.uri());
        // Only the range's diagnostics can be fixed, so with none in context there is usually nothing
        // to offer. Short-circuiting here avoids a recompile — the analyzer's fix lookup compiles the
        // file — on every lightbulb over clean code, which is the overwhelmingly common case. Where
        // adequacy is being measured there is one offer that is not about a diagnostic — the rows a
        // behavior does not cover — so the short cut is skipped, and only for a client that asked.
        if (text == null || (!hasContextDiagnostics(params) && !analyzer.measuring())) {
            return List.of();
        }
        List<Object> out = new ArrayList<>();
        ModuleGraph graph = workspace.snapshot(documents.openDocuments());
        for (CodeAction a : analyzer.codeActions(p.uri(), text, p.range(), graph)) {
            Map<String, Object> action = new LinkedHashMap<>();
            action.put("title", a.title());
            action.put("kind", "quickfix");
            action.put("edit", Map.of("changes", Map.of(a.uri(), List.of(textEdit(a.range(), a.newText())))));
            out.add(action);
        }
        return out;
    }

    /** Whether the codeAction request carries any client-side diagnostics for its range. */
    private static boolean hasContextDiagnostics(JsonNode params) {
        if (params == null) {
            return false;
        }
        JsonNode context = params.get("context");
        if (context == null) {
            return false;
        }
        JsonNode diagnostics = context.get("diagnostics");
        return diagnostics != null && diagnostics.isArray() && !diagnostics.isEmpty();
    }

    // --- rename ---

    /** A {@code WorkspaceEdit} renaming the name under the cursor everywhere it is used,
     * or {@code null} when the new name is not a legal identifier or the cursor is not on a
     * renameable symbol — the client then reports the rename as unavailable. */
    private Object rename(JsonNode params) {
        Params.RenameParams p = InboundDecoders.decode(InboundDecoders.RENAME, params).orElse(null);
        if (p == null || documents.get(p.uri()) == null || !analyzer.isValidName(p.newName())) {
            return null;
        }
        ModuleGraph graph = workspace.snapshot(documents.openDocuments());
        Map<String, List<souther.lsp.protocol.TextEdit>> edits =
                analyzer.renameEdits(p.uri(), p.position(), graph, p.newName());
        if (edits.isEmpty()) {
            return null;
        }
        Map<String, Object> changes = new LinkedHashMap<>();
        for (Map.Entry<String, List<souther.lsp.protocol.TextEdit>> e : edits.entrySet()) {
            List<Object> textEdits = new ArrayList<>();
            for (souther.lsp.protocol.TextEdit edit : e.getValue()) {
                // what to write comes with the place: a binding written as a field's own name is
                // renamed by naming the field it reads, not by writing over it
                textEdits.add(textEdit(edit.range(), edit.newText()));
            }
            changes.put(e.getKey(), textEdits);
        }
        return Map.of("changes", changes);
    }

    // --- formatting ---

    private Object formatting(JsonNode params) {
        String uri = InboundDecoders.decode(InboundDecoders.DOC_REF, params)
                .map(Params.DocRef::uri).orElse(null);
        String text = uri == null ? null : documents.get(uri);
        if (text == null) {
            return List.of();
        }
        return analyzer.format(text)
                .filter(formatted -> !formatted.equals(text))   // no edit when already canonical
                .<Object>map(formatted -> List.of(fullEdit(text, formatted)))
                .orElse(List.of());
    }

    /** A single {@code TextEdit} replacing the whole document with {@code formatted}. */
    private static Map<String, Object> fullEdit(String text, String formatted) {
        LineIndex lines = new LineIndex(text);
        int end = text.length();
        Range range = new Range(new Position(0, 0),
                new Position(lines.lspLine(end), lines.lspColumn(end)));
        return textEdit(range, formatted);
    }

    /** A {@code TextEdit}: replace {@code range} with {@code newText}. */
    private static Map<String, Object> textEdit(Range range, String newText) {
        Map<String, Object> edit = new LinkedHashMap<>();
        edit.put("range", rangeJson(range));
        edit.put("newText", newText);
        return edit;
    }

    // --- semantic tokens ---

    private Object semanticTokens(JsonNode params) {
        String uri = InboundDecoders.decode(InboundDecoders.DOC_REF, params)
                .map(Params.DocRef::uri).orElse(null);
        String text = uri == null ? null : documents.get(uri);
        if (text == null) {
            return Map.of("data", List.of());
        }
        List<Integer> data = new ArrayList<>();
        for (int value : analyzer.semanticTokens(text)) {
            data.add(value);
        }
        return Map.of("data", data);
    }

    // --- diagnostics ---

    /** Recomputes diagnostics for the whole workspace and publishes each open document's set — an edit
     * to one module can change what its importers report, so every open file is refreshed together. */
    private void publishAll() {
        ModuleGraph graph = workspace.snapshot(documents.openDocuments());
        Map<String, List<LspDiagnostic>> byUri = analyzer.diagnostics(graph, workspace.modulePath());
        for (String uri : documents.uris()) {
            publish(uri, byUri.getOrDefault(uri, List.of()));
        }
    }

    private void publish(String uri, List<LspDiagnostic> diagnostics) {
        List<Object> items = new ArrayList<>();
        for (LspDiagnostic d : diagnostics) {
            Map<String, Object> item = new LinkedHashMap<>();
            item.put("range", rangeJson(d.range()));
            item.put("severity", d.severity());
            if (d.code() != null) {
                item.put("code", d.code());
            }
            item.put("source", "souther");
            item.put("message", d.message());
            if (!d.tags().isEmpty()) {
                item.put("tags", d.tags());
            }
            if (!d.related().isEmpty()) {
                List<Object> related = new ArrayList<>();
                for (LspDiagnostic.Related r : d.related()) {
                    related.add(Map.of("location",
                            Map.of("uri", r.uri(), "range", rangeJson(r.range())),
                            "message", r.message()));
                }
                item.put("relatedInformation", related);
            }
            items.add(item);
        }
        notify("textDocument/publishDiagnostics", Map.of("uri", uri, "diagnostics", items));
    }

    private void clearDiagnostics(String uri) {
        notify("textDocument/publishDiagnostics", Map.of("uri", uri, "diagnostics", List.of()));
    }

    private static Map<String, Object> rangeJson(Range r) {
        return Map.of("start", positionJson(r.start()), "end", positionJson(r.end()));
    }

    private static Map<String, Object> positionJson(Position p) {
        return Map.of("line", p.line(), "character", p.character());
    }

    // --- JSON-RPC framing of responses / notifications ---

    private void respond(JsonNode id, Object result) {
        Map<String, Object> message = new LinkedHashMap<>();
        message.put("jsonrpc", "2.0");
        message.put("id", id);
        message.put("result", result);
        conn.write(JSON.writeValueAsString(message));
    }

    private void respondError(JsonNode id, int code, String text) {
        Map<String, Object> message = new LinkedHashMap<>();
        message.put("jsonrpc", "2.0");
        message.put("id", id);
        message.put("error", Map.of("code", code, "message", text));
        conn.write(JSON.writeValueAsString(message));
    }

    private void notify(String method, Object params) {
        Map<String, Object> message = new LinkedHashMap<>();
        message.put("jsonrpc", "2.0");
        message.put("method", method);
        message.put("params", params);
        conn.write(JSON.writeValueAsString(message));
    }

    /** Asks the client to watch the workspace's {@code .sou} files and report on-disk changes via
     * {@code workspace/didChangeWatchedFiles}, so the cached disk scan is invalidated when a file is
     * created, edited, or deleted outside the editor rather than relying on the client watching by
     * default. The registration response is a no-op here (dropped by {@link #run}); a client without
     * dynamic registration simply ignores the request. */
    private void registerFileWatchers() {
        Map<String, Object> registration = new LinkedHashMap<>();
        registration.put("id", "souther-sou-watcher");
        registration.put("method", "workspace/didChangeWatchedFiles");
        registration.put("registerOptions",
                Map.of("watchers", List.of(Map.of("globPattern", "**/*.sou"))));
        sendRequest("client/registerCapability", Map.of("registrations", List.of(registration)));
    }

    private void sendRequest(String method, Object params) {
        Map<String, Object> message = new LinkedHashMap<>();
        message.put("jsonrpc", "2.0");
        message.put("id", "souther-" + nextRequestId++);
        message.put("method", method);
        message.put("params", params);
        conn.write(JSON.writeValueAsString(message));
    }
}
