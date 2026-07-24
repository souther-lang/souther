package net.unit8.souther.lsp.rpc;

import net.unit8.souther.lsp.protocol.Position;
import net.unit8.souther.lsp.protocol.Range;

/** The inbound LSP request/notification payloads the server decodes (only the fields it uses). */
public final class Params {

    private Params() {
    }

    /** {@code textDocument/didOpen}: the opened document's uri and full text. */
    public record DidOpen(String uri, String text) {
    }

    /** {@code textDocument/didChange} under full-sync: the uri and the whole new text. */
    public record DidChange(String uri, String text) {
    }

    /** A request that names a document ({@code didClose}, {@code documentSymbol},
     * {@code semanticTokens/full}). */
    public record DocRef(String uri) {
    }

    /** A position-bearing request ({@code hover}, {@code definition}, {@code completion}). */
    public record PositionParams(String uri, Position position) {
    }

    /** {@code textDocument/rename}: the document, the cursor, and the new name to bind. */
    public record RenameParams(String uri, Position position, String newName) {
    }

    /** {@code textDocument/codeAction}: the document and the selected range (the context's
     * diagnostics are recomputed by the analyzer, so they are not decoded). */
    public record CodeActionParams(String uri, Range range) {
    }
}
