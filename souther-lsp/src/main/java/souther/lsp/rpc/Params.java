package souther.lsp.rpc;

import souther.lsp.protocol.Position;
import souther.lsp.protocol.Range;

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

    /**
     * {@code textDocument/selectionRange}: the document and every place a selection is to widen
     * from.
     *
     * <p>Several, because an editor may hold several cursors, and each of them widens through its
     * own nesting. One answer per place asked about, in the order they were asked.
     */
    public record PositionsParams(String uri, java.util.List<Position> positions) {
    }

    /** {@code workspace/symbol}: what is being looked for. Empty asks for everything, which is what
     *  the protocol says an empty query means. */
    public record Query(String query) {
    }

    /** {@code textDocument/rename}: the document, the cursor, and the new name to bind. */
    public record RenameParams(String uri, Position position, String newName) {
    }

    /**
     * A request that names a document and a stretch of it ({@code codeAction},
     * {@code inlayHint}).
     *
     * <p>One record for both, because what is decoded is the same two things — a codeAction's
     * context carries diagnostics, and the analyzer recomputes those rather than reading them, so
     * nothing of it is decoded. A record per method would be the same shape written twice and free
     * to drift.
     */
    public record RangeParams(String uri, Range range) {
    }
}
