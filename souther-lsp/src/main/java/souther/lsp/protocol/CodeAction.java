package souther.lsp.protocol;

/**
 * Something an editor offers to do to a document.
 *
 * <p>Two shapes, because two kinds of offer cost different things to work out. A quick fix knows its
 * edit as soon as it knows the diagnostic; writing the rows a behavior does not cover takes putting
 * values through the module's own decoders, which costs a decoder run for each point it settles.
 * Worked out to show the offer, that is paid every time an editor asks what is available here —
 * which is on a cursor move — and thrown away every time nobody takes it.
 *
 * <p>So the second kind carries what it needs to be worked out later, and the protocol's
 * {@code codeAction/resolve} is where somebody taking it asks for the edit.
 */
public sealed interface CodeAction {

    /** What the editor shows. */
    String title();

    /** The document the offer is about. */
    String uri();

    /**
     * What an action does to a document: replacing {@code range} in {@code uri} with {@code newText}.
     *
     * <p>Its own thing rather than fields of an action, because it is what a resolve produces. The
     * protocol says a resolve fills in the properties an action was sent without and alters none of
     * the ones it was sent with, so what is worked out then has to be smaller than an action — able
     * to be added to what the client sent back, and not to stand in for it.
     */
    record Edit(String uri, Range range, String newText) {}

    /** An offer whose edit is already worked out. */
    record Applied(String title, Edit edit) implements CodeAction {

        @Override
        public String uri() {
            return edit.uri();
        }
    }

    /**
     * An offer whose edit is worked out when somebody takes it.
     *
     * <p>What it carries is what identifies the work, and never the work itself or the compilation
     * it came from. A document is edited between the offer being shown and being taken, so the
     * behavior is looked up again in whatever the workspace holds then — an edit built here and
     * handed over later would be applied to a source it was not written against.
     */
    record Deferred(String title, String uri, String module, String behavior)
            implements CodeAction {}
}
