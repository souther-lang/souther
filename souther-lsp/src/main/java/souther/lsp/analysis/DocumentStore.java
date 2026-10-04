package souther.lsp.analysis;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;

/** The open documents, keyed by URI. Full-sync only: each change replaces the whole text. */
public final class DocumentStore {

    private final Map<String, String> texts = new LinkedHashMap<>();

    public void open(String uri, String text) {
        texts.put(uri, text);
    }

    public void change(String uri, String text) {
        texts.put(uri, text);
    }

    public void close(String uri) {
        texts.remove(uri);
    }

    /** The current text of {@code uri}, or {@code null} if it is not open. */
    public String get(String uri) {
        return texts.get(uri);
    }

    /** The URIs of every open document, as a view that refuses a change: only {@link #open},
     *  {@link #change} and {@link #close} alter what is open. */
    public Set<String> uris() {
        return Collections.unmodifiableSet(texts.keySet());
    }

    /** Every open document's text, keyed by URI — the overlay a {@link Workspace} applies over the
     * on-disk sources. A view that refuses a change, and one only the workspace is handed: what it
     * copies from it is the snapshot, and a request would otherwise copy every open document once
     * more before the workspace does. */
    Map<String, String> openDocuments() {
        return Collections.unmodifiableMap(texts);
    }
}
