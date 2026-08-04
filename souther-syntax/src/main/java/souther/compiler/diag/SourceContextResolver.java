package souther.compiler.diag;

import java.util.HashMap;
import java.util.Map;
import java.util.function.Function;

/**
 * What text to quote for a source id. A diagnostic points into as many files as it has regions, so
 * a renderer is handed this rather than one already-resolved {@link SourceContext}.
 *
 * <p>An id it does not know, and a file it cannot read, both answer null — the renderer then leaves
 * the snippet out rather than quoting a line from somewhere else.
 *
 * <p>A secondary that names no source of its own is never asked about: it inherits the diagnostic's
 * ({@link LabeledRegion#sourceIdOr(String)}) before anything is looked up. A whole diagnostic that
 * names none is asked about as {@link Located#NO_SOURCE}, and what that means is the caller's to
 * say — a compile of one source names none and yet has exactly one file to quote.
 *
 * <p>Answering twice for one id must give the same text, since a caret is drawn under a line quoted
 * from it. {@link #memoized} is how a caller reading files off disk keeps that true, and it also
 * keeps a compile that reports many problems in one file from reading it many times. Rendering
 * walks one list on one thread, so nothing here is synchronised.
 */
@FunctionalInterface
public interface SourceContextResolver {

    /** The text and display name for {@code sourceId}, or null when there is none to quote. */
    SourceContext sourceOf(String sourceId);

    /** Nothing to quote for anything — a caller that has no sources to hand. */
    static SourceContextResolver none() {
        return id -> null;
    }

    /** A resolver that asks {@code loader} once per id and keeps the answer, absence included. */
    static SourceContextResolver memoized(Function<String, SourceContext> loader) {
        Map<String, SourceContext> known = new HashMap<>();
        return id -> {
            if (known.containsKey(id)) {
                return known.get(id);
            }
            SourceContext found = loader.apply(id);
            known.put(id, found);
            return found;
        };
    }
}
