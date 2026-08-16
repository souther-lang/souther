package souther.compiler.diag;

import souther.compiler.source.SourceId;

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
 * <p>A secondary is asked about under the source it names, which every one of them does
 * ({@link DiagnosticPlace.InSource}); one with nothing to quote is not asked about at all, because
 * it points at nothing and is said in words instead. A whole diagnostic that names none is asked
 * about as {@link Located#NO_SOURCE}, and what that means is the caller's to say — a compile of one
 * source names none and yet has exactly one file to quote.
 *
 * <p>Answering twice for one id must give the same text, since a caret is drawn under a line quoted
 * from it. {@link #memoized} is how a caller reading files off disk keeps that true, and it also
 * keeps a compile that reports many problems in one file from reading it many times. Rendering
 * walks one list on one thread, so nothing here is synchronised.
 */
@FunctionalInterface
public interface SourceContextResolver {

    /** The text and display name for {@code sourceId}, or null when there is none to quote. */
    SourceContext sourceOf(SourceId sourceId);

    /** Nothing to quote for anything — a caller that has no sources to hand. */
    static SourceContextResolver none() {
        return id -> null;
    }

    /** A resolver that asks {@code loader} once per id and keeps the answer, absence included. */
    static SourceContextResolver memoized(Function<SourceId, SourceContext> loader) {
        Map<SourceId, SourceContext> known = new HashMap<>();
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
