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
 * it points at nothing and is said in words instead. A report that points at nothing is asked about
 * under the file it is listed on ({@link ReportContext#filedUnder()}), and one in a text the caller
 * handed over is not asked about here at all — {@link #quotedFrom} has the text.
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

    /**
     * The text to quote a spot from, or null when there is none.
     *
     * <p>A switch over where the spot is rather than a lookup, because one of the two arms is not a
     * lookup: a caller reading a text it has no identity for handed the text over, and asking this
     * for an identity nobody gave is what used to come back as "no file" for a place the caller was
     * holding the file of.
     */
    default SourceContext quotedFrom(Spot spot) {
        return switch (spot) {
            case Spot.InSource in -> sourceOf(in.place().source());
            case Spot.InTextBeingRead(TextBeingRead text, UnnamedRegion _) -> switch (text) {
                case TextBeingRead.UnderAnId(SourceId source) -> sourceOf(source);
                case TextBeingRead.AsHandedOver(SourceContext held) -> held;
            };
        };
    }

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
