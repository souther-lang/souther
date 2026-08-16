package souther.compiler.diag;

import souther.compiler.source.SourceId;

/**
 * What to call a source id in front of a person.
 *
 * <p>A source id identifies a source inside one compile and is whatever the caller handed its
 * sources over as — a position in a list for a build, a document URI for an editor. That is the
 * right thing for a result to carry: two reasons are the same reason when they are about the same
 * source, and only an identity settles that.
 *
 * <p>What to call it is a different question, and its answer is not a property of the source.
 * {@link SourceNames} gives a file the shortest tail of its path that no other file in the same
 * compile shares, so the name of {@code a/model.sou} is {@code model.sou} on its own and
 * {@code a/model.sou} beside a {@code b/model.sou}. A source cannot be asked what it is called
 * without being told what it is being read beside — which is why this is given at the point a report
 * is rendered rather than held with the result.
 *
 * <p>{@link SourceContextResolver} answers the same question for a diagnostic, along with the text
 * to quote. This is the half a report needs, and the two are given by the same caller from the same
 * list of files.
 */
@FunctionalInterface
public interface SourceNameResolver {

    /** What to call {@code sourceId}. An id this does not know stands for itself, so a rendering
     *  still says which of them it is about rather than dropping the subject. */
    String nameOf(SourceId sourceId);

    /**
     * A caller with no names to give: every id stands for itself.
     *
     * <p>For a caller whose ids are already names — an editor keyed on document URIs — and for one
     * rendering a report over sources it did not read off a disk.
     */
    static SourceNameResolver identity() {
        return id -> id == null ? null : id.value();
    }
}
