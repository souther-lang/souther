package souther.compiler.diag;

import java.util.Objects;

/**
 * The coordinate carrying this stands in for code written in {@code declaration}, which this compile
 * has no source for. It is where the code was reached from — the call the body was spliced into —
 * and not where the code is.
 *
 * <p>A class and not a record, so that {@code declaration} is held without being published. A record
 * generates an accessor, and an accessor here is the thing this exists to remove: a reader holding
 * one could build a statement about where code is written without going through {@link Citation},
 * which is how the same coordinate came to be presented as a place by three surfaces and qualified
 * by one.
 *
 * <p>The declaration is in the equality all the same. Provenance is part of what a
 * {@link SourcePos} is, and two positions that differ in it are read differently by every surface —
 * so an incremental answer that changed only here has changed, and two diagnostics that differ only
 * here are two problems. Being able to compare is not being able to read: a caller can ask whether
 * this is the provenance it already holds, and cannot ask what it is.
 *
 * <p>The declaration is in {@code toString} for the opposite reason. Nothing builds a report out of
 * it, and it is the first thing anybody looks at when a caret is somewhere unexpected.
 */
final class StoodInFor extends WrittenAt {

    private final String declaration;

    StoodInFor(String declaration) {
        this.declaration = Objects.requireNonNull(declaration,
                "code out of sight is reached by a name");
    }

    @Override
    public boolean isOutOfSight() {
        return true;
    }

    @Override
    Citation cite(SourcePos reachedFrom) {
        return new OutOfSightCitation(declaration,
                new SourceRef(reachedFrom.sourceId(), reachedFrom));
    }

    @Override
    public boolean equals(Object other) {
        return other instanceof StoodInFor that && declaration.equals(that.declaration);
    }

    @Override
    public int hashCode() {
        return declaration.hashCode();
    }

    @Override
    public String toString() {
        return "OutOfSight[declaration=" + declaration + "]";
    }
}
