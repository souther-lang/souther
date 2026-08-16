package souther.compiler.diag;

import java.util.Objects;

/**
 * Where the code a splice is copying is written — what {@link SourcePos#standingInFor} is told.
 *
 * <p>Its own type because that is the whole of what a splice needs, and because a caller outside this
 * package must be able to carry the answer without reading it. {@code HelperInliner} takes this off
 * the helper's declaration and stamps it over the copy; it never learns which module the helper is
 * in, so it cannot write a place of its own out of one.
 *
 * <p>A placement used to stand in for this, which meant handing a splice a whole text to take one
 * component of — and a value one of whose components is ignored is a value that will be read for it
 * eventually.
 */
public final class DeclaringCode {

    private final SourceProvenance provenance;

    /** Where code a splice is about to copy is written. Public because a caller may say what it is
     *  copying — a parse already says as much when it hands over a published module's text — and
     *  what it may not do is read one back out of a position it was given. */
    public DeclaringCode(SourceProvenance provenance) {
        this.provenance = Objects.requireNonNull(provenance,
                "code copied from somewhere was written there");
    }

    SourceProvenance provenance() {
        return provenance;
    }

    /**
     * The same declaration, reached by {@code name} — what a splice writes when it learns the name
     * the call reaches, a parse of a published module having known only the module.
     *
     * <p>A refinement of one authority's answer and not a second answer: what kind of thing this
     * compile is without is kept, and only the name a reader here writes for it is replaced.
     */
    public DeclaringCode reachedBy(String name) {
        return new DeclaringCode(provenance.reachedBy(name));
    }

    @Override
    public boolean equals(Object other) {
        return other instanceof DeclaringCode that && provenance.equals(that.provenance);
    }

    @Override
    public int hashCode() {
        return provenance.hashCode();
    }

    @Override
    public String toString() {
        return String.valueOf(provenance);
    }
}
