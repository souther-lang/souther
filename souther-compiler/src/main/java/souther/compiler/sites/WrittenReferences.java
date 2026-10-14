package souther.compiler.sites;

import souther.compiler.diag.SourcePos;
import souther.compiler.types.SourceReferenceOrigin;

import java.util.Map;

/**
 * Where each name a module wrote stands in its own source.
 *
 * <p>Beside {@link WrittenApplications} and read off the same walk. A name written where a value goes
 * is where a copy of what it names is made, so a reader saying which copy a construct stands in has
 * a reference to send somebody to, as it has a call.
 *
 * <p>Filed under {@link SourceReferenceOrigin}, which a copy cannot change, for the reason
 * {@link WrittenApplications} is filed under an origin: a reader that met the reference inside a
 * helper spliced into its own body asks the module that wrote the helper.
 */
public final class WrittenReferences {

    private final Map<SourceReferenceOrigin, SourcePos> byOrigin;

    WrittenReferences(Map<SourceReferenceOrigin, SourcePos> byOrigin) {
        this.byOrigin = Map.copyOf(byOrigin);
    }

    /** Where the reference {@code origin} names is written, or null where this module wrote no
     *  such reference. */
    public SourcePos at(SourceReferenceOrigin origin) {
        return origin == null ? null : byOrigin.get(origin);
    }

    /** How many were found, which is what says a walk reached a module at all. */
    public int count() {
        return byOrigin.size();
    }

    @Override
    public boolean equals(Object other) {
        return other instanceof WrittenReferences written && byOrigin.equals(written.byOrigin);
    }

    @Override
    public int hashCode() {
        return byOrigin.hashCode();
    }

    @Override
    public String toString() {
        return byOrigin.size() + " written references";
    }
}
