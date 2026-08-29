package souther.compiler.diag;

import java.util.Objects;

/** Code written where this compile cannot show it, met at {@code at} — a place in a file the reader
 *  holds, which the placement {@code at} carries guarantees. */
record ReachedCitation(SourceProvenance provenance, SourcePos at) implements Citation.Reached {

    ReachedCitation {
        Objects.requireNonNull(provenance, "code out of sight came from somewhere");
        Objects.requireNonNull(at, "a citation is about a place");
    }
}
