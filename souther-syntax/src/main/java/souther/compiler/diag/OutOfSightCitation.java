package souther.compiler.diag;

import java.util.Objects;

/** Code written where this compile cannot show it, met at {@code reachedFrom}. */
record OutOfSightCitation(SourceProvenance provenance, SourceRef reachedFrom)
        implements Citation.OutOfSight {

    OutOfSightCitation {
        Objects.requireNonNull(provenance, "code out of sight came from somewhere");
        Objects.requireNonNull(reachedFrom, "a citation is about a place");
    }
}
