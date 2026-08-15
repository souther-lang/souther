package souther.compiler.diag;

import java.util.Objects;

/** Code written where this compile cannot show it, met at {@code reachedFrom}. */
record OutOfSightCitation(String declaration, SourceRef reachedFrom)
        implements Citation.OutOfSight {

    OutOfSightCitation {
        Objects.requireNonNull(declaration, "code out of sight is reached by a name");
        Objects.requireNonNull(reachedFrom, "a citation is about a place");
    }
}
