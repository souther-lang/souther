package souther.compiler.diag;

import java.util.Objects;

/** Code written where this compile cannot show it, met at {@code at} — a position in a text the
 *  caller handed over and this compilation cannot name. */
record UnplacedElsewhereCitation(SourceProvenance provenance, SourcePos at)
        implements Citation.UnplacedElsewhere {

    UnplacedElsewhereCitation {
        Objects.requireNonNull(provenance, "code out of sight came from somewhere");
        Objects.requireNonNull(at, "a citation is about a place");
    }
}
