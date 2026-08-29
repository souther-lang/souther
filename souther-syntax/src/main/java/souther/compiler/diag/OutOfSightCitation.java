package souther.compiler.diag;

import java.util.Objects;

/** Code written where this compile cannot show it, the position being inside that code and so
 *  nowhere a reader can be sent. */
record OutOfSightCitation(SourceProvenance provenance) implements Citation.OutOfSight {

    OutOfSightCitation {
        Objects.requireNonNull(provenance, "code out of sight came from somewhere");
    }
}
