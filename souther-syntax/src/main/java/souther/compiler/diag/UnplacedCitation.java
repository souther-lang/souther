package souther.compiler.diag;

import java.util.Objects;

/** Code written at {@code at}, in a text this compilation cannot name. */
record UnplacedCitation(SourcePos at) implements Citation.Unplaced {

    UnplacedCitation {
        Objects.requireNonNull(at, "a citation is about a place");
    }
}
