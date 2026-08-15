package souther.compiler.diag;

import java.util.Objects;

/** A place a source was read for, where the code it names is written. */
record WrittenCitation(SourceRef at) implements Citation.Written {

    WrittenCitation {
        Objects.requireNonNull(at, "a citation is about a place");
    }
}
