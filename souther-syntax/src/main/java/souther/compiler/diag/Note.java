package souther.compiler.diag;

import souther.compiler.diag.msg.Supporting;

/**
 * A hint line under a diagnostic (Elm's {@code Hint:}).
 *
 * <p>A hint says what to write instead, and it says it about values of its own — which is why it is
 * a {@link Supporting} message of its own rather than a share of that line's values.
 */
public record Note(Supporting said) {

    public Note {
        java.util.Objects.requireNonNull(said, "a hint says what to write instead");
    }
}
