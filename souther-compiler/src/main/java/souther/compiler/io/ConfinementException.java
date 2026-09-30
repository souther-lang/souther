package souther.compiler.io;

import java.io.IOException;

/** A name that would reach outside the tree it was asked of, or through a link inside it. */
public final class ConfinementException extends IOException {
    private static final long serialVersionUID = 1L;

    public ConfinementException(String message) {
        super(message);
    }
}
