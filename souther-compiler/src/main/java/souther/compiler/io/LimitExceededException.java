package souther.compiler.io;

import java.io.IOException;

/** Input that is larger than what the reader is willing to hold. */
public final class LimitExceededException extends IOException {
    private static final long serialVersionUID = 1L;

    public LimitExceededException(String message) {
        super(message);
    }
}
