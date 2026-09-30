package souther.compiler.io;

import java.io.IOException;
import java.io.InputStream;

/**
 * The one way this code reads a whole stream whose size somebody else chose.
 *
 * <p>A file, a jar entry and a message all say how large they are, or simply keep going, and what
 * they say is not what decides how much memory is spent on them. The limit is the reader's, and it is
 * asked for at the call so that no read of foreign input is written without one.
 */
public final class BoundedRead {

    private BoundedRead() {}

    /**
     * Everything {@code in} holds, at most {@code maxBytes} of it.
     *
     * @throws LimitExceededException when the stream holds more
     */
    public static byte[] bytes(InputStream in, long maxBytes) throws IOException {
        long wanted = Math.min(maxBytes + 1, Integer.MAX_VALUE - 8L);
        byte[] data = in.readNBytes((int) wanted);
        if (data.length > maxBytes) {
            throw new LimitExceededException("more than " + maxBytes + " bytes");
        }
        return data;
    }
}
