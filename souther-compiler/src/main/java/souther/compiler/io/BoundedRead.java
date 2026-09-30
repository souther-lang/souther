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

    /** The most bytes read of one class file that was found on a class path. */
    public static final long CLASS_FILE_BYTES = 16L * 1024 * 1024;

    /**
     * The most bytes read of one source file that was found under a root or inside an archive. A
     * file the caller names directly is the caller's own and is read as it is.
     */
    public static final long SOURCE_FILE_BYTES = 16L * 1024 * 1024;

    /** The most entries of one directory tree or one archive that a single walk or listing looks at. */
    public static final long MOST_ENTRIES = 1_000_000;

    /** The most entries all the scans of one request look at together; see {@link WorkBudget}. */
    public static final long MOST_ENTRIES_PER_REQUEST = 4 * MOST_ENTRIES;

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
