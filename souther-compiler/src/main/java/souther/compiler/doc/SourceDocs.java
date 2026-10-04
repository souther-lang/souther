package souther.compiler.doc;

import java.nio.file.Path;
import java.nio.file.attribute.FileTime;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * What sources have been read to say about the types they declare, for as long as whoever holds
 * this is asked.
 *
 * <p>Reading one is running the compiler's front end over it against a class path, which costs far
 * more than everything else a {@code jar_api} answer does. A server answering a client asks the same
 * class again — for another member, or for the next part of an answer too long to hand over at once
 * — and the answer has not moved unless the source or a class path entry has.
 *
 * <p>So what an answer is kept under is everything it was read from: the source's text, the type it
 * was asked about, the class path it was resolved against, whether that class path was read through
 * a lookup, and each entry as the file it is now — its path, size and modification time. An entry
 * that is a directory has no such stamp, since what changes in one is a file somewhere below it, and
 * a read against one is not kept.
 *
 * <p>A read is held against the budget of the request that made it. A request that would have run
 * out of budget reading the same source again is answered from here instead, so one of these serves
 * callers that all ask under one budget, as a server's requests do.
 */
final class SourceDocs {

    /** How a source is read when nothing is kept for it. */
    interface Reader {
        SourceDoc read(String source, String binaryName, String classPath, ClassLookup confined);
    }

    /** A class path entry as the file it is now. */
    record Stamp(Path path, long size, FileTime modified) {}

    private record Key(String source, String binaryName, String classPath, boolean confined,
            List<Stamp> entries) {}

    /** How many reads are kept before the one asked for longest ago is let go. */
    private static final int MOST_KEPT = 64;

    /** Reads every time, keeping nothing: a one-shot command asks once. */
    static final SourceDocs NONE = new SourceDocs(SourceDoc::of, false);

    private final Reader reader;
    /** Null when nothing is kept. */
    private final Map<Key, SourceDoc> kept;

    SourceDocs(Reader reader) {
        this(reader, true);
    }

    private SourceDocs(Reader reader, boolean keeps) {
        this.reader = reader;
        this.kept = keeps ? new LinkedHashMap<>(16, 0.75f, true) {
            @Override
            protected boolean removeEldestEntry(Map.Entry<Key, SourceDoc> eldest) {
                return size() > MOST_KEPT;
            }
        } : null;
    }

    /** Kept for a session, reading as {@link SourceDoc#of} does. */
    static SourceDocs forASession() {
        return new SourceDocs(SourceDoc::of);
    }

    /**
     * What {@code source} says about {@code binaryName}, read against {@code classPath} or through
     * {@code confined}. {@code entries} is the class path as it stands, or null when one of its
     * entries has no stamp, and then nothing is kept.
     */
    SourceDoc read(String source, String binaryName, String classPath, ClassLookup confined,
            List<Stamp> entries) {
        if (kept == null || entries == null) {
            return reader.read(source, binaryName, classPath, confined);
        }
        Key key = new Key(source, binaryName, classPath, confined != null, List.copyOf(entries));
        SourceDoc held = kept.get(key);
        if (held != null) {
            return held;
        }
        SourceDoc read = reader.read(source, binaryName, classPath, confined);
        kept.put(key, read);
        return read;
    }
}
