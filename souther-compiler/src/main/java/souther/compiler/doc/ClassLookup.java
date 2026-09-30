package souther.compiler.doc;

import java.io.IOException;
import java.util.List;

/**
 * Where the types a source names are found, when the class path is not something javac may open
 * for itself.
 *
 * <p>javac given a class path string searches it with its own file access, which knows nothing of
 * what the caller allows to be read. Given this instead, it asks for the classes of one package at
 * a time and gets bytes that were read the way every other file of the run is read.
 */
interface ClassLookup {

    /** The classes directly in {@code packageName}, from every entry, in class path order. */
    List<Held> classesIn(String packageName) throws IOException;

    /** A class file the lookup holds, and how to read it. */
    record Held(String binaryName, Bytes bytes) {}

    /** The bytes of a class file, read when asked for. */
    interface Bytes {
        byte[] get() throws IOException;
    }
}
