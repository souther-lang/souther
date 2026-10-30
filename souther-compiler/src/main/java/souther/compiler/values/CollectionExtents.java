package souther.compiler.values;

/**
 * What the language holds of how many elements a collection has.
 *
 * <p>The runtime keeps a list, a set and a map in the JVM's own collections, whose size is an
 * {@code int}. The number is kept here and read by the binder that gives the size operations their
 * end ({@code OperationFactBinder}), as {@link TextExtents#LONGEST_STRING} is for a string.
 */
public final class CollectionExtents {

    /** The most elements a list or a set holds, and the most entries a map does. */
    public static final long MOST_ELEMENTS = Integer.MAX_VALUE;

    private CollectionExtents() {
    }
}
