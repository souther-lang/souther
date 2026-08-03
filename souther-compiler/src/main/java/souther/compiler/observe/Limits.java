package souther.compiler.observe;

/**
 * How much of a value an observation keeps.
 *
 * <p>Reading a decoded value into {@link ObservedValue} takes it out of the class loader that built it,
 * which is why the observation exists. It does not, on its own, bound how big the result is — a row may
 * hand a behavior a list of ten thousand lines, and a query answer holding that keeps it for as long as
 * the answer is memoised. So the walk stops at these limits and records what it dropped.
 *
 * @param maxDepth    how deep the walk goes before a subtree becomes {@link ObservedValue.Truncated}
 * @param maxNodes    how many nodes the whole observation may hold
 * @param maxElements how many elements of one collection are kept
 * @param maxText     how many characters of one string are kept
 */
public record Limits(int maxDepth, int maxNodes, int maxElements, int maxText) {

    /** What an example row's inputs are observed under. Wide enough for a domain value written by hand,
     * narrow enough that a pathological fixture cannot sit in the query graph. */
    public static final Limits DEFAULT = new Limits(12, 2000, 64, 1024);

    public Limits {
        if (maxDepth < 1 || maxNodes < 1 || maxElements < 0 || maxText < 0) {
            throw new IllegalArgumentException("limits must be positive: " + maxDepth + ", " + maxNodes
                    + ", " + maxElements + ", " + maxText);
        }
    }
}
