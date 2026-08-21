package souther.compiler.flow;

/**
 * What got a run down a path, in whatever words the naming has for it, and whether they say all of
 * it.
 *
 * <p>Two fields and not one, because the second is about the naming and the first is about the run.
 * A reading that steers rows takes both; a reading that asks what a value comes to takes neither.
 *
 * @param path         the conditions along the way, as the naming writes them
 * @param completeness whether the naming could write all of them
 */
public record Provenance<P>(P path, Completeness completeness) {

    public Provenance {
        if (path == null) {
            throw new IllegalArgumentException("a path with nothing on it is still a path");
        }
        if (completeness == null) {
            throw new IllegalArgumentException("a path is either named whole or it is not: " + path);
        }
    }

    /** The same path, with something on the way to it that the naming could not write down. */
    public Provenance<P> partial() {
        return completeness == Completeness.PARTIAL
                ? this : new Provenance<>(path, Completeness.PARTIAL);
    }

    public boolean isComplete() {
        return completeness == Completeness.COMPLETE;
    }
}
