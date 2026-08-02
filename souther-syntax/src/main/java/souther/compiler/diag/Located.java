package souther.compiler.diag;

import java.util.List;

/**
 * A diagnostic and which of the sources a compile was handed it came from. A {@link Diagnostic}
 * says where in a file it is; which file that is belongs to the compile, not to the diagnostic, so
 * it is carried alongside.
 *
 * @param diagnostic what was found
 * @param sourceIndex the source it belongs to, or {@code -1} when it names none — which covers a
 *        single-source compile, where the caller knows the file it handed over
 */
public record Located(Diagnostic diagnostic, int sourceIndex) {

    /** The index a diagnostic that names no source carries. */
    public static final int NO_SOURCE = -1;

    /**
     * The one of {@code sources} that {@code index} names, or null when it names none — so a caller
     * quotes no line rather than the wrong one.
     *
     * <p>A compile of one source names none: it drops the index, since the caller knows the file it
     * handed over. The single source it was given is the answer there however the diagnostic is
     * tagged, which is why one item is not read as "index 0 or nothing".
     */
    public static <T> T in(List<T> sources, int index) {
        if (sources.size() == 1) {
            return sources.get(0);
        }
        return index >= 0 && index < sources.size() ? sources.get(index) : null;
    }
}
