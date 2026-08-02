package souther.compiler.diag;

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
}
