package souther.compiler.generated;

/**
 * What a {@link LinkageError} out of a generated class says.
 *
 * <p>The runtime is {@code provided}, so a build that compiles Souther without it on the class path
 * can generate the classes and not load them. That is the one {@code LinkageError} that says nothing
 * about the model or about this code, and what reads it can go on without the observation the class
 * would have made. The rest of the family says a class was generated or loaded wrong
 * ({@code VerifyError}, {@code ClassFormatError}, {@code NoSuchMethodError}): it is this compiler's
 * output, or the library it was generated against, failing, and it is not about any row or any
 * example. Reading those as "no runtime" would let a broken back end report every model consistent,
 * or send the author to look at a row that is fine.
 */
public final class GeneratedLinkage {

    private static final String RUNTIME_PACKAGE = "souther.runtime.";

    private GeneratedLinkage() {}

    /** Whether {@code cause} is this host having no runtime rather than anything being wrong. */
    public static boolean runtimeAbsent(Throwable cause) {
        return cause instanceof NoClassDefFoundError missing
                && missing.getMessage() != null
                && missing.getMessage().replace('/', '.').startsWith(RUNTIME_PACKAGE);
    }

    /**
     * Returns where {@code failure} is the runtime being absent, and otherwise throws what a
     * compiler failing at its own output is: an unchecked exception holding the error, which the
     * command line reports as an internal compiler error rather than as a fact about the model.
     */
    public static void requireRuntimeAbsent(LinkageError failure) {
        if (!runtimeAbsent(failure)) {
            throw new GeneratedClassDefect(failure);
        }
    }

    /** A class this compiler generated that the JVM refused to link. */
    public static final class GeneratedClassDefect extends IllegalStateException {

        private static final long serialVersionUID = 1L;

        GeneratedClassDefect(LinkageError cause) {
            super("a generated class does not link, which is this compiler's output and not the"
                    + " model: " + cause, cause);
        }
    }
}
