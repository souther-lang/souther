package souther.compiler.generated;

import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.Set;

/**
 * What a failure out of a generated class says about the compiler's own output.
 *
 * <p>A generated class that the JVM refuses to link ({@code VerifyError}, {@code ClassFormatError},
 * {@code NoSuchMethodError}) is this compiler's output, or the library it was generated against,
 * failing. It is not about any row or any example, so a reader that turns it into "nothing could be
 * observed" sends the author to look at something that is fine, and one that reads the empty result
 * as agreement lets a broken back end report every model consistent.
 *
 * <p>Two things that look the same are not defects. A class of the runtime that cannot be found
 * ({@link #runtimeAbsent}): the runtime is {@code provided}, so a build that compiles Souther without
 * it can generate the classes and not load them, and what reads it can go on without the observation
 * the class would have made. A class initializer that threw: that is the evaluated code failing, and
 * what it failed with is read from its cause.
 *
 * <p>Asked of the throwable and of every cause under it, because the failure is raised inside the
 * generated code and reaches a catch through whatever stands between: a reflective call wraps it in
 * an {@code InvocationTargetException}, and a layer that reports its own failure carries it as a
 * cause. Read off the outermost throwable only, a defect wrapped once is a value that could not be
 * built.
 */
public final class GeneratedLinkage {

    private static final String RUNTIME_PACKAGE = "souther.runtime.";

    /** What the JVM says of a class whose initializer already failed once. */
    private static final String INITIALIZER_FAILED = "Could not initialize class ";

    private GeneratedLinkage() {}

    /**
     * Whether {@code cause} is a class of the runtime not being found.
     *
     * <p>That is all it says. It does not say the runtime is not on the class path: a runtime of
     * another version that lacks a class the generated code names fails the same way, and so is read
     * as absent here.
     */
    public static boolean runtimeAbsent(Throwable cause) {
        return cause instanceof NoClassDefFoundError missing
                && missing.getMessage() != null
                && missing.getMessage().replace('/', '.').startsWith(RUNTIME_PACKAGE);
    }

    /**
     * Returns where nothing in {@code thrown} or its causes is a generated class failing to link,
     * and otherwise throws what a compiler failing at its own output is: an unchecked exception
     * holding the error, which the command line reports as an internal compiler error.
     */
    public static void rejectDefect(Throwable thrown) {
        Set<Throwable> seen = Collections.newSetFromMap(new IdentityHashMap<>());
        for (Throwable each = thrown; each != null && seen.add(each); each = each.getCause()) {
            if (each instanceof GeneratedClassDefect already) {
                throw already;
            }
            if (each instanceof LinkageError failure && isDefect(failure)) {
                throw new GeneratedClassDefect(failure);
            }
        }
    }

    private static boolean isDefect(LinkageError failure) {
        if (runtimeAbsent(failure) || failure instanceof ExceptionInInitializerError) {
            return false;
        }
        return !(failure instanceof NoClassDefFoundError
                && failure.getMessage() != null
                && failure.getMessage().startsWith(INITIALIZER_FAILED));
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
