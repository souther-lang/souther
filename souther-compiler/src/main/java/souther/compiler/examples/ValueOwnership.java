package souther.compiler.examples;

import souther.compiler.evaluate.EvaluationContext;
import souther.compiler.generated.GeneratedLinkage;

/**
 * Whose classes a live value is of, which decides what it means when reading one of its members
 * fails.
 *
 * <p>A value a row reads may be one this compile built or one a supplied implementation answered.
 * The first is of classes this compile generated, so a link failure in one of its accessors is this
 * compiler's output failing. The second is of another build's classes, and the same failure is what
 * that build's own dependencies came to. Nothing in the failure says which; the value's class does,
 * through the loader that defined it. That a value exists says nothing about it, since the JVM
 * resolves what an accessor's body names when the body runs, not when the class is linked.
 */
final class ValueOwnership {

    private final ClassLoader own;

    /** @param own the loader this compile's generated classes are defined by */
    ValueOwnership(ClassLoader own) {
        this.own = own;
    }

    /** A reader of values none of whose classes this compile generated. */
    static ValueOwnership none() {
        return new ValueOwnership(null);
    }

    /**
     * Returns where the failure of reading a member of {@code live} says only that the member could
     * not be read, and otherwise raises what it says.
     *
     * <p>A stop is raised, since the value was fine and the evaluation ran out. So is a defect that
     * something below already found, wherever it was wrapped. And so is a link failure in a value
     * of this compile's own classes. A link failure in a value of any other class returns, which is
     * a member that cannot be read.
     */
    void readFailed(Object live, Throwable failure) {
        EvaluationContext.rethrowIfOverspent(failure);
        GeneratedLinkage.rethrowClassified(failure);
        if (own != null && live.getClass().getClassLoader() == own) {
            GeneratedLinkage.rejectDefect(failure);
        }
    }
}
