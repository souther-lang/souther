package souther.runtime;

/**
 * A first-class function value — a lambda that has escaped its lexical scope and so cannot be
 * expanded inline (spec §blocks). The backend generates one implementing class per such lambda,
 * with the captured free variables held in final fields and the body compiled into {@link #apply}.
 *
 * <p>Souther functions are multi-argument (not curried), so {@code apply} takes the arguments as an
 * array; a call site of known arity boxes its arguments into it. A function that does not escape is
 * still expanded inline and never becomes an {@code Fn}.
 */
@FunctionalInterface
public interface Fn {
    Object apply(Object[] args);

    /**
     * Stands where a step function is expected that the compiler has shown is never applied — a fold
     * over an empty list literal, whose element type is the bottom and whose step therefore cannot be
     * materialised (it would open a value that is not there). Passing this rather than a null keeps
     * every value the generated code hands around non-null; being applied means the reasoning that
     * placed it was wrong, which is a compiler bug and says so.
     */
    Fn NEVER = args -> {
        throw new IllegalStateException("souther: a fold step over an empty list was applied");
    };
}
