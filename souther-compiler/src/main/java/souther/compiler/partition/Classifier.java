package souther.compiler.partition;

import souther.compiler.observe.ObservedValue;

/**
 * Whether a value an {@code example} row was given belongs to one equivalence class.
 *
 * <p>Separate from being able to produce a value of that class. A class can be recognised in rows the
 * author already wrote while nothing can generate a representative for it — a type whose invariant is
 * a pattern, a record whose fields constrain each other — and treating those as unmeasurable would
 * throw away coverage that is already there.
 */
@FunctionalInterface
public interface Classifier {

    boolean matches(ObservedValue value);

    /** Recognises nothing: a class that exists but cannot be told from another by looking. */
    static Classifier none() {
        return _ -> false;
    }
}
