package souther.compiler.semantics;

import souther.compiler.numeric.Rel;

/**
 * A relation between two arguments: {@code left rel right}. What a case is reached under, written
 * in the arguments the operation was given and in nothing else.
 *
 * @param <A> the word for an argument of the operation
 */
public record ArgumentsStand<A>(A left, Rel rel, A right) {

    public ArgumentsStand {
        java.util.Objects.requireNonNull(left, "a relation has two sides");
        java.util.Objects.requireNonNull(rel, "and stands some way");
        java.util.Objects.requireNonNull(right, "a relation has two sides");
    }
}
