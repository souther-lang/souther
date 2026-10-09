package souther.compiler.semantics;

import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;

/**
 * A relation between two numbers of the arguments: {@code left rel right}. What a case is reached
 * under, written in the arguments the operation was given and in nothing else — an argument, or a
 * form of them with a constant, as {@code n < 0} compares an argument with nought.
 *
 * @param <A> the word for an argument of the operation
 */
public record ArgumentsStand<A>(LinearForm<A> left, Rel rel, LinearForm<A> right) {

    public ArgumentsStand {
        java.util.Objects.requireNonNull(left, "a relation has two sides");
        java.util.Objects.requireNonNull(rel, "and stands some way");
        java.util.Objects.requireNonNull(right, "a relation has two sides");
    }

    /** {@code left rel right}, two arguments as themselves. */
    public static <A> ArgumentsStand<A> of(A left, Rel rel, A right) {
        return new ArgumentsStand<>(LinearForm.atom(left), rel, LinearForm.atom(right));
    }

    /** The argument {@code side} is, where it is one argument as itself, or null. */
    public static <A> A theArgument(LinearForm<A> side) {
        if (!side.constant().equals(ExactRatio.ZERO) || side.coefs().size() != 1) {
            return null;
        }
        var only = side.coefs().entrySet().iterator().next();
        return only.getValue().equals(ExactRatio.ONE) ? only.getKey() : null;
    }
}
