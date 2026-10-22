package souther.compiler.inputs;

import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.LinearForm;

import java.util.Objects;

/**
 * What a closure computed of one element of a walk, as what it comes to of the element and a form
 * of numbers of the input that stand the same for every element: {@code p.n + bonus} is {@code
 * p.n} of the element and {@code bonus} beside it.
 *
 * <p>{@link ElementValue} stays what one element alone settles, so that wherever it is evaluated
 * an element is all it is handed. What stands beside it is no place of any element, and a
 * reading over the elements says what it comes to over them by how it gathers them ({@link
 * #gathered}).
 *
 * @param relative  what the closure computes of the element
 * @param invariant the numbers of the input beside it, the same for every element; nought where
 *                  there are none
 */
public record ElementComputation(ElementValue relative, LinearForm<NumericTerm> invariant) {

    public ElementComputation {
        Objects.requireNonNull(relative, "a computation is of the element");
        Objects.requireNonNull(invariant, "and of nothing, or of numbers beside it");
        if (invariant.constant().signum() != 0) {
            throw new IllegalArgumentException("a constant is part of what the element comes to,"
                    + " and not of the numbers beside it: " + invariant);
        }
    }

    /** Whether nothing stands beside what the element comes to. */
    public boolean ofTheElementAlone() {
        return invariant.coefs().isEmpty();
    }

    /** How a reading over the elements gathers what each comes to. */
    public enum Gathering {
        /** The least or the greatest of them. */
        AN_END,
        /** What they add up to. */
        A_TOTAL
    }

    /**
     * What {@code ofTheElements}, the number the gathering comes to over what each element comes
     * to of itself, is with what stands beside every element put back: the same form added once
     * to an end, since every element is moved by it alike and the order between them is kept —
     * or null where it is not held here. A total adds it once for every element, which is how
     * many there are times the form, and no form of numbers holds that product; it is held only
     * where nothing stands beside.
     */
    public LinearForm<NumericTerm> gathered(Gathering how, NumericTerm ofTheElements) {
        LinearForm<NumericTerm> alone = LinearForm.atom(ofTheElements);
        if (ofTheElementAlone()) {
            return alone;
        }
        return switch (how) {
            case AN_END -> alone.plus(invariant) instanceof ExactAnswer.Held<LinearForm<NumericTerm>>(
                    LinearForm<NumericTerm> moved) ? moved : null;
            case A_TOTAL -> null;
        };
    }
}
