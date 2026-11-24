package souther.compiler.inputs;

import souther.compiler.numeric.WholeNumberSet;

import java.math.BigInteger;

/**
 * The values of one number at which an equation with another can hold, as far as that is shown
 * and as far as it is possible.
 *
 * <p>{@code weightHere·s + weightThere·c + constant = 0} is asked of {@code c}, the number beside,
 * for the values {@code s} the first takes. Two sets of {@code s} are asked, and they answer
 * different claims:
 * <ul>
 * <li>{@code shown} is worked out from the values {@code s} is shown to take. Where {@code c} is
 * in it, a row is known that holds the equation, and nothing is said of the others.
 * <li>{@code possible} is worked out from a set every value of {@code s} lies in. Where
 * {@code c} is not in it, no row holds the equation, whatever {@code s} the program comes to.
 * </ul>
 * A value in {@code possible} and not in {@code shown} is neither one nor the other: it is not
 * shown to be reached and not shown to be out of reach.
 *
 * @param shown    the values at which some row is shown to hold the equation
 * @param possible the values at which a row may hold it
 */
public record WhereAnEquationHolds(WholeNumberSet shown, WholeNumberSet possible) {

    public WhereAnEquationHolds {
        if (shown == null || possible == null) {
            throw new IllegalArgumentException("an equation holds somewhere or nowhere");
        }
    }

    /**
     * Where {@code weightHere·s + weightThere·c + constant = 0} holds, or null where a weight is
     * nought and the equation is no relation of the two.
     *
     * @param taken    the values {@code s} is shown to take
     * @param mayTake  the values {@code s} may take: every one it takes is in it
     */
    public static WhereAnEquationHolds of(WholeNumberSet taken, WholeNumberSet mayTake,
                                          BigInteger weightHere, BigInteger weightThere,
                                          BigInteger constant) {
        WholeNumberSet shown = taken.valuesBeside(weightHere, weightThere, constant);
        WholeNumberSet possible = mayTake.valuesBeside(weightHere, weightThere, constant);
        return shown == null || possible == null ? null
                : new WhereAnEquationHolds(shown, possible);
    }

    /** Whether no row holds the equation with the number at {@code value}. */
    public boolean failsAt(BigInteger value) {
        return !possible.holds(value);
    }

    /** Whether a row is shown to hold the equation with the number at {@code value}. */
    public boolean isShownToHoldAt(BigInteger value) {
        return shown.holds(value);
    }
}
