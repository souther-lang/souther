package souther.compiler.semantics;

import souther.compiler.numeric.Rel;

import java.math.BigDecimal;

/**
 * One bound an operation's result has, as the numeric domain holds bounds: the result against a
 * constant, or the result against one argument and a constant.
 *
 * <p>The shape is the domain's and is what a fact may say. A statement of another shape — a result
 * between two arguments, a result no greater than a sum — is one the domain would take in and
 * derive nothing from, so it is not writable here rather than written and silently dropped.
 *
 * <p><b>A bound is where a result stops, so {@link Rel#NE} is not one.</b> Everything else the
 * relations name is an end: an order names one, and an equality names both at once. A result that is
 * anything but one value is two ranges with a hole between them, which is not what this says and not
 * what either reader of it can carry — so it is refused here, where the representation is, and not
 * at the check that holds a fact to the library's signatures. That one asks whether a fact and a
 * declaration agree; this one is about what a bound is.
 *
 * @param against  the argument the result is bounded against, or null where the bound is a constant
 *                 one
 * @param offset   added to that argument, or the constant itself where there is no argument
 * @param rel      how the result stands to it
 * @param provided what has to hold of the arguments for this to be the operation's answer
 */
public record ResultBound(ArgumentRef against, BigDecimal offset, Rel rel, Provided provided) {

    public ResultBound {
        java.util.Objects.requireNonNull(offset, "a bound stands somewhere");
        java.util.Objects.requireNonNull(rel, "and stands some way to it");
        java.util.Objects.requireNonNull(provided, "and under some condition, `Always` if none");
        if (rel == Rel.NE) {
            throw new IllegalArgumentException(
                    "a bound says where a result stops, and `NE` says where it does not stand: "
                            + against + " " + rel + " " + offset);
        }
    }

    /**
     * What has to hold of a call's arguments for the bound beside it to be what the operation
     * answers there.
     *
     * <p>A condition on the arguments and not on the result. An operation whose answer is bounded
     * only for some of the values it takes says so here, rather than being left out of the facts
     * for the values where the bound does not hold.
     *
     * <p>Whether a call meets one is read where calls are read; this says which condition it is.
     */
    public sealed interface Provided {

        /** Nothing: the bound is what the operation does, whatever it is given. */
        record Always() implements Provided {}

        /**
         * An argument that reads as a constant above zero.
         *
         * <p>Constant, and not written as one. What a name was given is what the name is, wherever
         * a value is read, so {@code floorMod(x, k)} under {@code let k = 100} is the same call as
         * {@code floorMod(x, 100)}. Requiring the digits at the call would make a rule an author
         * cannot predict from what the value is, only from where it was written.
         */
        record ConstantAboveZero(ArgumentRef argument) implements Provided {

            public ConstantAboveZero {
                java.util.Objects.requireNonNull(argument, "this one names an argument");
            }
        }
    }
}
