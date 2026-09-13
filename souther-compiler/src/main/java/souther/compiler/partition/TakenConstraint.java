package souther.compiler.partition;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Place;
import souther.compiler.numeric.Rel;

/**
 * What a condition on the way states, in a vocabulary a search can compose a row against.
 *
 * <p><b>Two vocabularies and not one, because a carrier's values are not always numbers.</b> The
 * arithmetic says {@code Σ coef·position rel 0}, and every term of that sum has to count to a number
 * for the sum to mean anything. A string counts to none and is still ordered, so a rule holding one
 * against a written value is a relation this compiler can carry and the arithmetic has nowhere to
 * put. Written as one vocabulary, the second was recorded as a condition nothing could state — and a
 * search below it composed against rules wider than the rows that reach it.
 *
 * <p><b>Not a widening of the first.</b> {@link Place} is where a value sits on its carrier's order
 * and {@link java.math.BigDecimal} is a scalar of the arithmetic; the second is not the general case
 * of the first. A form carrying places would be a sum of things that do not add, so what is held
 * apart here is which question each shape can be asked: an {@link Affine} runs through the numeric
 * algebra, and an {@link Ordered} is a bound on one position's own order.
 */
public sealed interface TakenConstraint {

    /** What the condition states, read the way the path met it. */
    Rel rel();

    /**
     * Which of the input's numbers this is about.
     *
     * <p>Asked of the constraint rather than read off whichever shape it turned out to be. What a
     * composer does with a condition on the way is place a value for every position it names, and
     * that act is the same act in both vocabularies — read off the shapes, it would be written once
     * per shape and a vocabulary added later would be one the composer walks past.
     */
    java.util.Set<NumericTerm> terms();

    /**
     * An inequality over a form of the input's numbers: {@code form rel 0}.
     *
     * <p>The threshold is inside the form as its constant, so a rule and the same rule with the
     * threshold moved across are one value. What this is over is every term the arithmetic could
     * name, however many of them there are.
     */
    record Affine(LinearForm<NumericTerm> form, Rel rel) implements TakenConstraint {

        @Override
        public java.util.Set<NumericTerm> terms() {
            return form.coefs().keySet();
        }
    }

    /**
     * One position held against one written value on the order that position stands on.
     *
     * <p>One term and not a form, because this is the shape a carrier that counts nothing is ever
     * asked in: two strings have no sum, so there is no form over them for a bound to be about. A
     * relation between two such positions is not this — it is a distance, and a distance is the
     * arithmetic's even where the values are not, which is why {@code a < b} over two strings is an
     * {@link Affine} and {@code a < "t"} is this.
     *
     * @param term the position this bounds
     * @param at   the place on its order the rule names
     */
    record Ordered(NumericTerm term, Place at, Rel rel) implements TakenConstraint {

        public Ordered {
            if (term == null || at == null) {
                throw new IllegalArgumentException(
                        "a bound on an order is a position and a place on it: " + term + " " + at);
            }
        }

        @Override
        public java.util.Set<NumericTerm> terms() {
            return java.util.Set.of(term);
        }
    }
}
