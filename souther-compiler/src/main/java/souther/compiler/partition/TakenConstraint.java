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
     * <p>A position of the input and not any number of it. What a bound on an order is about is
     * where a value stands, and a count taken over a run or a form of several is not something an
     * order holds a place for — a term of one of those kinds would be a bound this could spell and
     * nothing could read.
     *
     * <p><b>A bound, so a relation that is not one cannot be spelled here.</b> {@link Rel#NE} holds
     * everywhere but at one place, which is a hole and not an end; this vocabulary says where a run
     * stops. Admitted, it would be a value that says a region was narrowed by something no region
     * can be narrowed by — and every reader of {@link OnTheWay.TakenIn} takes that for the search
     * having been narrowed. So it is refused where it would be built ({@link #of}), and a condition
     * that comes to one is a condition this reading could not turn into a cut.
     *
     * @param term the position this bounds
     * @param at   the place on its order the rule names
     */
    record Ordered(NumericTerm.FromOnePosition term, Place at, Rel rel)
            implements TakenConstraint {

        public Ordered {
            if (term == null || at == null) {
                throw new IllegalArgumentException(
                        "a bound on an order is a position and a place on it: " + term + " " + at);
            }
            if (!isABound(rel)) {
                throw new IllegalArgumentException(
                        "a bound on an order says where a run stops, and " + rel + " does not");
            }
        }

        /** The bound {@code rel} draws at {@code at}, or null where the relation draws none. The
         *  one place that decides it, so that what is built and what a region can be narrowed by
         *  are one answer rather than two that agree until one of them is edited. */
        public static Ordered of(NumericTerm.FromOnePosition term, Place at, Rel rel) {
            return isABound(rel) ? new Ordered(term, at, rel) : null;
        }

        /** Whether {@code rel} says where a run stops. */
        private static boolean isABound(Rel rel) {
            return rel != Rel.NE;
        }

        @Override
        public java.util.Set<NumericTerm> terms() {
            return java.util.Set.of(term);
        }
    }
}
