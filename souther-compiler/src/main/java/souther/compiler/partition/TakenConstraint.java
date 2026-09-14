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
     * stops. What a rule states that way is an {@link AwayFrom}, and the two are held apart because
     * what a reader does with them differs: an end moves where a run starts or stops, and a hole
     * leaves the run where it was and takes one value out of it.
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

        /** Whether {@code rel} says where a run stops. */
        static boolean isABound(Rel rel) {
            return rel != Rel.NE;
        }

        @Override
        public java.util.Set<NumericTerm> terms() {
            return java.util.Set.of(term);
        }
    }

    /**
     * One position held away from one place on its order.
     *
     * <p>What a disequality states. A hole and not an end: the values above it and the values below
     * it are both still there, so nothing about where the run stops has changed and one value has
     * gone out of it. Said as a bound, one whole side of the order would go with it.
     *
     * <p>Its own shape rather than an {@link Ordered} carrying {@link Rel#NE}, because what a
     * reader does with it is the other thing. A run's ends are what a chooser looks between; a hole
     * is what it must not offer, and a row written at one is a row the rules refuse.
     *
     * @param term the position this holds apart
     * @param at   the place on its order no value of the position may be
     */
    record AwayFrom(NumericTerm.FromOnePosition term, Place at) implements TakenConstraint {

        public AwayFrom {
            if (term == null || at == null) {
                throw new IllegalArgumentException(
                        "a hole in an order is a position and a place on it: " + term + " " + at);
            }
        }

        /** {@link Rel#NE}, which is the only relation that states a hole. */
        @Override
        public Rel rel() {
            return Rel.NE;
        }

        @Override
        public java.util.Set<NumericTerm> terms() {
            return java.util.Set.of(term);
        }
    }
}
