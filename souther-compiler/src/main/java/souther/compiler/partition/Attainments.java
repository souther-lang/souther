package souther.compiler.partition;

import java.util.ArrayList;
import java.util.List;

/**
 * The ways a row makes a value come to a number ({@link Attainment}), and whether some were left
 * unmade.
 *
 * <p>Two facts are one empty list otherwise: that no rule says how a row makes the value a
 * number, and that a rule does and the figure the search of a site is given did not allow it
 * ({@link StopAssessment}). The first is a value no stop is shown over; the second is a search
 * cut short, which is said as such and not as the first.
 *
 * <p>Made through {@link Builder}, which holds every way made to the one figure there is for
 * them ({@link #MOST}): a way is made by a comparison with each of the others, or a step's every
 * arm, or the product of what two values come to, and a reader that is to look at no more than
 * the figure must not be handed what was built past it.
 *
 * @param ways         the ways made
 * @param leftUnmade   whether some were not made for want of the figure
 */
record Attainments(List<Attainment> ways, boolean leftUnmade) {

    /** How many ways a stop is looked for by at one site, and so the most that are made of a
     *  value: the one figure the search of a site is given. */
    static final int MOST = CompositionBudget.VALUES_A_POSITION_ON_THE_WAY_IS_TRIED_AT.maximum();

    Attainments {
        ways = List.copyOf(ways);
    }

    /** No rule says how a row makes the value a number. */
    static final Attainments NONE = new Attainments(List.of(), false);

    /** A rule does, and what it makes is more than the figure allows. */
    static final Attainments TOO_MANY = new Attainments(List.of(), true);

    /** {@code ways}, all of them made. */
    static Attainments of(List<Attainment> ways) {
        return ways.isEmpty() ? NONE : new Attainments(ways, false);
    }

    boolean isEmpty() {
        return ways.isEmpty();
    }

    /**
     * Ways made one at a time, until there are the figure's worth: the ways beyond it are not
     * made, and what is built says it left some unmade.
     */
    static final class Builder {

        private final List<Attainment> made = new ArrayList<>();
        private boolean leftUnmade;

        /** Whether {@code way} was made: it is where there is room for it, and where there is
         *  none that is left unmade. */
        boolean add(Attainment way) {
            if (made.size() >= MOST) {
                leftUnmade = true;
                return false;
            }
            made.add(way);
            return true;
        }

        /** That {@code of} was made of what had some unmade, which this then has as well. */
        void noting(Attainments of) {
            leftUnmade |= of.leftUnmade();
        }

        /** Whether there is room for another: not once the figure's worth are made. */
        boolean hasRoom() {
            return made.size() < MOST;
        }

        /** What was made, and whether some were not. */
        Attainments build() {
            return new Attainments(made, leftUnmade);
        }
    }
}
