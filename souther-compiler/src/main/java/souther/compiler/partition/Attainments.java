package souther.compiler.partition;

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
 * @param ways         the ways made
 * @param leftUnmade   whether some were not made for want of the figure
 */
record Attainments(List<Attainment> ways, boolean leftUnmade) {

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
}
