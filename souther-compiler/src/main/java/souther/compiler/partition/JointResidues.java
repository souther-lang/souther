package souther.compiler.partition;

import java.util.List;
import java.util.Optional;
import java.util.Set;

/**
 * Whether some statements of remainders by one divisor can be met together by choosing one
 * remainder of the form they share and one of a number they are moved by, and where that number
 * may lie if they are.
 *
 * <p>Each statement holds {@code x + onTheNumber * n + shift} to one of {@code allowed} by
 * {@code divisor}, where {@code x} is the form that every statement is of and a pivot can bring to
 * any remainder, and {@code n} is a whole number the statements are moved by, one that lies from
 * nought up. What matters of both is the remainder each leaves, so the choices are the pairs of
 * remainders, which are as many as the divisor's square: each pair is tried against every
 * statement.
 *
 * <p>The number is taken as small as the pair allows, which is the remainder itself: no
 * non-negative whole number of that remainder is smaller. It is the least {@code n} such a
 * choice can use, so where {@code n} lies up to a bound the choice needs the bound to reach it
 * and no more. Where no pair meets every statement, no whole number does: the statements are met
 * by no row at all.
 */
final class JointResidues {

    private JointResidues() {}

    /** {@code x + onTheNumber * n + shift}, by the divisor, is one of {@code allowed}. */
    record Statement(int shift, int onTheNumber, Set<Integer> allowed) {}

    /**
     * The choice that meets every statement, with the least value of the number that makes it.
     *
     * @param x     the remainder the form leaves
     * @param least the least non-negative number the choice uses
     */
    record Choice(int x, int least) {}

    /**
     * The choice that needs the number no further than any other does, or empty where there is
     * none.
     */
    static Optional<Choice> least(int divisor, List<Statement> statements) {
        Choice best = null;
        for (int y = 0; y < divisor; y++) {
            for (int x = 0; x < divisor; x++) {
                if (meetsEvery(divisor, statements, x, y)
                        && (best == null || y < best.least())) {
                    best = new Choice(x, y);
                }
            }
        }
        return Optional.ofNullable(best);
    }

    private static boolean meetsEvery(int divisor, List<Statement> statements, int x, int n) {
        for (Statement each : statements) {
            int left = Math.floorMod(x + each.onTheNumber() * n + each.shift(), divisor);
            if (!each.allowed().contains(left)) {
                return false;
            }
        }
        return true;
    }
}
