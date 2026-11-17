package souther.compiler.partition;

import java.util.List;
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
 * <p>This is the answer to the remainders and to nothing else of a program: that a choice is
 * given says the statements leave a pair of remainders, and not that a row of the program stops at
 * no operation, or meets what else the way states. The number is taken as small as the pair allows,
 * which is the remainder itself: no non-negative whole number of that remainder is smaller. For
 * the remainders alone, some whole numbers meet every statement with the number lying up to a
 * bound exactly where the bound is no less than {@link Choice#least}.
 */
final class JointResidues {

    /** The most remainders of a divisor that every pair is tried of: the search is the square of
     *  the divisor, and a larger one is not started. */
    static final int MOST_DIVISOR = 64;

    private JointResidues() {}

    /** {@code x + onTheNumber * n + shift}, by the divisor, is one of {@code allowed}. */
    record Statement(int shift, int onTheNumber, Set<Integer> allowed) {}

    /** What the statements leave of the remainders. */
    sealed interface Answer {}

    /**
     * A pair of remainders every statement allows.
     *
     * @param x     the remainder the form leaves
     * @param least the least non-negative number the pair uses
     */
    record Choice(int x, int least) implements Answer {}

    /** No pair of remainders is allowed by every statement, so no whole number is. */
    record None() implements Answer {}

    /** The divisor is past what is searched: nothing is said of the statements. That is no answer
     *  that they cannot be met. */
    record NotSearched() implements Answer {}

    /**
     * The pair that needs the number no further than any other does, none where no pair is
     * allowed, and not searched where the divisor is past {@link #MOST_DIVISOR}.
     */
    static Answer least(int divisor, List<Statement> statements) {
        if (divisor < 1 || divisor > MOST_DIVISOR) {
            return new NotSearched();
        }
        for (int y = 0; y < divisor; y++) {
            for (int x = 0; x < divisor; x++) {
                if (meetsEvery(divisor, statements, x, y)) {
                    return new Choice(x, y);
                }
            }
        }
        return new None();
    }

    /**
     * Whether every statement is met at the remainders {@code x} and {@code n}. The sum is worked
     * out in {@code long}: a shift and a weight are any {@code int}, and the product of one with a
     * remainder, up to the most divisor searched, lies far inside a {@code long}.
     */
    private static boolean meetsEvery(int divisor, List<Statement> statements, int x, int n) {
        for (Statement each : statements) {
            long sum = (long) x + (long) each.onTheNumber() * n + each.shift();
            if (!each.allowed().contains((int) Math.floorMod(sum, (long) divisor))) {
                return false;
            }
        }
        return true;
    }
}
