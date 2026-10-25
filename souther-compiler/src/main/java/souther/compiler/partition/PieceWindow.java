package souther.compiler.partition;

import java.util.OptionalLong;

/**
 * Which of the pieces of a split a container holds: those from index {@code from} up to, and not
 * including, {@code until}, or to the last where there is none.
 *
 * <p>What {@code List.take} and {@code List.drop} leave of the pieces, in the order they were
 * applied, and the one place that order is kept: taking and dropping do not commute, since the
 * pieces left of {@code drop(1, take(2, p))} are the second alone and of
 * {@code take(2, drop(1, p))} the second and the third.
 *
 * <p>Counted in {@code long} and saturated, so that no count a program writes makes a window
 * mean something else. A drop past every piece there can be is a window of none, as the run time
 * leaves it, and is not a number that wraps round into a window of some. A window of none is
 * {@link #isEmpty}, and is not the absence of a window: a container of none is a container, and
 * some of none of its pieces is false and every one of them is true.
 *
 * @param from  the index of the first piece held
 * @param until the index the pieces held stop before, or none where they run to the last
 */
record PieceWindow(long from, OptionalLong until) {

    /** Every piece. */
    static final PieceWindow ALL = new PieceWindow(0, OptionalLong.empty());

    PieceWindow {
        if (from < 0 || (until.isPresent() && until.getAsLong() < 0)) {
            throw new IllegalArgumentException("a window starts and stops at an index: "
                    + from + " " + until);
        }
        // Held once whichever way it was written: a window that stops where or before it starts
        // holds nothing, and is the one window of nothing.
        if (until.isPresent() && until.getAsLong() <= from) {
            from = 0;
            until = OptionalLong.of(0);
        }
    }

    /** Whether the window holds no piece, whatever the string. */
    boolean isEmpty() {
        return until.isPresent() && until.getAsLong() == 0;
    }

    /** What is left of this window by {@code List.drop} of {@code count}, which is not negative. */
    PieceWindow dropping(long count) {
        return new PieceWindow(saturatedSum(from, count), until);
    }

    /** What is left of this window by {@code List.take} of {@code count}, which is not negative. */
    PieceWindow taking(long count) {
        long stop = saturatedSum(from, count);
        return new PieceWindow(from, OptionalLong.of(
                until.isPresent() ? Math.min(until.getAsLong(), stop) : stop));
    }

    /** Whether the window starts at the first piece. */
    boolean startsAtTheFirst() {
        return from == 0;
    }

    private static long saturatedSum(long one, long other) {
        long sum = one + other;
        return sum < 0 ? Long.MAX_VALUE : sum;
    }
}
