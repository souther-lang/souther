package souther.compiler.partition;

import java.util.function.Predicate;

/**
 * Every way of sharing so many elements out among kinds of element that leaves each count asked
 * of how many meet a statement a count that is asked for — and no way that cannot.
 *
 * <p>A kind either meets a statement or does not, so how many elements of a sharing meet it is the
 * sum of what the kinds that do are given. Handing the elements out kind by kind, what the kinds
 * not yet given any can still add is known: nothing where none of them meets the statement, all
 * that is left where all of them do, and anything from none to all otherwise. A hand-out whose
 * least and greatest total leaves no count that is asked for is dropped before the kinds after it
 * are handed anything, so a count that no container of this size can come to is found out at the
 * first kind, and not after the sharings are walked.
 *
 * <p>Where the different values of a place are what is counted, how many meet the statement is
 * only the most that can be different; that count is asked for if some number from one (or none,
 * where none meet it) to that many is.
 *
 * <p>The sharings looked at are counted, every hand-out that was not dropped, whole or part. That
 * is the figure the caller gives; the work between two of them is no more than a count for each
 * number of elements left, so the figure bounds the whole walk.
 */
final class SharingsAmongKinds {

    private final int kinds;
    private final int statements;
    private final boolean[][] meets;
    /** For each statement, how many of the numbers below each are asked for. */
    private final int[][] askedBelow;
    private final int kept;
    private final int figure;
    /** For each kind and from it on, whether some kind meets, and whether some kind does not, the
     *  statement. */
    private final boolean[][] someMeetFrom;
    private final boolean[][] someDoNotFrom;

    private int looked;
    private boolean spent;

    /**
     * @param meets for each kind, for each statement, whether the kind's elements meet it
     * @param asked for each statement, which counts of the elements meeting it are asked for, from
     *              none up to as many as are shared out
     * @param kept  the statement whose different values are counted, or -1
     * @param figure how many hand-outs are looked at before the walk is stopped
     */
    SharingsAmongKinds(boolean[][] meets, boolean[][] asked, int kept, int figure) {
        this.kinds = meets.length;
        this.statements = asked.length;
        this.meets = meets;
        this.kept = kept;
        this.figure = figure;
        this.askedBelow = new int[statements][];
        for (int statement = 0; statement < statements; statement++) {
            askedBelow[statement] = new int[asked[statement].length + 1];
            for (int count = 0; count < asked[statement].length; count++) {
                askedBelow[statement][count + 1] =
                        askedBelow[statement][count] + (asked[statement][count] ? 1 : 0);
            }
        }
        this.someMeetFrom = new boolean[kinds + 1][statements];
        this.someDoNotFrom = new boolean[kinds + 1][statements];
        for (int kind = kinds - 1; kind >= 0; kind--) {
            for (int statement = 0; statement < statements; statement++) {
                someMeetFrom[kind][statement] =
                        someMeetFrom[kind + 1][statement] || meets[kind][statement];
                someDoNotFrom[kind][statement] =
                        someDoNotFrom[kind + 1][statement] || !meets[kind][statement];
            }
        }
    }

    /** How many hand-outs have been looked at, over every size asked. */
    int looked() {
        return looked;
    }

    /** Whether the walk was stopped by the figure. */
    boolean spent() {
        return spent;
    }

    /**
     * Gives {@code each} every sharing of {@code size} elements that is not dropped.
     *
     * @return false where {@code each} said to stop, or the figure stopped the walk
     */
    boolean ofSize(int size, Predicate<int[]> each) {
        if (kinds == 0 || spent) {
            return !spent;
        }
        return fill(0, size, new int[kinds], new int[statements], each);
    }

    private boolean fill(int kind, int left, int[] counts, int[] meeting, Predicate<int[]> each) {
        int[] next = new int[statements];
        // The last kind is given what is left: the sharing has the size asked.
        for (int count = kind == kinds - 1 ? left : 0; count <= left; count++) {
            counts[kind] = count;
            for (int statement = 0; statement < statements; statement++) {
                next[statement] = meeting[statement] + (meets[kind][statement] ? count : 0);
            }
            if (!reachable(kind + 1, left - count, next)) {
                continue;
            }
            if (looked++ == figure) {
                spent = true;
                return false;
            }
            boolean carryOn = kind == kinds - 1 ? each.test(counts)
                    : fill(kind + 1, left - count, counts, next.clone(), each);
            if (!carryOn) {
                return false;
            }
        }
        return true;
    }

    /**
     * Whether kinds from {@code from} on, handed {@code left} elements between them, can bring how
     * many meet each statement to a count that is asked for, given {@code meeting} already do.
     */
    private boolean reachable(int from, int left, int[] meeting) {
        for (int statement = 0; statement < statements; statement++) {
            int least = meeting[statement]
                    + (from < kinds && !someDoNotFrom[from][statement] ? left : 0);
            int most = meeting[statement]
                    + (from < kinds && someMeetFrom[from][statement] ? left : 0);
            // The different values meeting a statement are none where none meet it, and otherwise
            // one to as many as meet it.
            int lowest = statement != kept ? least : least > 0 ? 1 : 0;
            int[] below = askedBelow[statement];
            int top = Math.min(most, below.length - 2);
            if (lowest > top || below[top + 1] - below[lowest] == 0) {
                return false;
            }
        }
        return true;
    }
}
