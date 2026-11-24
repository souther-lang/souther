package souther.compiler.meaning;

import java.util.ArrayList;
import java.util.List;
import java.util.Objects;

/**
 * The ways the elements of containers written out are kept, as what decides each element and
 * nothing else: for every element, the truths that keep it in the order they were decided, each
 * with whether the element is kept where it holds or where it does not.
 *
 * <p>A truth is a number here and not the statement it makes. What a truth states is read by
 * whoever holds the ways, and the ways are only which truths decide which elements. That is all a
 * statement over the ways needs to be written out again, so it is held as this and not as a
 * function that writes it.
 *
 * <p>The ways are a tree in which a truth is a node only below the decisions that let an element
 * reach it: an element is kept by truths in the order they were decided, the innermost filter's
 * first, and a later truth is the step of a filter that is handed the element only where the
 * earlier ones kept it. Where an earlier one comes out the other way the later one is not
 * evaluated, it states nothing there, and the tree does not split on it. One truth shared by
 * several elements is one truth, decided once.
 *
 * @param keptBy for each element, the truths that keep it, the innermost filter's first
 * @param truths how many truths there are, numbered from nought
 */
public record KeptWays(List<List<Keep>> keptBy, int truths) {

    /** A truth an element is kept by and whether it keeps the element where it holds. */
    public record Keep(int truth, boolean holds) {}

    public KeptWays {
        keptBy = keptBy.stream().map(List::copyOf).toList();
        for (List<Keep> each : keptBy) {
            for (Keep keep : each) {
                Objects.checkIndex(keep.truth(), truths);
            }
        }
    }

    /** What the ways are made of, which tells these from others. */
    public String spelled() {
        StringBuilder out = new StringBuilder();
        for (int i = 0; i < keptBy.size(); i++) {
            out.append(i).append(':');
            for (Keep keep : keptBy.get(i)) {
                out.append(keep.truth()).append(keep.holds() ? '+' : '-').append(',');
            }
            out.append(';');
        }
        return out.toString();
    }

    /** The decisions of no truth yet. */
    public Boolean[] undecided() {
        return new Boolean[truths];
    }

    /**
     * The first truth some element is handed to and that is not decided yet, given what is
     * decided — or -1 where there is none, and the way is a leaf.
     */
    public int nextEvaluated(Boolean[] decided) {
        int next = -1;
        for (List<Keep> kept : keptBy) {
            for (Keep keep : kept) {
                Boolean decision = decided[keep.truth()];
                if (decision == null) {
                    if (next < 0 || keep.truth() < next) {
                        next = keep.truth();
                    }
                    break;
                }
                if (decision != keep.holds()) {
                    break;
                }
            }
        }
        return next;
    }

    /** Whether element {@code i} is there at a leaf, every truth it is kept by decided as it
     *  was kept. */
    public boolean isThere(int i, Boolean[] decided) {
        for (Keep keep : keptBy.get(i)) {
            if (decided[keep.truth()] != keep.holds()) {
                return false;
            }
        }
        return true;
    }

    /** Those of {@code things}, one for each element from the first, that are there at a leaf. */
    public <T> List<T> thereOf(List<T> things, Boolean[] decided) {
        List<T> there = new ArrayList<>();
        for (int i = 0; i < things.size(); i++) {
            if (isThere(i, decided)) {
                there.add(things.get(i));
            }
        }
        return there;
    }

    /** How many of the {@code count} elements from element {@code from} are there at a leaf. */
    public long countThere(int from, int count, Boolean[] decided) {
        long there = 0;
        for (int i = from; i < from + count; i++) {
            there += isThere(i, decided) ? 1 : 0;
        }
        return there;
    }

    /**
     * How many readings the tree makes in all, or {@code limit} where it makes that many or more.
     *
     * <p>What a leaf reads is the reader's: a sum reads one of each element there, as the sum of
     * the elements of a container that is not kept by anything does, so a leaf is the elements
     * that are there and one for a leaf that has none. A count reads no element, only which are
     * there, so a leaf is one. Counted only to {@code limit}, because what a caller asks is whether
     * the work is within a budget, and a tree of independent truths has as many leaves as there
     * are combinations of them. The truths {@code decided} already are not split again.
     *
     * @param readsTheElements whether a leaf reads each element that is there
     */
    public long work(Boolean[] decided, long limit, boolean readsTheElements) {
        int next = nextEvaluated(decided);
        if (next < 0) {
            long there = 0;
            for (int i = 0; readsTheElements && i < keptBy.size(); i++) {
                there += isThere(i, decided) ? 1 : 0;
            }
            return Math.min(limit, Math.max(1, there));
        }
        long total = 0;
        for (boolean holds : new boolean[] {true, false}) {
            decided[next] = holds;
            total += work(decided, limit - total, readsTheElements);
            decided[next] = null;
            if (total >= limit) {
                return limit;
            }
        }
        return total;
    }

    /** What is made of each way, given what a truth makes of the two ways it splits into. */
    public interface Making<R> {

        /** A way split on {@code truth}: what is made of the way where it holds and where it
         *  does not. */
        R split(int truth, R where, R otherwise);

        /** A way that is a leaf, every truth that decides an element decided. */
        R leaf(Boolean[] decided);
    }

    /**
     * Every way, made as {@code making} says: the tree walked from the truths {@code decided}
     * down to its leaves.
     */
    public <R> R made(Making<R> making, Boolean[] decided) {
        int next = nextEvaluated(decided);
        if (next < 0) {
            return making.leaf(decided);
        }
        decided[next] = true;
        R where;
        R otherwise;
        try {
            where = made(making, decided);
            decided[next] = false;
            otherwise = made(making, decided);
        } finally {
            decided[next] = null;
        }
        return making.split(next, where, otherwise);
    }
}
