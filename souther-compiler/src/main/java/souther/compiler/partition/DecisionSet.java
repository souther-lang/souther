package souther.compiler.partition;

import java.util.AbstractSet;
import java.util.Arrays;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * The decisions a combination is made of, as a set that works out its hash once and spreads it.
 *
 * <p>A combination is looked up wherever a requirement is met, counted or reported, and each lookup
 * of an ordinary set hashes every decision in it again — and a decision is a deep value, a construct
 * with the calls it was copied through. The set is never changed after it is made, so what it hashes
 * to is worked out when it is made.
 *
 * <p>And spread. An ordinary set hashes to the sum of what its decisions hash to, and the decisions
 * of one comparison visited many times differ only in the visit and in which way it came out: those
 * hash linearly, so every combination with as many held as another sums to the same number and
 * the combinations of one group fall into a few buckets, each told apart by comparing deep values.
 * Each decision's hash is mixed before it is summed, so the order of the decisions still does not
 * matter and the combinations land apart.
 *
 * <p>Held as the array the decisions were given in, which is few, and not as a hashed set: making
 * one of a group's thousands of combinations would otherwise hash every decision of it again, which
 * is the cost this set exists to avoid. Equal to another of its kind holding the same decisions,
 * and to nothing else: a set hashed any other way cannot be equal to this one and keep what a
 * set's hash promises.
 *
 * <p>The decision is written out in full because this package declares a {@code Condition} of its
 * own.
 */
public final class DecisionSet extends AbstractSet<souther.compiler.reading.Condition> {

    private final List<souther.compiler.reading.Condition> decisions;
    private final int hash;

    private DecisionSet(souther.compiler.reading.Condition[] decisions, int hash) {
        this.decisions = List.of(decisions);
        this.hash = hash;
    }

    public static DecisionSet of(Set<souther.compiler.reading.Condition> decisions) {
        if (decisions instanceof DecisionSet already) {
            return already;
        }
        souther.compiler.reading.Condition[] held =
                decisions.toArray(new souther.compiler.reading.Condition[0]);
        int sum = 0;
        for (souther.compiler.reading.Condition each : held) {
            sum += mixed(each.hashCode());
        }
        return new DecisionSet(held, sum);
    }

    /**
     * The distinct decisions of {@code ordered}, hashed from what {@code hashes} already holds of
     * each.
     *
     * <p>The combinations of one group are made of the same few decisions, taken in turn, and a
     * decision is a deep value that costs as much to hash each time. Asked of the one decision
     * once, a group of many choices hashes as many decisions as it has outcomes and not as many as
     * its choices have. And a decision met twice is told from another by that hash first, so two
     * decisions are compared deeply only where they could be one.
     *
     * @param hashes what each decision of the group hashes to, by the decision itself; filled as
     *               decisions are met
     */
    static DecisionSet of(List<souther.compiler.reading.Condition> ordered,
                          Map<souther.compiler.reading.Condition, Integer> hashes) {
        souther.compiler.reading.Condition[] held =
                new souther.compiler.reading.Condition[ordered.size()];
        int[] hashed = new int[held.length];
        int count = 0;
        int sum = 0;
        for (souther.compiler.reading.Condition each : ordered) {
            int h = hashes.computeIfAbsent(each, souther.compiler.reading.Condition::hashCode);
            boolean seen = false;
            for (int i = 0; i < count && !seen; i++) {
                seen = held[i] == each || (hashed[i] == h && held[i].equals(each));
            }
            if (!seen) {
                held[count] = each;
                hashed[count] = h;
                count++;
                sum += mixed(h);
            }
        }
        return new DecisionSet(Arrays.copyOf(held, count), sum);
    }

    /** The finalizer of a 32-bit murmur hash: every bit of the input moves every bit of the output. */
    private static int mixed(int h) {
        int x = h;
        x ^= x >>> 16;
        x *= 0x85ebca6b;
        x ^= x >>> 13;
        x *= 0xc2b2ae35;
        x ^= x >>> 16;
        return x;
    }

    @Override
    public Iterator<souther.compiler.reading.Condition> iterator() {
        return decisions.iterator();
    }

    @Override
    public int size() {
        return decisions.size();
    }

    @Override
    public boolean contains(Object o) {
        for (souther.compiler.reading.Condition each : decisions) {
            if (each == o || each.equals(o)) {
                return true;
            }
        }
        return false;
    }

    @Override
    public int hashCode() {
        return hash;
    }

    /**
     * Whether {@code o} holds the same decisions.
     *
     * <p>Two sets made from one walk hold the very same decisions in the same order, which is told
     * by comparing them as they stand; sets that differ in order or in decision are compared as
     * sets are.
     */
    @Override
    public boolean equals(Object o) {
        if (o == this) {
            return true;
        }
        if (!(o instanceof DecisionSet that) || that.decisions.size() != decisions.size()
                || that.hash != hash) {
            return false;
        }
        boolean alike = true;
        for (int i = 0; alike && i < decisions.size(); i++) {
            alike = decisions.get(i) == that.decisions.get(i);
        }
        if (alike) {
            return true;
        }
        for (souther.compiler.reading.Condition each : decisions) {
            if (!that.contains(each)) {
                return false;
            }
        }
        return true;
    }
}
