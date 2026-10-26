package souther.compiler.partition;

import java.util.AbstractSet;
import java.util.Collection;
import java.util.Collections;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

/**
 * The decisions a combination is made of, as a set that works out its hash once and spreads it.
 *
 * <p>A combination is looked up wherever a requirement is met, counted or reported, and each lookup
 * of an ordinary set hashes every decision in it again — and a decision is a deep value, a construct
 * with the calls it was copied through. The set is never changed after it is made, so what it hashes
 * to is worked out the first time it is asked.
 *
 * <p>And spread. An ordinary set hashes to the sum of what its decisions hash to, and the decisions
 * of one comparison visited many times differ only in the visit and in which way it came out: those
 * hash linearly, so every combination with as many held as another sums to the same number and
 * the combinations of one group fall into a few buckets, each told apart by comparing deep values.
 * Each decision's hash is mixed before it is summed, so the order of the decisions still does not
 * matter and the combinations land apart.
 *
 * <p>In the order the decisions were given, so that two walks of one set read it the same way round.
 * Equal to another of its kind holding the same decisions, and to nothing else: a set hashed any
 * other way cannot be equal to this one and keep what a set's hash promises.
 *
 * <p>The decision is written out in full because this package declares a {@code Condition} of its
 * own.
 */
public final class DecisionSet extends AbstractSet<souther.compiler.reading.Condition> {

    private final Set<souther.compiler.reading.Condition> decisions;
    private int hash;
    private boolean hashed;

    private DecisionSet(Collection<souther.compiler.reading.Condition> decisions) {
        this.decisions = Collections.unmodifiableSet(new LinkedHashSet<>(decisions));
    }

    public static DecisionSet of(Set<souther.compiler.reading.Condition> decisions) {
        return decisions instanceof DecisionSet already ? already : new DecisionSet(decisions);
    }

    /**
     * The decisions of {@code decisions}, hashed from what {@code hashes} already holds of each.
     *
     * <p>The combinations of one group are made of the same few decisions, taken in turn, and a
     * decision is a deep value that costs as much to hash each time. Asked of the one decision
     * once, a group of many choices hashes as many decisions as it has outcomes and not as many as
     * its choices have.
     *
     * @param hashes what each decision of the group hashes to, by the decision itself; filled as
     *               decisions are met
     */
    static DecisionSet of(Set<souther.compiler.reading.Condition> decisions,
                          Map<souther.compiler.reading.Condition, Integer> hashes) {
        DecisionSet out = new DecisionSet(decisions);
        int sum = 0;
        for (souther.compiler.reading.Condition each : out.decisions) {
            sum += mixed(hashes.computeIfAbsent(each,
                    souther.compiler.reading.Condition::hashCode));
        }
        out.hash = sum;
        out.hashed = true;
        return out;
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
        return decisions.contains(o);
    }

    @Override
    public int hashCode() {
        if (!hashed) {
            int sum = 0;
            for (souther.compiler.reading.Condition each : decisions) {
                sum += mixed(each.hashCode());
            }
            hash = sum;
            hashed = true;
        }
        return hash;
    }

    /**
     * Whether {@code o} holds the same decisions.
     *
     * <p>Two sets made from one walk hold the very same decisions in the same order, which is told
     * by comparing them as they stand before anything is hashed; sets that differ in order or in
     * decision are compared as sets are.
     */
    @Override
    public boolean equals(Object o) {
        if (o == this) {
            return true;
        }
        if (!(o instanceof DecisionSet that) || that.size() != size()
                || that.hashCode() != hashCode()) {
            return false;
        }
        Iterator<souther.compiler.reading.Condition> mine = decisions.iterator();
        Iterator<souther.compiler.reading.Condition> theirs = that.decisions.iterator();
        boolean alike = true;
        while (alike && mine.hasNext()) {
            alike = mine.next() == theirs.next();
        }
        return alike || decisions.containsAll(that.decisions);
    }
}
