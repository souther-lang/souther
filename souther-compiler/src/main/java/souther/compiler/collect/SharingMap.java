package souther.compiler.collect;

import java.util.Arrays;
import java.util.Objects;

/**
 * Keys each with a value, where putting a value under a key makes another of these and leaves this
 * one as it was, sharing with it every part the put did not reach.
 *
 * <p>For a state carried along a walk that takes several alternatives from one place: each of them
 * puts on the same state, and none reads what another put. A map copied at each put costs the
 * square of the path; this one costs the depth of a trie of the keys' hashes, so a put costs what
 * it adds. Unlike {@link AppendOnly}, a key may be put again, and the new value is the one read
 * from then on.
 *
 * <p>Keys are equal by {@link Object#equals} and hashed by {@link Object#hashCode}, as a
 * {@code HashMap}'s are. Keys whose hashes are equal are kept in one list at the bottom of the
 * trie and told apart there.
 *
 * <p>No equality of its own, and no walk over what it holds: what is asked of one is what is under
 * a key.
 *
 * @param <K> what a value is put under, immutable and equal by what it holds
 * @param <V> what is put, never null
 */
public final class SharingMap<K, V> {

    private static final int BITS = 5;
    private static final int MASK = (1 << BITS) - 1;

    private static final SharingMap<?, ?> EMPTY = new SharingMap<>(new Branch(0, new Node[0]));

    /** A part of the trie, never changed once made. */
    private sealed interface Node permits Entry, Branch, Alike {}

    /** One key put, with its hash. */
    private record Entry(Object key, int hash, Object value) implements Node {}

    /** A level of the trie: a slot for each five bits of hash some key below it has. */
    private static final class Branch implements Node {

        private final int present;
        private final Node[] slots;

        Branch(int present, Node[] slots) {
            this.present = present;
            this.slots = slots;
        }
    }

    /** The keys whose hashes are all {@code hash}. */
    private static final class Alike implements Node {

        private final int hash;
        private final Entry[] entries;

        Alike(int hash, Entry[] entries) {
            this.hash = hash;
            this.entries = entries;
        }
    }

    private final Branch root;

    private SharingMap(Branch root) {
        this.root = root;
    }

    /** Nothing put. */
    @SuppressWarnings("unchecked")
    public static <K, V> SharingMap<K, V> empty() {
        return (SharingMap<K, V>) EMPTY;
    }

    /** What was put under {@code key} last, or null where nothing was. */
    @SuppressWarnings("unchecked")
    public V get(K key) {
        int hash = spread(key.hashCode());
        Node node = root;
        for (int shift = 0; ; shift += BITS) {
            switch (node) {
                case Branch branch -> {
                    int bit = 1 << ((hash >>> shift) & MASK);
                    if ((branch.present & bit) == 0) {
                        return null;
                    }
                    node = branch.slots[Integer.bitCount(branch.present & (bit - 1))];
                }
                case Entry entry -> {
                    return entry.hash() == hash && entry.key().equals(key)
                            ? (V) entry.value() : null;
                }
                case Alike alike -> {
                    if (alike.hash != hash) {
                        return null;
                    }
                    for (Entry each : alike.entries) {
                        if (each.key().equals(key)) {
                            return (V) each.value();
                        }
                    }
                    return null;
                }
            }
        }
    }

    /** These with {@code value} under {@code key}, in place of what was under it. */
    public SharingMap<K, V> with(K key, V value) {
        Objects.requireNonNull(value, "what is put is something");
        Entry entry = new Entry(key, spread(key.hashCode()), value);
        return new SharingMap<>(putInto(root, entry, 0));
    }

    private static Node put(Node node, Entry entry, int shift) {
        return switch (node) {
            case Branch branch -> putInto(branch, entry, shift);
            case Entry there -> there.hash() == entry.hash() && there.key().equals(entry.key())
                    ? entry : joined(there, there.hash(), entry, shift);
            case Alike alike -> alike.hash == entry.hash() ? putInto(alike, entry)
                    : joined(alike, alike.hash, entry, shift);
        };
    }

    private static Branch putInto(Branch branch, Entry entry, int shift) {
        int bit = 1 << ((entry.hash() >>> shift) & MASK);
        int at = Integer.bitCount(branch.present & (bit - 1));
        Node[] slots = branch.slots;
        if ((branch.present & bit) == 0) {
            Node[] wider = new Node[slots.length + 1];
            System.arraycopy(slots, 0, wider, 0, at);
            wider[at] = entry;
            System.arraycopy(slots, at, wider, at + 1, slots.length - at);
            return new Branch(branch.present | bit, wider);
        }
        Node[] replaced = slots.clone();
        replaced[at] = put(slots[at], entry, shift + BITS);
        return new Branch(branch.present, replaced);
    }

    private static Alike putInto(Alike alike, Entry entry) {
        Entry[] entries = alike.entries;
        for (int at = 0; at < entries.length; at++) {
            if (entries[at].key().equals(entry.key())) {
                Entry[] replaced = entries.clone();
                replaced[at] = entry;
                return new Alike(alike.hash, replaced);
            }
        }
        Entry[] wider = Arrays.copyOf(entries, entries.length + 1);
        wider[entries.length] = entry;
        return new Alike(alike.hash, wider);
    }

    /**
     * {@code there}, a node of keys all hashed {@code hash}, and {@code entry}, of a key not among
     * them, under one node at {@code shift}. A single entry of another hash is a node of keys
     * hashed as it is, and two hashes that differ differ in some five bits at or past any shift
     * that has not told them apart yet.
     */
    private static Node joined(Node there, int hash, Entry entry, int shift) {
        if (hash == entry.hash()) {
            return new Alike(hash, new Entry[] {(Entry) there, entry});
        }
        int thereAt = (hash >>> shift) & MASK;
        int entryAt = (entry.hash() >>> shift) & MASK;
        if (thereAt == entryAt) {
            return new Branch(1 << thereAt, new Node[] {joined(there, hash, entry, shift + BITS)});
        }
        Node[] slots = thereAt < entryAt ? new Node[] {there, entry} : new Node[] {entry, there};
        return new Branch((1 << thereAt) | (1 << entryAt), slots);
    }

    /** The hash with its high bits mixed into the low ones, which the first levels read. */
    private static int spread(int hash) {
        return hash ^ (hash >>> 16);
    }
}
