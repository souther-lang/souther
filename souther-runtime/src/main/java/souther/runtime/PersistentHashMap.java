package souther.runtime;

import org.jspecify.annotations.Nullable;

import java.util.AbstractMap;
import java.util.AbstractSet;
import java.util.ArrayDeque;
import java.util.Arrays;
import java.util.Deque;
import java.util.Iterator;
import java.util.Map;
import java.util.NoSuchElementException;
import java.util.Objects;
import java.util.Set;

/**
 * An immutable hash map backed by a CHAMP trie (Compressed Hash-Array Mapped Prefix-tree). Each
 * node packs its inline key/value pairs and its sub-nodes into a single array addressed by two
 * bitmaps (a 5-bit hash chunk per level), so {@code get}/{@code put}/{@code remove} are O(log32 n)
 * and each new version shares all untouched structure with the previous one — which is what makes
 * a {@code groupBy} that grows a map O(n log n) instead of the O(n²) a whole-map copy would cost.
 *
 * <p>It implements {@link java.util.Map} so it flows through codegen and the boundary unchanged.
 * Extending {@link AbstractMap} supplies the immutable, mutator-throwing defaults.
 *
 * <p>Which key a lookup finds is the language's question. Keys and values are compared and hashed
 * through {@link Values}, so a Decimal key is found by the amount it is rather than by the scale it
 * arrived with, and the trie is indexed by that hash — there is one index, not two, so {@code get}
 * cannot also answer the JDK's question. {@code equals} and {@code hashCode} follow the same rule
 * rather than being inherited, because a map whose {@code get} is the language's and whose hash was
 * the JDK's would call two maps equal and hash them apart.
 *
 * <p>The cost is stated rather than hidden: against a foreign {@code java.util.Map} holding the same
 * amount at another scale, {@code equals} is not symmetric. Only Java interop can construct that
 * pair. A {@link PersistentVector} keeps the {@code List} contract instead, because a list compares
 * positionally and has no index to be indexed by.
 *
 * <p>Iteration order is a deterministic, implementation-defined hash order (not insertion order):
 * the same set of keys always yields the same order, so boundary encoding stays reproducible.
 *
 * <p>Values are never null (a Souther collection models absence with {@code Option}), so
 * {@link #get} returning {@code null} unambiguously means "absent".
 *
 * <p>{@code remove} keeps the trie canonical: an emptied sub-node is dropped and a sub-node that
 * collapses to a single entry is inlined back into its parent (bubbling up a level when the parent
 * would otherwise become a lone-entry inner node). So a key set reached by deletions has the same
 * shape — and the same deterministic iteration order — as one built directly.
 */
public final class PersistentHashMap<K, V> extends AbstractMap<K, V> implements ValueSemantics {

    private static final int BITS = 5;
    private static final int MASK = (1 << BITS) - 1;   // 31
    private static final Object NOT_FOUND = new Object();

    public static final PersistentHashMap<?, ?> EMPTY =
            new PersistentHashMap<>(BitmapIndexedNode.EMPTY, 0);

    private final Node root;
    private final int size;

    private PersistentHashMap(Node root, int size) {
        this.root = root;
        this.size = size;
    }

    @SuppressWarnings("unchecked")
    public static <K, V> PersistentHashMap<K, V> empty() {
        return (PersistentHashMap<K, V>) EMPTY;
    }

    /** Wraps {@code m} as a PersistentHashMap, sharing when it already is one, else building it in
     *  one pass through {@link Builder} (later entries win). */
    @SuppressWarnings("unchecked")
    public static <K, V> PersistentHashMap<K, V> from(Map<? extends K, ? extends V> m) {
        if (m instanceof PersistentHashMap<?, ?> phm) {
            return (PersistentHashMap<K, V>) phm;
        }
        Builder<K, V> b = new Builder<>();
        for (Map.Entry<? extends K, ? extends V> e : m.entrySet()) {
            b.set(e.getKey(), e.getValue());
        }
        return b.build();
    }

    /** Spreads the key's hash so that low-order bits (the first chunk consumed) carry entropy. */
    private static int spread(int h) {
        return h ^ (h >>> 16);
    }

    /**
     * The trie index for {@code key}: {@link Values#hash}, spread.
     *
     * <p>The carriers that answer for themselves are taken here rather than inside {@code Values} so
     * that their {@code hashCode} is called from this site. Routed through the shared function, that
     * one call would see every key type in the program and go megamorphic; called here it sees the
     * key type of the map being walked. Which carriers those are is still {@code Values}'s to say —
     * only the call is moved, not the rule.
     */
    private static int hashOf(@Nullable Object key) {
        if (key == null) {
            return 0;
        }
        if (Values.answersForItself(key.getClass())) {
            return spread(key.hashCode());
        }
        return spread(Values.hash(key));
    }

    @Override
    public int size() {
        return size;
    }

    /** {@code null} for an absent key, as {@link Map#get} says. The {@code "null"} suppression is for
     *  {@link AbstractMap}, which carries no nullness annotations: against an unannotated {@code V}
     *  a nullable return reads as narrowing the inherited one. */
    @Override
    @SuppressWarnings({"unchecked", "null"})
    public @Nullable V get(@Nullable Object key) {
        Object r = root.find(key, hashOf(key), 0);
        return r == NOT_FOUND ? null : (V) r;
    }

    @Override
    public boolean containsKey(@Nullable Object key) {
        return root.find(key, hashOf(key), 0) != NOT_FOUND;
    }

    @Override
    public boolean equals(@Nullable Object o) {
        return valueEquals(o);
    }

    @Override
    public int hashCode() {
        return valueHash();
    }

    /**
     * Whether {@code o} is the same map the language means: the same keys, each mapped to the same
     * value. Both questions are asked of {@link Values}, so an amount is the amount it is at either
     * scale, on the key side and on the value side.
     *
     * <p>The other map is taken through {@link #from} first, because a foreign map is keyed by
     * Java's equality, which is finer than the language's: a map holding 1.0 and 1.00 has two
     * entries and the language sees one key. Counted as it stands, both would find the same entry
     * here and nothing would notice the key this map has that it does not. Where such a map maps its
     * duplicate keys to different values, {@code from} keeps the later one in iteration order, and
     * that is the value the comparison sees — the language cannot hold both, and which of them a
     * foreign map meant is not a question the boundary can answer.
     */
    @Override
    public boolean valueEquals(Object o) {
        if (o == this) {
            return true;
        }
        if (!(o instanceof Map<?, ?> m)) {
            return false;
        }
        PersistentHashMap<?, ?> other = PersistentHashMap.from(m);
        if (other.size() != size) {
            return false;
        }
        for (Map.Entry<?, ?> e : other.entrySet()) {
            // asked as two questions rather than reading an absent key off a null answer: a map
            // Souther built never stores one, but `from` will build a map from a foreign map that
            // does, and "not here" and "here, holding nothing" are not the same answer
            if (!containsKey(e.getKey()) || !Values.equal(get(e.getKey()), e.getValue())) {
                return false;
            }
        }
        return true;
    }

    /** Summed over the entries, so it does not depend on the order they are walked in — two maps
     *  built by different routes hold the same entries in different places. */
    @Override
    public int valueHash() {
        int h = 0;
        for (Map.Entry<K, V> e : entrySet()) {
            h += Values.hash(e.getKey()) ^ Values.hash(e.getValue());
        }
        return h;
    }

    /** This map with {@code key} mapped to {@code val} (added, or overwriting an equal-keyed entry).
     *  Named {@code assoc} rather than {@code put} because {@link java.util.Map#put} is the mutating
     *  operation and returns the old value — this returns a new map. */
    public PersistentHashMap<K, V> assoc(K key, V val) {
        Box added = new Box();
        Node newRoot = root.put(key, hashOf(key), val, 0, added, false);
        if (newRoot == root) {
            return this;   // key present with an equal value: unchanged
        }
        return new PersistentHashMap<>(newRoot, added.value ? size + 1 : size);
    }

    /** This map without {@code key}; {@code this} when the key is absent. A removal always returns a
     *  new node and a no-op returns the same node, so reference identity alone tells us whether the
     *  size dropped — no separate "was it removed" flag is threaded through. */
    public PersistentHashMap<K, V> without(K key) {
        Node newRoot = root.remove(key, hashOf(key), 0);
        if (newRoot == root) {
            return this;
        }
        return new PersistentHashMap<>(newRoot, size - 1);
    }

    @Override
    public Set<Map.Entry<K, V>> entrySet() {
        return new AbstractSet<>() {
            @Override
            public int size() {
                return size;
            }

            @Override
            @SuppressWarnings("unchecked")
            public Iterator<Map.Entry<K, V>> iterator() {
                return (Iterator<Map.Entry<K, V>>) (Iterator<?>) new EntryIterator(root, size);
            }
        };
    }

    // --- nodes ---

    /** A mutable one-bit flag {@code put} sets to report whether it added a new key (versus replacing
     *  an existing key's value), so the map's size is adjusted correctly. {@code remove} needs no such
     *  flag: it decides by reference identity (see {@link #without}). */
    private static final class Box {
        boolean value;
    }

    /**
     * Where a value is held, so that reading a key and then writing it descends the trie once rather
     * than twice — what {@code Map.upsert} does on every element of a fold that counts. A
     * {@link Builder} owns one and hands it to {@link Node#probe}, so the sharing costs no allocation.
     *
     * <p>It is only ever read straight after the descent that filled it, and only by the builder that
     * owns the nodes it points into: a write that does anything other than overwrite that very slot
     * gives up the probe first, so it can never name an array the trie has replaced.
     */
    private static final class Probe {
        @Nullable Object key;
        @Nullable Object @Nullable [] holder;
        int index;
    }

    private interface Node {
        Object find(@Nullable Object key, int keyHash, int shift);

        /** Reports into {@code probe} where {@code key}'s value is held inline under this node, and
         *  answers whether it is held at all. A key in a collision bucket is not reported: the bucket
         *  is the rare case and has nothing to gain. */
        boolean probe(@Nullable Object key, int keyHash, int shift, Probe probe);

        /**
         * This node with {@code key} mapped to {@code val}.
         *
         * <p>{@code owned} says the caller is a {@link Builder} and every node under it is one the
         * builder created, so a slot may be written in place instead of the node being cloned; the
         * node is then returned unchanged and the parent has nothing to rewrite either. What is left
         * to allocate is only what changes an array's length or a bitmap: adding a key to a node, and
         * splitting an inline pair into a sub-node when two keys collide at that level. Overwriting
         * an existing key's value allocates nothing at all.
         *
         * <p>An ordinary persistent put passes {@code false} and clones every node on the path, as it
         * must.
         */
        Node put(Object key, int keyHash, Object val, int shift, Box addedLeaf, boolean owned);

        Node remove(Object key, int keyHash, int shift);

        int payloadArity();

        Object keyAt(int i);

        Object valAt(int i);

        int nodeArity();

        Node nodeAt(int i);
    }

    /** Builds a node holding exactly two entries with distinct keys, descending until their hash
     *  chunks differ (or bottoming out in a {@link HashCollisionNode} when the full hashes match). */
    private static Node mergeTwoPairs(Object k0, int h0, Object v0,
                                      Object k1, int h1, Object v1, int shift) {
        if (h0 == h1) {
            return new HashCollisionNode(h0, new Object[]{k0, v0, k1, v1});
        }
        int mask0 = (h0 >>> shift) & MASK;
        int mask1 = (h1 >>> shift) & MASK;
        if (mask0 != mask1) {
            int dataMap = (1 << mask0) | (1 << mask1);
            Object[] contents = mask0 < mask1
                    ? new Object[]{k0, v0, k1, v1}
                    : new Object[]{k1, v1, k0, v0};
            return new BitmapIndexedNode(dataMap, 0, contents);
        }
        Node sub = mergeTwoPairs(k0, h0, v0, k1, h1, v1, shift + BITS);
        return new BitmapIndexedNode(0, 1 << mask0, new Object[]{sub});
    }

    /**
     * A CHAMP node. {@code contents} holds {@code payloadArity} inline {@code [key, value]} pairs at
     * the front, then {@code nodeArity} sub-nodes in forward order at the tail. {@code dataMap} marks
     * the hash-chunk bits with an inline pair, {@code nodeMap} the bits with a sub-node.
     */
    private static final class BitmapIndexedNode implements Node {
        static final BitmapIndexedNode EMPTY = new BitmapIndexedNode(0, 0, new Object[0]);

        final int dataMap;
        final int nodeMap;
        final Object[] contents;

        BitmapIndexedNode(int dataMap, int nodeMap, Object[] contents) {
            this.dataMap = dataMap;
            this.nodeMap = nodeMap;
            this.contents = contents;
        }

        private int dataIndex(int bitpos) {
            return Integer.bitCount(dataMap & (bitpos - 1));
        }

        private int nodeIndex(int bitpos) {
            return Integer.bitCount(nodeMap & (bitpos - 1));
        }

        @Override
        public int payloadArity() {
            return Integer.bitCount(dataMap);
        }

        @Override
        public int nodeArity() {
            return Integer.bitCount(nodeMap);
        }

        @Override
        public Object keyAt(int i) {
            return contents[2 * i];
        }

        @Override
        public Object valAt(int i) {
            return contents[2 * i + 1];
        }

        @Override
        public Node nodeAt(int i) {
            return (Node) contents[2 * payloadArity() + i];
        }

        @Override
        public Object find(@Nullable Object key, int keyHash, int shift) {
            int bitpos = 1 << ((keyHash >>> shift) & MASK);
            if ((dataMap & bitpos) != 0) {
                int i = dataIndex(bitpos);
                return Values.equal(keyAt(i), key) ? valAt(i) : NOT_FOUND;
            }
            if ((nodeMap & bitpos) != 0) {
                return nodeAt(nodeIndex(bitpos)).find(key, keyHash, shift + BITS);
            }
            return NOT_FOUND;
        }

        @Override
        public boolean probe(@Nullable Object key, int keyHash, int shift, Probe probe) {
            int bitpos = 1 << ((keyHash >>> shift) & MASK);
            if ((dataMap & bitpos) != 0) {
                int i = dataIndex(bitpos);
                if (!Values.equal(keyAt(i), key)) {
                    return false;
                }
                probe.holder = contents;
                probe.index = 2 * i + 1;
                return true;
            }
            if ((nodeMap & bitpos) != 0) {
                return nodeAt(nodeIndex(bitpos)).probe(key, keyHash, shift + BITS, probe);
            }
            return false;
        }

        @Override
        public Node put(Object key, int keyHash, Object val, int shift, Box addedLeaf, boolean owned) {
            int bitpos = 1 << ((keyHash >>> shift) & MASK);
            if ((dataMap & bitpos) != 0) {
                int i = dataIndex(bitpos);
                Object currentKey = keyAt(i);
                if (Values.equal(currentKey, key)) {
                    if (Values.equal(valAt(i), val)) {
                        return this;
                    }
                    return copyAndSetValue(bitpos, val, owned);
                }
                Node sub = mergeTwoPairs(currentKey, hashOf(currentKey), valAt(i),
                        key, keyHash, val, shift + BITS);
                addedLeaf.value = true;
                return copyAndMigrateInlineToNode(bitpos, sub);
            }
            if ((nodeMap & bitpos) != 0) {
                int i = nodeIndex(bitpos);
                Node sub = nodeAt(i);
                Node newSub = sub.put(key, keyHash, val, shift + BITS, addedLeaf, owned);
                return newSub == sub ? this : copyAndSetNode(bitpos, newSub, owned);
            }
            addedLeaf.value = true;
            return copyAndInsertValue(bitpos, key, val);
        }

        @Override
        public Node remove(Object key, int keyHash, int shift) {
            int bitpos = 1 << ((keyHash >>> shift) & MASK);
            if ((dataMap & bitpos) != 0) {
                int i = dataIndex(bitpos);
                if (Values.equal(keyAt(i), key)) {
                    return copyAndRemoveValue(bitpos);
                }
                return this;
            }
            if ((nodeMap & bitpos) != 0) {
                int i = nodeIndex(bitpos);
                Node sub = nodeAt(i);
                Node newSub = sub.remove(key, keyHash, shift + BITS);
                if (newSub == sub) {
                    return this;
                }
                switch (sizePredicate(newSub)) {
                    case 0:
                        return copyAndRemoveNode(bitpos);
                    case 1:
                        // The sub-node collapsed to a single entry: inline it here so the trie stays
                        // canonical (a HashCollisionNode that dropped to one pair, or a sub-node whose
                        // sole surviving key belongs one level up). When this node is itself just that
                        // one sub-node, bubble the entry up instead so this node does not become a
                        // non-canonical lone-entry inner node — re-keyed to this level's bit, since the
                        // surviving key shares the removed key's chunk here and only diverged deeper.
                        if (payloadArity() == 0 && nodeArity() == 1) {
                            return new BitmapIndexedNode(bitpos, 0,
                                    new Object[]{newSub.keyAt(0), newSub.valAt(0)});
                        }
                        return copyAndMigrateNodeToInline(bitpos, newSub);
                    default:
                        return copyAndSetNode(bitpos, newSub, false);
                }
            }
            return this;
        }

        /** 0 for empty, 1 for a single inline entry (a candidate to inline into the parent), 2 for
         *  anything larger. */
        private static int sizePredicate(Node n) {
            if (n.payloadArity() == 0 && n.nodeArity() == 0) {
                return 0;
            }
            if (n.nodeArity() == 0 && n.payloadArity() == 1) {
                return 1;
            }
            return 2;
        }

        /** Neither bitmap moves, so an owned node writes the slot and is still itself — which is what
         *  lets the whole path above an insert allocate nothing. */
        private BitmapIndexedNode copyAndSetValue(int bitpos, Object val, boolean owned) {
            if (owned) {
                contents[2 * dataIndex(bitpos) + 1] = val;
                return this;
            }
            Object[] c = contents.clone();
            c[2 * dataIndex(bitpos) + 1] = val;
            return new BitmapIndexedNode(dataMap, nodeMap, c);
        }

        private BitmapIndexedNode copyAndSetNode(int bitpos, Node node, boolean owned) {
            if (owned) {
                contents[2 * payloadArity() + nodeIndex(bitpos)] = node;
                return this;
            }
            Object[] c = contents.clone();
            c[2 * payloadArity() + nodeIndex(bitpos)] = node;
            return new BitmapIndexedNode(dataMap, nodeMap, c);
        }

        /** The array grows and {@code dataMap} gains a bit, so this one allocates even when owned —
         *  once per key the builder actually adds, and not at all when it overwrites one. */
        private BitmapIndexedNode copyAndInsertValue(int bitpos, Object key, Object val) {
            int idx = 2 * dataIndex(bitpos);
            Object[] c = new Object[contents.length + 2];
            System.arraycopy(contents, 0, c, 0, idx);
            c[idx] = key;
            c[idx + 1] = val;
            System.arraycopy(contents, idx, c, idx + 2, contents.length - idx);
            return new BitmapIndexedNode(dataMap | bitpos, nodeMap, c);
        }

        private BitmapIndexedNode copyAndRemoveValue(int bitpos) {
            int idx = 2 * dataIndex(bitpos);
            Object[] c = new Object[contents.length - 2];
            System.arraycopy(contents, 0, c, 0, idx);
            System.arraycopy(contents, idx + 2, c, idx, contents.length - idx - 2);
            return new BitmapIndexedNode(dataMap ^ bitpos, nodeMap, c);
        }

        private BitmapIndexedNode copyAndRemoveNode(int bitpos) {
            int idx = 2 * payloadArity() + nodeIndex(bitpos);
            Object[] c = new Object[contents.length - 1];
            System.arraycopy(contents, 0, c, 0, idx);
            System.arraycopy(contents, idx + 1, c, idx, contents.length - idx - 1);
            return new BitmapIndexedNode(dataMap, nodeMap ^ bitpos, c);
        }

        /** Removes the inline pair at {@code bitpos} and inserts {@code node} at that bit in the node
         *  section (data shrinks by a pair, nodes grow by one). */
        private BitmapIndexedNode copyAndMigrateInlineToNode(int bitpos, Node node) {
            int p = payloadArity();
            int n = nodeArity();
            int d = dataIndex(bitpos);
            int ni = nodeIndex(bitpos);
            Object[] c = new Object[contents.length - 1];   // -2 data, +1 node
            System.arraycopy(contents, 0, c, 0, 2 * d);                       // data before the pair
            System.arraycopy(contents, 2 * d + 2, c, 2 * d, 2 * (p - 1) - 2 * d);  // data after the pair
            int nodeBase = 2 * (p - 1);
            System.arraycopy(contents, 2 * p, c, nodeBase, ni);              // nodes before ni
            c[nodeBase + ni] = node;
            System.arraycopy(contents, 2 * p + ni, c, nodeBase + ni + 1, n - ni);  // nodes from ni
            return new BitmapIndexedNode(dataMap ^ bitpos, nodeMap | bitpos, c);
        }

        /** Inlines {@code node}'s single entry at {@code bitpos} and drops it from the node section
         *  (data grows by a pair, nodes shrink by one) — the inverse of {@link
         *  #copyAndMigrateInlineToNode}, restoring canonical form after a removal. */
        private BitmapIndexedNode copyAndMigrateNodeToInline(int bitpos, Node node) {
            int p = payloadArity();
            int n = nodeArity();
            int d = dataIndex(bitpos);
            int ni = nodeIndex(bitpos);
            Object[] c = new Object[contents.length + 1];   // +2 data, -1 node
            System.arraycopy(contents, 0, c, 0, 2 * d);                       // data before the pair
            c[2 * d] = node.keyAt(0);
            c[2 * d + 1] = node.valAt(0);
            System.arraycopy(contents, 2 * d, c, 2 * d + 2, 2 * (p - d));      // data after the pair
            int nodeBase = 2 * (p + 1);
            System.arraycopy(contents, 2 * p, c, nodeBase, ni);              // nodes before ni
            System.arraycopy(contents, 2 * p + ni + 1, c, nodeBase + ni, n - ni - 1);  // nodes after ni
            return new BitmapIndexedNode(dataMap | bitpos, nodeMap ^ bitpos, c);
        }
    }

    /** A bucket of entries whose full hashes collide (distinct keys, same {@code hash}). */
    private static final class HashCollisionNode implements Node {
        final int hash;
        final Object[] pairs;   // [k0,v0,k1,v1,...], length >= 4

        HashCollisionNode(int hash, Object[] pairs) {
            this.hash = hash;
            this.pairs = pairs;
        }

        @Override
        public Object find(@Nullable Object key, int keyHash, int shift) {
            if (keyHash != hash) {
                return NOT_FOUND;
            }
            for (int i = 0; i < pairs.length; i += 2) {
                if (Values.equal(pairs[i], key)) {
                    return pairs[i + 1];
                }
            }
            return NOT_FOUND;
        }

        @Override
        public boolean probe(@Nullable Object key, int keyHash, int shift, Probe probe) {
            return false;   // a bucket of colliding keys: rare, and the walk down it is the cost
        }

        @Override
        public Node put(Object key, int keyHash, Object val, int shift, Box addedLeaf, boolean owned) {
            if (keyHash != hash) {
                // A key that reaches this node with a different hash: wrap the bucket in a bitmap node
                // at this level, then insert into that.
                Node wrapper = new BitmapIndexedNode(0, 1 << ((hash >>> shift) & MASK),
                        new Object[]{this});
                return wrapper.put(key, keyHash, val, shift, addedLeaf, owned);
            }
            for (int i = 0; i < pairs.length; i += 2) {
                if (Values.equal(pairs[i], key)) {
                    if (Values.equal(pairs[i + 1], val)) {
                        return this;
                    }
                    Object[] p = pairs.clone();
                    p[i + 1] = val;
                    return new HashCollisionNode(hash, p);
                }
            }
            addedLeaf.value = true;
            Object[] p = Arrays.copyOf(pairs, pairs.length + 2);
            p[pairs.length] = key;
            p[pairs.length + 1] = val;
            return new HashCollisionNode(hash, p);
        }

        @Override
        public Node remove(Object key, int keyHash, int shift) {
            if (keyHash != hash) {
                return this;
            }
            for (int i = 0; i < pairs.length; i += 2) {
                if (Values.equal(pairs[i], key)) {
                    if (pairs.length == 4) {
                        int other = i == 0 ? 2 : 0;
                        // Fall back to a one-entry bitmap node at this level for the surviving key.
                        return new BitmapIndexedNode(1 << ((hash >>> shift) & MASK), 0,
                                new Object[]{pairs[other], pairs[other + 1]});
                    }
                    Object[] p = new Object[pairs.length - 2];
                    System.arraycopy(pairs, 0, p, 0, i);
                    System.arraycopy(pairs, i + 2, p, i, pairs.length - i - 2);
                    return new HashCollisionNode(hash, p);
                }
            }
            return this;
        }

        @Override
        public int payloadArity() {
            return pairs.length / 2;
        }

        @Override
        public Object keyAt(int i) {
            return pairs[2 * i];
        }

        @Override
        public Object valAt(int i) {
            return pairs[2 * i + 1];
        }

        @Override
        public int nodeArity() {
            return 0;
        }

        @Override
        public Node nodeAt(int i) {
            throw new IndexOutOfBoundsException();
        }
    }

    /** Depth-first iterator over the trie: emits a node's inline pairs, then descends its sub-nodes.
     *  Deterministic (bitmap order), O(1) amortized per entry. */
    private static final class EntryIterator implements Iterator<Map.Entry<Object, Object>> {
        private final Deque<Node> stack = new ArrayDeque<>();
        private @Nullable Node payloadNode;
        private int payloadIndex;

        EntryIterator(Node root, int size) {
            if (size > 0) {
                stack.push(root);
            }
            advance();
        }

        private void advance() {
            payloadNode = null;
            while (!stack.isEmpty()) {
                Node n = stack.pop();
                for (int i = n.nodeArity() - 1; i >= 0; i--) {
                    stack.push(n.nodeAt(i));
                }
                if (n.payloadArity() > 0) {
                    payloadNode = n;
                    payloadIndex = 0;
                    return;
                }
            }
        }

        @Override
        public boolean hasNext() {
            return payloadNode != null;
        }

        @Override
        public Map.Entry<Object, Object> next() {
            Node node = payloadNode;
            if (node == null) {
                throw new NoSuchElementException();
            }
            Object k = node.keyAt(payloadIndex);
            Object v = node.valAt(payloadIndex);
            payloadIndex++;
            if (payloadIndex >= node.payloadArity()) {
                advance();
            }
            return new SimpleImmutableEntry<>(k, v);
        }
    }

    /**
     * A single-use, from-empty bulk builder for the runtime's own bulk operations — {@link #from},
     * {@code Maps.fromList}/{@code mapKeys}, and the {@code PersistentHashSet} set algebra. Every
     * node it reaches it created itself, and the trie under construction never leaves the method
     * that is building it, so writing an element of a node's array in place cannot be observed by
     * anything: no other version shares those nodes.
     *
     * <p>That is what {@code assoc} cannot do. An insert rewrites the bitmaps an older version reads
     * to interpret the same array, so a persistent put has to clone every node on the path — there is
     * no region of a CHAMP node that older versions do not look at, which is why the vector's claimed
     * tail has no counterpart here (ADR-0060).
     *
     * <p>A fold may thread one through all the same, and {@code Maps.build} does: what the confinement
     * asks for is that no version before the last is read, and the compiler establishes exactly that
     * before it hands the walk a builder (the compiler's {@code GrowingFold}). It is a
     * {@link java.util.Map} of what it has been given so far, so a step that reads the accumulator it
     * is growing — which is what {@code Map.upsert} does — reads it as any map.
     *
     * <p>Ownership needs no mark on the node. Starting from the shared {@link
     * BitmapIndexedNode#EMPTY} and only ever inserting, every node the builder can reach below the
     * root is one it built: nothing here adopts a node from elsewhere. {@code EMPTY} itself is the
     * one node it does not own, and it is never written — a write needs an entry or a child to
     * replace, and {@code EMPTY} has neither, so the first insert allocates as it would anyway.
     * Once {@link #build} hands the trie over, every later write comes through {@code assoc}, which
     * passes {@code owned = false}.
     *
     * <p>Marking each node instead would cost a reference on every node in every map, which measured
     * as a 6% regression on the persistent {@code assoc} path — the common one — to speed up this
     * one. A flag threaded down the call is free.
     */
    static final class Builder<K, V> extends AbstractMap<K, V> {
        private final Box added = new Box();
        private final Probe probe = new Probe();
        private Node root = BitmapIndexedNode.EMPTY;
        private int size;
        /** Whether {@link #build} has handed the trie over. A builder is single-use: the map it built
         *  shares the nodes it filled, so a later write would reach into a value that is supposed to be
         *  immutable. Refusing here is what keeps that from being possible rather than merely unlikely
         *  — the compiler's own analysis is what stops a walk from keeping its builder, and a guarantee
         *  about a value should not rest on an analysis somewhere else. */
        private boolean built;

        /**
         * Sets {@code key} to {@code val}, saying nothing about what was there before — bulk
         * construction has no use for the old value and would pay a second lookup for it.
         *
         * <p>A key just read is written where it was found: {@code Map.upsert} reads the key and then
         * writes it, and the descent the read made is still good for the write. Anything else gives up
         * the probe and descends, which is also what keeps the probe from ever naming a slot that has
         * moved — only this method moves one.
         */
        void set(K key, V val) {
            if (built) {
                throw new IllegalStateException("this builder has already been built");
            }
            @Nullable Object @Nullable [] held = probe.holder;
            if (held != null && Values.equal(probe.key, key)) {
                held[probe.index] = val;
                probe.holder = null;
                probe.key = null;
                return;
            }
            probe.holder = null;
            probe.key = null;
            added.value = false;
            root = root.put(key, hashOf(key), val, 0, added, true);
            if (added.value) {
                size++;
            }
        }

        @Override
        @SuppressWarnings("null")
        public @Nullable V put(K key, V val) {
            @Nullable V old = get(key);
            set(key, val);
            return old;
        }

        @Override
        public int size() {
            return size;
        }

        /** The value at {@code key}, remembering where it was found so that writing the same key back
         *  — which is what an {@code upsert} does next — need not descend again. */
        @Override
        @SuppressWarnings({"unchecked", "null"})
        public @Nullable V get(@Nullable Object key) {
            if (root.probe(key, hashOf(key), 0, probe)) {
                probe.key = key;
                return (V) Objects.requireNonNull(probe.holder)[probe.index];
            }
            probe.holder = null;
            probe.key = null;
            return null;
        }

        @Override
        public boolean containsKey(@Nullable Object key) {
            return root.find(key, hashOf(key), 0) != NOT_FOUND;
        }

        @Override
        public Set<Map.Entry<K, V>> entrySet() {
            return new AbstractSet<>() {
                @Override
                public int size() {
                    return size;
                }

                @Override
                @SuppressWarnings("unchecked")
                public Iterator<Map.Entry<K, V>> iterator() {
                    return (Iterator<Map.Entry<K, V>>) (Iterator<?>) new EntryIterator(root, size);
                }
            };
        }

        /** The map it has built. The trie is handed over here, so nothing may be set afterwards. */
        PersistentHashMap<K, V> build() {
            built = true;
            return size == 0 ? empty() : new PersistentHashMap<>(root, size);
        }
    }
}
