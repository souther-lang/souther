package souther.compiler.check;

import souther.compiler.types.BindingId;

import java.util.AbstractMap;
import java.util.AbstractSet;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;

/**
 * What an environment holds per binding, as a value that is extended without being copied.
 *
 * <p>{@link Scope} and {@link Denotations} are both handed on as snapshots: an arm is read under the
 * environment the arm was entered in while a sibling reads under the one it extended, and a
 * reader may keep one and ask it later. Extending an environment therefore returns a new one and
 * leaves the old one as it was. Doing that by copying the whole map makes a body of N bindings cost
 * N² to enter; here an extension shares everything it did not touch, so it costs what the hash
 * trie is deep — bounded by the width of the hash, not by how many bindings are held.
 *
 * <p>Iteration is in the order bindings were first entered, which is the order a diagnostic offers
 * names in. Entering a binding already held replaces its value and keeps its place.
 *
 * <p>This is the representation of one environment and not a general collection: the key is always
 * a {@link BindingId}, and nothing here removes.
 */
final class BindingMap<V> extends AbstractMap<BindingId, V> {

    private static final int BITS = 5;

    private static final int MASK = (1 << BITS) - 1;

    private static final BindingMap<Object> EMPTY = new BindingMap<>(null, 0, null);

    private final Node root;

    private final int size;

    private final Order order;

    private BindingMap(Node root, int size, Order order) {
        this.root = root;
        this.size = size;
        this.order = order;
    }

    @SuppressWarnings("unchecked")
    static <V> BindingMap<V> empty() {
        return (BindingMap<V>) EMPTY;
    }

    /** {@code map} as an environment: itself where it already is one, otherwise its entries entered
     * in the order it iterates them. */
    static <V> BindingMap<V> from(Map<BindingId, V> map) {
        if (map instanceof BindingMap<V> already) {
            return already;
        }
        return BindingMap.<V>empty().withAll(map);
    }

    /** This environment with {@code binding} entered as {@code value}; this one is left as it was. */
    BindingMap<V> with(BindingId binding, V value) {
        Objects.requireNonNull(value, "a binding entered is a binding with something behind it");
        Leaf leaf = new Leaf(hashOf(binding), binding, value);
        boolean held = findLeaf(binding) != null;
        return new BindingMap<>(put(root, 0, leaf), held ? size : size + 1,
                held ? order : new Order(binding, order));
    }

    BindingMap<V> withAll(Map<BindingId, V> more) {
        BindingMap<V> out = this;
        for (Map.Entry<BindingId, V> entry : more.entrySet()) {
            out = out.with(entry.getKey(), entry.getValue());
        }
        return out;
    }

    @Override
    @SuppressWarnings("unchecked")
    public V get(Object binding) {
        Leaf leaf = findLeaf(binding);
        return leaf == null ? null : (V) leaf.value();
    }

    @Override
    public boolean containsKey(Object binding) {
        return findLeaf(binding) != null;
    }

    @Override
    public int size() {
        return size;
    }

    @Override
    public Set<Map.Entry<BindingId, V>> entrySet() {
        return new AbstractSet<>() {
            @Override
            public Iterator<Map.Entry<BindingId, V>> iterator() {
                return entriesInOrder().iterator();
            }

            @Override
            public int size() {
                return size;
            }
        };
    }

    private List<Map.Entry<BindingId, V>> entriesInOrder() {
        List<Map.Entry<BindingId, V>> entries = new ArrayList<>(size);
        for (Order at = order; at != null; at = at.before()) {
            entries.add(new AbstractMap.SimpleImmutableEntry<>(at.binding(), get(at.binding())));
        }
        Collections.reverse(entries);
        return Collections.unmodifiableList(entries);
    }

    private Leaf findLeaf(Object binding) {
        if (!(binding instanceof BindingId id)) {
            return null;
        }
        int hash = hashOf(id);
        Node at = root;
        for (int shift = 0; at != null; shift += BITS) {
            switch (at) {
                case Leaf leaf -> {
                    return leaf.key().equals(id) ? leaf : null;
                }
                case Collision collision -> {
                    if (collision.hash() != hash) {
                        return null;
                    }
                    for (Leaf leaf : collision.leaves()) {
                        if (leaf.key().equals(id)) {
                            return leaf;
                        }
                    }
                    return null;
                }
                case Branch branch -> {
                    int bit = 1 << ((hash >>> shift) & MASK);
                    if ((branch.bitmap() & bit) == 0) {
                        return null;
                    }
                    at = branch.slots()[Integer.bitCount(branch.bitmap() & (bit - 1))];
                }
            }
        }
        return null;
    }

    private static int hashOf(BindingId binding) {
        int h = binding.hashCode();
        return h ^ (h >>> 16);
    }

    private static Node put(Node at, int shift, Leaf leaf) {
        return switch (at) {
            case null -> leaf;
            case Leaf held -> {
                if (held.key().equals(leaf.key())) {
                    yield leaf;
                }
                yield held.hash() == leaf.hash()
                        ? new Collision(leaf.hash(), List.of(held, leaf))
                        : join(held, held.hash(), leaf, shift);
            }
            case Collision held -> {
                if (held.hash() != leaf.hash()) {
                    yield join(held, held.hash(), leaf, shift);
                }
                List<Leaf> leaves = new ArrayList<>(held.leaves());
                int same = -1;
                for (int i = 0; i < leaves.size(); i++) {
                    if (leaves.get(i).key().equals(leaf.key())) {
                        same = i;
                    }
                }
                if (same >= 0) {
                    leaves.set(same, leaf);
                } else {
                    leaves.add(leaf);
                }
                yield new Collision(held.hash(), List.copyOf(leaves));
            }
            case Branch branch -> {
                int bit = 1 << ((leaf.hash() >>> shift) & MASK);
                int pos = Integer.bitCount(branch.bitmap() & (bit - 1));
                Node[] slots;
                if ((branch.bitmap() & bit) != 0) {
                    slots = branch.slots().clone();
                    slots[pos] = put(slots[pos], shift + BITS, leaf);
                    yield new Branch(branch.bitmap(), slots);
                }
                slots = new Node[branch.slots().length + 1];
                System.arraycopy(branch.slots(), 0, slots, 0, pos);
                slots[pos] = leaf;
                System.arraycopy(branch.slots(), pos, slots, pos + 1, branch.slots().length - pos);
                yield new Branch(branch.bitmap() | bit, slots);
            }
        };
    }

    /** A branch holding {@code held} and {@code leaf}, which hash differently. */
    private static Node join(Node held, int heldHash, Leaf leaf, int shift) {
        int heldIndex = (heldHash >>> shift) & MASK;
        int leafIndex = (leaf.hash() >>> shift) & MASK;
        if (heldIndex == leafIndex) {
            return new Branch(1 << heldIndex, new Node[] {join(held, heldHash, leaf, shift + BITS)});
        }
        Node[] slots = heldIndex < leafIndex ? new Node[] {held, leaf} : new Node[] {leaf, held};
        return new Branch((1 << heldIndex) | (1 << leafIndex), slots);
    }

    private sealed interface Node permits Leaf, Collision, Branch {}

    private record Leaf(int hash, BindingId key, Object value) implements Node {}

    private record Collision(int hash, List<Leaf> leaves) implements Node {}

    private static final class Branch implements Node {
        private final int bitmap;

        private final Node[] slots;

        Branch(int bitmap, Node[] slots) {
            this.bitmap = bitmap;
            this.slots = slots;
        }

        int bitmap() {
            return bitmap;
        }

        Node[] slots() {
            return slots;
        }
    }

    private record Order(BindingId binding, Order before) {}
}
