package souther.compiler.carrier;

import java.util.HashMap;
import java.util.Map;
import java.util.Objects;
import java.util.function.Consumer;

/**
 * What a key answers, and nothing about what order the keys were given in.
 *
 * <p>A {@link Map} answers this and more: {@code keySet}, {@code values}, {@code forEach}, an
 * {@code iterator}, even {@code toString} — every one of them a walk, and a walk taken off a map
 * that was built through a salted copy is a walk taken off nothing, differently on some runs than
 * on others. This answers only what a key is bound to and whether one is bound at all, so a caller
 * who wants to know something about an order has to ask a value that states one rather than
 * iterating this to find out — there is nothing here to iterate, and nothing here spells its
 * contents out as text either.
 *
 * <p>Not a {@code Map} and not an {@code Iterable}: a caller who reaches for {@code entrySet} or a
 * {@code for} loop finds nothing to reach for, which is the point. Built from nothing wider than a
 * key and a value handed over one pair at a time ({@link #built}), so there is no arbitrary
 * iteration this could be built from to launder into an answer that looks like one.
 *
 * <p>Neither a key nor a value may be {@code null}: {@link #get} already answers {@code null} for a
 * key nothing is bound to, and a bound key answering the same thing would leave a caller unable to
 * tell the two apart from {@link #get} alone.
 *
 * <p>A key stated twice while this is built is refused rather than resolved by keeping one of the
 * two: the two callers who put it disagree about what it answers, and picking a winner would answer
 * a question neither of them asked. Asked by {@link #containsKey} rather than read off what
 * {@code Map.put} hands back — a map answers {@code null} for a fresh key and for one already bound
 * to {@code null} alike, so a check that trusted the answer back would let a key through twice
 * wherever the first of the two bound it to nothing, and nothing may be bound to anyway.
 */
public final class Lookup<K, V> {

    private final Map<K, V> at;

    private Lookup(Map<K, V> at) {
        this.at = at;
    }

    /**
     * Built from {@code fill}, which hands over one key at a time and nothing else.
     *
     * <p>The {@link Entries} {@code fill} is handed writes straight to a map this keeps to itself
     * until {@code fill} returns, and only a snapshot of it leaves — {@link #equals} reads that
     * snapshot and nothing else, so a caller who keeps the {@link Entries} past the call cannot go
     * on changing what a value already built from it answers.
     */
    public static <K, V> Lookup<K, V> built(Consumer<Entries<K, V>> fill) {
        Map<K, V> at = new HashMap<>();
        fill.accept((key, value) -> {
            Objects.requireNonNull(key, "a key");
            Objects.requireNonNull(value, "a value");
            if (at.containsKey(key)) {
                throw new IllegalArgumentException("a key stated twice: " + key);
            }
            at.put(key, value);
        });
        return new Lookup<>(Map.copyOf(at));
    }

    /** How {@link #built} is filled: a key and the value bound to it, and nothing this can be
     *  asked to do besides state one. */
    public interface Entries<K, V> {
        void put(K key, V value);
    }

    /** What {@code key} is bound to, or {@code null} where nothing is. */
    public V get(K key) {
        return at.get(key);
    }

    /** Whether anything is bound to {@code key}. */
    public boolean containsKey(K key) {
        return at.containsKey(key);
    }

    @Override
    public boolean equals(Object other) {
        return other instanceof Lookup<?, ?> lookup && at.equals(lookup.at);
    }

    @Override
    public int hashCode() {
        return at.hashCode();
    }
}
