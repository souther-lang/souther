package souther.compiler.collect;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;

/**
 * Keys each with a value, told one at a time, where every value told one more is a new value and the
 * one it was told on still stands.
 *
 * <p>For a state carried along a path a step at a time, which names something new at most steps. A
 * map copied at each of those costs the square of the path, so one table is written for a line of
 * values each told one more than the last, and each of them reads the part of it that had been
 * written when it was made: an entry is written once and never changed, and the order entries were
 * written in says which values they belong to.
 *
 * <p>Only the last of a line writes on. A value told something after another was told something
 * else from the same one starts a table of its own, with what it can read copied — two lines from
 * one place are two lines, and neither reads what the other was told.
 *
 * <p>Written under the table's lock and read without it. What is in the table is only ever added
 * to, and an entry is in it before any value that reads it is made, so a reader reads what it may
 * read whatever is being added beside it.
 *
 * <p>No equality of its own. Two of these told the same things are two lines, and what one is
 * equal to is decided by whoever holds it, over what it reads.
 *
 * @param <K> what an entry is told under
 * @param <V> what it is told
 */
public final class AppendOnly<K, V> {

    /** One table, and how much of it has been written. */
    private static final class Table<K, V> {

        private final Map<K, Told<V>> told = new ConcurrentHashMap<>();
        private int written;
    }

    /** A value, and where in the table it was written. */
    private record Told<V>(V value, int at) {}

    private final Table<K, V> table;
    private final int reads;

    private AppendOnly(Table<K, V> table, int reads) {
        this.table = table;
        this.reads = reads;
    }

    /** Where a test in this package counts the entries a new line copies, and null everywhere
     *  else. What a value reads is the same whether its line was written on or copied, so how
     *  often a line is copied has nowhere else to be read. */
    static long[] COUNTING_COPIED;

    /** Nothing told. */
    public static <K, V> AppendOnly<K, V> empty() {
        return new AppendOnly<>(new Table<>(), 0);
    }

    /** {@code entries}, in the order the map hands them over. */
    public static <K, V> AppendOnly<K, V> of(Map<K, V> entries) {
        AppendOnly<K, V> out = empty();
        for (Map.Entry<K, V> each : entries.entrySet()) {
            out = out.with(each.getKey(), each.getValue());
        }
        return out;
    }

    /** What was told under {@code key}, or null where nothing was. */
    public V get(K key) {
        Told<V> told = table.told.get(key);
        return told != null && told.at() < reads ? told.value() : null;
    }

    /** Whether nothing was told. */
    public boolean isEmpty() {
        return reads == 0;
    }

    /**
     * These and {@code value} under {@code key}.
     *
     * @throws IllegalArgumentException where something is told under {@code key} already, which is
     *         the caller's to have asked
     */
    public AppendOnly<K, V> with(K key, V value) {
        if (get(key) != null) {
            throw new IllegalArgumentException("`" + key + "` is told already");
        }
        synchronized (table) {
            if (table.written == reads && !table.told.containsKey(key)) {
                table.told.put(key, new Told<>(value, reads));
                table.written++;
                return new AppendOnly<>(table, reads + 1);
            }
        }
        Table<K, V> fresh = new Table<>();
        for (Map.Entry<K, Told<V>> each : table.told.entrySet()) {
            if (each.getValue().at() < reads) {
                fresh.told.put(each.getKey(), each.getValue());
                long[] counting = COUNTING_COPIED;
                if (counting != null) {
                    counting[0]++;
                }
            }
        }
        fresh.told.put(key, new Told<>(value, reads));
        fresh.written = reads + 1;
        return new AppendOnly<>(fresh, reads + 1);
    }

    /** Every key, in the order they were told. */
    public Set<K> keys() {
        Set<K> out = new LinkedHashSet<>();
        for (Map.Entry<K, Told<V>> each : inOrder()) {
            out.add(each.getKey());
        }
        return out;
    }

    /** Every entry, in the order they were told. */
    public Map<K, V> asMap() {
        Map<K, V> out = new LinkedHashMap<>();
        for (Map.Entry<K, Told<V>> each : inOrder()) {
            out.put(each.getKey(), each.getValue().value());
        }
        return out;
    }

    private List<Map.Entry<K, Told<V>>> inOrder() {
        List<Map.Entry<K, Told<V>>> out = new ArrayList<>();
        for (Map.Entry<K, Told<V>> each : table.told.entrySet()) {
            if (each.getValue().at() < reads) {
                out.add(each);
            }
        }
        out.sort(Comparator.comparingInt(each -> each.getValue().at()));
        return out;
    }
}
