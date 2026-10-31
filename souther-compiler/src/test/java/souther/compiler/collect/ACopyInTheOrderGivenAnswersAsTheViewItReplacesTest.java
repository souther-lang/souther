package souther.compiler.collect;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * A copy kept in the order given answers every question as the unmodifiable view over a
 * {@code LinkedHashMap} or {@code LinkedHashSet} it stands in for: below the size where a table is
 * made and above it, with keys whose hashes collide, a null key and null values.
 */
class ACopyInTheOrderGivenAnswersAsTheViewItReplacesTest {

    /** A key whose hash is one of three, so that keys collide in the hashes and in a table. */
    private record Colliding(int id) {
        @Override
        public int hashCode() {
            return id % 3;
        }
    }

    /** Below the size a table is made at, at it, and well past it. */
    private static final List<Integer> SIZES = List.of(0, 1, 2, 8, 9, 10, 40);

    private static Map<Object, Object> given(int size) {
        Map<Object, Object> out = new LinkedHashMap<>();
        for (int i = size - 1; i >= 0; i--) {
            out.put(i == 3 ? null : new Colliding(i), i % 4 == 1 ? null : "v" + i);
        }
        return out;
    }

    @Test
    void aMapAnswersAsTheViewOverALinkedHashMap() {
        for (int size : SIZES) {
            Map<Object, Object> view = Collections.unmodifiableMap(given(size));
            Map<Object, Object> held = InTheOrderGiven.map(given(size));
            assertEquals(List.copyOf(view.keySet().stream().map(String::valueOf).toList()),
                    held.keySet().stream().map(String::valueOf).toList(), "the order of the keys");
            assertEquals(new ArrayList<>(view.values()), new ArrayList<>(held.values()));
            assertEquals(new ArrayList<>(view.entrySet()), new ArrayList<>(held.entrySet()));
            List<Object> keysForEach = new ArrayList<>();
            held.forEach((key, value) -> keysForEach.add(key));
            assertEquals(new ArrayList<>(view.keySet()), keysForEach);
            for (int i = -1; i <= size; i++) {
                Object key = i == 3 ? null : new Colliding(i);
                assertEquals(view.get(key), held.get(key), "the value of " + key);
                assertEquals(view.containsKey(key), held.containsKey(key), "holding " + key);
                assertEquals(view.getOrDefault(key, "none"), held.getOrDefault(key, "none"));
                assertEquals(view.keySet().contains(key), held.keySet().contains(key));
            }
            assertEquals(view.containsValue(null), held.containsValue(null));
            assertEquals(view, held);
            assertEquals(held, view);
            assertEquals(view.hashCode(), held.hashCode());
            assertEquals(view.toString(), held.toString());
            assertEquals(view.size(), held.size());
            assertEquals(view.isEmpty(), held.isEmpty());
            assertThrows(UnsupportedOperationException.class, () -> held.put("k", "v"));
            assertThrows(UnsupportedOperationException.class, () -> held.remove(new Colliding(0)));
            assertSame(held, InTheOrderGiven.map(held));
        }
    }

    /** The keys of a copy as a list are its keys in its order, as the view's keys listed are, and
     *  the list refuses every change; so are those of a map this did not make. */
    @Test
    void theKeysOfACopyAreListedInItsOrder() {
        for (int size : SIZES) {
            List<Object> expected = new ArrayList<>(given(size).keySet());
            List<Object> keys = InTheOrderGiven.keys(InTheOrderGiven.map(given(size)));
            assertEquals(expected, keys, "the keys of " + size);
            assertEquals(expected.hashCode(), keys.hashCode());
            for (int at = 0; at < size; at++) {
                assertEquals(expected.get(at), keys.get(at));
            }
            assertThrows(IndexOutOfBoundsException.class, () -> keys.get(size));
            assertThrows(UnsupportedOperationException.class, () -> keys.add("k"));
        }
        Map<String, Integer> plain = new LinkedHashMap<>();
        plain.put("b", 1);
        plain.put("a", 2);
        assertEquals(List.of("b", "a"), InTheOrderGiven.keys(plain));
    }

    @Test
    void aMapIsNotEqualToOneMissingANullValuedKey() {
        Map<Object, Object> nulls = new LinkedHashMap<>();
        nulls.put("a", null);
        Map<Object, Object> other = new LinkedHashMap<>();
        other.put("b", null);
        assertEquals(false, InTheOrderGiven.map(nulls).equals(other));
        assertEquals(nulls, InTheOrderGiven.map(nulls));
    }

    @Test
    void aSetAnswersAsTheViewOverALinkedHashSet() {
        for (int size : SIZES) {
            Set<Object> given = new LinkedHashSet<>(given(size).keySet());
            Set<Object> view = Collections.unmodifiableSet(given);
            Set<Object> held = InTheOrderGiven.set(given);
            assertEquals(new ArrayList<>(view), new ArrayList<>(held), "the order");
            List<Object> each = new ArrayList<>();
            held.forEach(each::add);
            assertEquals(new ArrayList<>(view), each);
            for (int i = -1; i <= size; i++) {
                Object element = i == 3 ? null : new Colliding(i);
                assertEquals(view.contains(element), held.contains(element), "holding " + element);
            }
            assertEquals(view, held);
            assertEquals(held, view);
            assertEquals(view.hashCode(), held.hashCode());
            assertEquals(view.toString(), held.toString());
            assertThrows(UnsupportedOperationException.class, () -> held.add("x"));
            assertThrows(UnsupportedOperationException.class, () -> held.remove(new Colliding(0)));
            assertSame(held, InTheOrderGiven.set(held));
        }
    }
}
