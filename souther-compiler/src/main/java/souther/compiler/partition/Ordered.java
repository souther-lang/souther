package souther.compiler.partition;

import souther.compiler.values.InOneOrder;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.SequencedMap;

/**
 * Copying a map without giving up either of the two things a copy is made for.
 *
 * <p>{@link Map#copyOf} refuses null and loses the order it was handed; a {@link LinkedHashMap}
 * keeps the order and admits null. Every value here that holds obligations against answers wants
 * both, and taking the second on its own is how an absence walked back into the middle of a
 * structure built to have none: a key present with nothing under it satisfied a check written over
 * the keys, and the reader that looked the key up met the null the whole arrangement exists to
 * stop.
 *
 * <p>So the rule is written once. A second spelling of it is a second place for one of the two
 * halves to be forgotten.
 */
final class Ordered {

    /**
     * The same entries, in the order they were handed over, with neither half of any entry
     * missing.
     *
     * <p>Every half-entry named and not the first one met. What is handed over holds no order of
     * its own — two callers that built one mapping two ways hand over one value — so a refusal
     * that stopped at the first would tell the two of them two different things about one thing
     * they got wrong.
     */
    static <K, V> SequencedMap<K, V> copyOf(Map<K, V> entries) {
        LinkedHashMap<K, V> out = new LinkedHashMap<>();
        List<String> halved = new ArrayList<>();
        entries.forEach((key, value) -> {
            if (key == null || value == null) {
                halved.add(key + " -> " + value);
            } else {
                out.put(key, value);
            }
        });
        if (!halved.isEmpty()) {
            throw new IllegalArgumentException(
                    "an entry with nothing on one side of it: " + InOneOrder.of(halved));
        }
        return Collections.unmodifiableSequencedMap(out);
    }

    private Ordered() {}
}
