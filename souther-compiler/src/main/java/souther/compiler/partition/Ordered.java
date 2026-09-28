package souther.compiler.partition;

import souther.compiler.values.InOneOrder;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.SequencedMap;

/**
 * Copying a map of obligations against answers, with neither half of any entry missing.
 *
 * <p>{@link Map#copyOf} refuses null; a {@link LinkedHashMap} admits it. Every value here that
 * holds obligations against answers wants the refusal, and going without it is how an absence
 * walked back into the middle of a structure built to have none: a key present with nothing under
 * it satisfied a check written over the keys, and the reader that looked the key up met the null
 * the whole arrangement exists to stop.
 *
 * <p>So the rule is written once. A second spelling of it is a second place for one of the two
 * halves to be forgotten.
 *
 * <p><b>And whether the copy keeps the order it was handed is the caller's question, which is why
 * there are two.</b> A mapping read by key alone is two mappings written two ways and is one value,
 * so it is held in no order at all ({@link #byKey}); a mapping whose order is what a reader is
 * offered keeps it ({@link #copyOf}). Kept where nothing asks for it, the order is something a
 * reader can start reading and a sentence can start saying, which is what this compiler holds
 * itself to elsewhere.
 */
final class Ordered {

    /**
     * The same entries, in the order they were handed over, with neither half of any entry
     * missing.
     */
    static <K, V> SequencedMap<K, V> copyOf(Map<K, V> entries) {
        LinkedHashMap<K, V> out = new LinkedHashMap<>();
        whole(entries, out);
        return Collections.unmodifiableSequencedMap(out);
    }

    /**
     * The same entries in no order at all, with neither half of any entry missing.
     *
     * <p>For a mapping every reader of which asks it by key. What it is equal to is which key holds
     * what, so two callers that built one mapping two ways hand over one value — and a copy that
     * kept the order one of them happened to build it in would hand a reader something that value
     * does not have.
     */
    static <K, V> Map<K, V> byKey(Map<K, V> entries) {
        HashMap<K, V> out = new HashMap<>();
        whole(entries, out);
        return Collections.unmodifiableMap(out);
    }

    /**
     * Every entry of {@code entries} into {@code out}, refusing the ones with a half missing.
     *
     * <p>Every half-entry named and not the first one met. What is handed over holds no order of
     * its own — two callers that built one mapping two ways hand over one value — so a refusal
     * that stopped at the first would tell the two of them two different things about one thing
     * they got wrong.
     */
    private static <K, V> void whole(Map<K, V> entries, Map<K, V> out) {
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
    }

    private Ordered() {}
}
