package souther.compiler.carrier;

import org.junit.jupiter.api.Test;

import java.util.concurrent.atomic.AtomicReference;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertThrows;

/** What a {@link Lookup} answers, and what it refuses to become once it is built. */
class ALookupAnswersOnlyWhatAKeyIsBoundToTest {

    @Test
    void twoLookupsFilledInDifferentOrdersAreOneValue() {
        Lookup<String, Integer> first = Lookup.built(put -> {
            put.put("a", 1);
            put.put("b", 2);
        });
        Lookup<String, Integer> second = Lookup.built(put -> {
            put.put("b", 2);
            put.put("a", 1);
        });

        assertEquals(first, second, "what is bound to each key is the same value, whichever order"
                + " the two were filled in");
        assertEquals(first.hashCode(), second.hashCode());
    }

    @Test
    void aKeyStatedTwiceIsRefused() {
        assertThrows(IllegalArgumentException.class, () -> Lookup.built(put -> {
            put.put("a", 1);
            put.put("a", 2);
        }), "the two callers who put it disagree about what it answers");
    }

    @Test
    void aNullKeyIsRefused() {
        assertThrows(NullPointerException.class,
                () -> Lookup.built(put -> put.put(null, 1)));
    }

    @Test
    void aNullValueIsRefused() {
        // A Lookup bound to null would answer the same as one bound to nothing at all, and a
        // caller asking Lookup#get could not tell the two apart.
        assertThrows(NullPointerException.class,
                () -> Lookup.<String, Integer>built(put -> put.put("a", null)));
    }

    @Test
    void whatIsBoundToAnAbsentKeyIsNull() {
        Lookup<String, Integer> lookup = Lookup.built(put -> put.put("a", 1));

        assertFalse(lookup.containsKey("b"));
        assertNull(lookup.get("b"));
    }

    @Test
    void aCallerThatKeepsTheEntriesCannotChangeWhatWasAlreadyBuilt() {
        AtomicReference<Lookup.Entries<String, Integer>> kept = new AtomicReference<>();

        Lookup<String, Integer> built = Lookup.built(put -> {
            put.put("a", 1);
            kept.set(put);
        });

        kept.get().put("b", 2);

        assertFalse(built.containsKey("b"), "built was handed a snapshot once the callback that"
                + " filled it returned, so writing through a kept Entries afterward cannot change"
                + " what built answers");
    }

    // Nothing tests that a Lookup is not a Map, a Set, a Collection or an Iterable: Lookup is a
    // final class implementing none of them, so `instanceof` against any of those is a compile
    // error rather than a runtime question — the compiler already refuses the call a walk would
    // start with, which is a stronger guarantee than a test of this could add.
}
