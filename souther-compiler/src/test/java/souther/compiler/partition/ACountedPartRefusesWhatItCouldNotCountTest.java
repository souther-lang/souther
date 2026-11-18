package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A counted part ({@link Tallied}) refuses what would change it without its count moving, and a
 * part refused anything is as it was.
 *
 * <p>A null put in would read as nothing having been there, and a part of another count put
 * inside would change without this count seeing it.
 */
class ACountedPartRefusesWhatItCouldNotCountTest {

    @Test
    void aTableRefusesANullAndIsAsItWas() {
        Tallied.Changes changes = new Tallied.Changes();
        Tallied.Table<String, String> table = changes.table(HashMap::new);
        long before = changes.count();

        assertThrows(NullPointerException.class, () -> table.put("k", null));
        assertThrows(NullPointerException.class, () -> table.putIfAbsent("k", null));
        assertThrows(NullPointerException.class, () -> table.computeIfAbsent("k", _ -> null));

        assertTrue(table.isEmpty());
        assertEquals(before, changes.count());
    }

    @Test
    void aPartOfAnotherCountIsRefusedWhereverItWouldBePutIn() {
        Tallied.Changes changes = new Tallied.Changes();
        Tallied.Group<String> elsewhere = new Tallied.Changes().group(HashSet::new);
        Tallied.Table<String, Tallied.Group<String>> table = changes.table(HashMap::new);
        Tallied.Sequence<Tallied.Group<String>> sequence = changes.sequence();
        Tallied.Value<Tallied.Group<String>> value = changes.value(null);

        assertThrows(IllegalArgumentException.class, () -> table.put("k", elsewhere));
        assertThrows(IllegalArgumentException.class, () -> sequence.add(elsewhere));
        assertThrows(IllegalArgumentException.class, () -> value.set(elsewhere));
        assertThrows(IllegalArgumentException.class, () -> changes.value(elsewhere));

        assertTrue(table.isEmpty());
        assertTrue(sequence.isEmpty());
        assertEquals(0, changes.count());
    }

    @Test
    void aPartOfAnotherCountIsRefusedAsAKeyAsMuchAsAValue() {
        Tallied.Changes changes = new Tallied.Changes();
        Tallied.Group<String> elsewhere = new Tallied.Changes().group(HashSet::new);
        Tallied.Table<Tallied.Group<String>, String> table = changes.table(HashMap::new);

        assertThrows(IllegalArgumentException.class, () -> table.put(elsewhere, "v"));
        assertThrows(IllegalArgumentException.class, () -> table.putIfAbsent(elsewhere, "v"));
        assertThrows(IllegalArgumentException.class,
                () -> table.computeIfAbsent(elsewhere, _ -> "v"));

        assertTrue(table.isEmpty());
        assertEquals(0, changes.count());
    }

    @Test
    void membersOneOfWhichIsRefusedPutNoneIn() {
        Tallied.Changes changes = new Tallied.Changes();
        Tallied.Group<String> group = changes.group(HashSet::new);

        assertThrows(NullPointerException.class,
                () -> group.addAll(Arrays.asList("admitted", null)));

        assertTrue(group.isEmpty());
        assertEquals(0, changes.count());
    }

    @Test
    void somethingAddedToAPartInsideAnotherMovesTheCountOfBoth() {
        Tallied.Changes changes = new Tallied.Changes();
        Tallied.Table<String, Tallied.Group<String>> table = changes.table(HashMap::new);
        Tallied.Group<String> inside = table.computeIfAbsent("k", _ -> changes.group(HashSet::new));
        long before = changes.count();

        inside.add("member");

        assertEquals(before + 1, changes.count());
    }
}
