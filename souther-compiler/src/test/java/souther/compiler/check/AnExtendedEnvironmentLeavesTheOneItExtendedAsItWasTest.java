package souther.compiler.check;

import souther.compiler.types.BindingId;
import souther.compiler.types.BindingOwner;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * An environment is handed on as a snapshot: an arm is read under the one it was entered in while a
 * sibling reads under the one it extended, and a reader may keep one and ask it later. Extending
 * one shares what it did not touch, so what the snapshot answers is decided by which environment
 * was asked and never by what was entered after.
 */
class AnExtendedEnvironmentLeavesTheOneItExtendedAsItWasTest {

    private static final BindingOwner OWNER = new BindingOwner.OfValue("demo", "b");

    private static BindingId id(int ordinal) {
        return new BindingId(OWNER, ordinal);
    }

    @Test
    void twoExtensionsOfOneEnvironmentDoNotSeeEachOther() {
        BindingMap<String> base = BindingMap.<String>empty().with(id(0), "base");
        BindingMap<String> left = base.with(id(1), "left");
        BindingMap<String> right = base.with(id(2), "right");

        assertEquals(1, base.size());
        assertFalse(base.containsKey(id(1)));
        assertTrue(left.containsKey(id(1)));
        assertFalse(left.containsKey(id(2)));
        assertTrue(right.containsKey(id(2)));
        assertFalse(right.containsKey(id(1)));
    }

    @Test
    void everySnapshotOfALongChainKeepsExactlyItsOwnPrefix() {
        int length = 3000;
        List<BindingMap<Integer>> snapshots = new ArrayList<>();
        BindingMap<Integer> at = BindingMap.empty();
        for (int i = 0; i < length; i++) {
            at = at.with(id(i), i);
            snapshots.add(at);
        }
        for (int i = 0; i < length; i += 97) {
            BindingMap<Integer> snapshot = snapshots.get(i);
            assertEquals(i + 1, snapshot.size());
            assertEquals(i, snapshot.get(id(i)));
            assertEquals(0, snapshot.get(id(0)));
            assertNull(snapshot.get(id(i + 1)));
        }
    }

    @Test
    void replacingABindingKeepsItsPlaceAndLeavesTheEarlierValueWhereItWas() {
        BindingMap<String> first = BindingMap.<String>empty()
                .with(id(0), "a").with(id(1), "b").with(id(2), "c");
        BindingMap<String> replaced = first.with(id(1), "B");

        assertEquals("b", first.get(id(1)));
        assertEquals("B", replaced.get(id(1)));
        assertEquals(3, replaced.size());
        assertEquals(List.of("a", "B", "c"), new ArrayList<>(replaced.values()));
        assertEquals(List.of(id(0), id(1), id(2)), new ArrayList<>(replaced.keySet()));
    }

    @Test
    void iterationIsInTheOrderBindingsWereFirstEntered() {
        BindingMap<Integer> at = BindingMap.empty();
        List<BindingId> entered = new ArrayList<>();
        for (int i = 40; i > 0; i--) {
            at = at.with(id(i), i);
            entered.add(id(i));
        }
        assertEquals(entered, new ArrayList<>(at.keySet()));
    }

    @Test
    void itIsEqualToAMapHoldingTheSameBindingsWhateverOrderTheyWereEnteredIn() {
        Map<BindingId, Integer> plain = new HashMap<>();
        BindingMap<Integer> forward = BindingMap.empty();
        BindingMap<Integer> backward = BindingMap.empty();
        for (int i = 0; i < 200; i++) {
            plain.put(id(i), i);
            forward = forward.with(id(i), i);
            backward = backward.with(id(199 - i), 199 - i);
        }
        assertEquals(plain, forward);
        assertEquals(forward, backward);
        assertEquals(plain.hashCode(), backward.hashCode());
    }

    @Test
    void aMapIsTakenAsItIsAndAnEnvironmentIsNotCopied() {
        BindingMap<String> env = BindingMap.<String>empty().with(id(0), "a");
        assertSame(env, BindingMap.from(env));
        assertEquals(env, BindingMap.from(Map.of(id(0), "a")));
    }
}
