package souther.compiler.collect;

import org.junit.jupiter.api.Test;

import java.lang.ref.WeakReference;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotSame;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertSame;

/**
 * A value made again while an equal one is held is handed out as the one held, a value is never
 * handed out for one it is not equal to — however their hashes fall — a slot holds the value made
 * last in it, and holding it keeps nothing alive.
 */
class AValueMadeAgainIsTheOneHeldTest {

    /** A value whose hash is chosen, so that two unequal ones can be put in one slot. */
    private record Hashed(String name, int hash) {
        @Override
        public int hashCode() {
            return hash;
        }
    }

    @Test
    void aValueMadeAgainIsTheOneHeld() {
        HeldOnce<Hashed> held = new HeldOnce<>(4);
        Hashed first = held.held(new Hashed("a", 1));
        Hashed again = new Hashed("a", 1);

        assertSame(first, held.held(again));
    }

    @Test
    void aValueIsNeverHandedOutForOneItIsNotEqualTo() {
        HeldOnce<Hashed> held = new HeldOnce<>(4);
        Hashed a = held.held(new Hashed("a", 7));
        Hashed b = new Hashed("b", 7);

        assertSame(b, held.held(b), "same hash, another value");
        assertEquals("b", held.held(new Hashed("b", 7)).name());
        Hashed aAgain = new Hashed("a", 7);
        assertSame(aAgain, held.held(aAgain), "the slot holds what was made last in it");
        assertNotSame(a, aAgain);
    }

    /**
     * A value nothing else holds any more is not kept alive by being held here: a table one process
     * shares across its compiles would otherwise keep whatever such a value refers to.
     */
    @Test
    void aValueNothingElseHoldsIsNotKeptAliveByTheTable() throws InterruptedException {
        HeldOnce<Hashed> held = new HeldOnce<>(4);
        WeakReference<Hashed> watched = new WeakReference<>(held.held(new Hashed("gone", 3)));

        for (int asked = 0; asked < 20 && watched.get() != null; asked++) {
            System.gc();
            Thread.sleep(10);
        }

        assertNull(watched.get(), "the table still holds a value nothing else does");
        Hashed again = new Hashed("gone", 3);
        assertSame(again, held.held(again), "made again, it is the one held from now on");
    }

    @Test
    void valuesInDifferentSlotsAreEachHeld() {
        HeldOnce<Hashed> held = new HeldOnce<>(4);
        Hashed one = held.held(new Hashed("one", 1));
        Hashed two = held.held(new Hashed("two", 2));

        assertSame(one, held.held(new Hashed("one", 1)));
        assertSame(two, held.held(new Hashed("two", 2)));
    }
}
