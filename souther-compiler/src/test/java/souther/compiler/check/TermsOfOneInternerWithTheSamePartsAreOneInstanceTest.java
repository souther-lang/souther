package souther.compiler.check;

import org.junit.jupiter.api.Test;
import souther.compiler.types.ValueName;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertSame;

/**
 * What {@code Term.equals} answers for terms whose parts are the same instances, and for terms
 * whose parts are only equal.
 *
 * <p>The answer for the first needs no table of pairs, so it is given without one; the contract it
 * must keep is that a difference on the face or in a part still makes two terms unequal, and that
 * two interners' graphs of one shape are still equal.
 */
class TermsOfOneInternerWithTheSamePartsAreOneInstanceTest {

    private final Term.Interner interned = new Term.Interner();

    private final ValueName size = new ValueName.Behavior("app.a", "size");

    private final ValueName other = new ValueName.Behavior("app.a", "other");

    @Test
    void aPlaceWrittenTwiceIsOneInstance() {
        assertSame(interned.written(1L), interned.written(1L));
    }

    @Test
    void aTermOfTheSameShapeAndPartsIsOneInstance() {
        Term one = interned.written(1L);

        assertSame(interned.called(size, List.of(one)), interned.called(size, List.of(one)));
    }

    @Test
    void termsDifferingInAPartAreNotEqual() {
        Term called = interned.called(size, List.of(interned.written(1L)));

        assertNotEquals(called, interned.called(size, List.of(interned.written(2L))));
    }

    @Test
    void termsDifferingInWhatTheyAreOfAreNotEqual() {
        Term one = interned.written(1L);

        assertNotEquals(interned.called(size, List.of(one)), interned.called(other, List.of(one)));
    }

    @Test
    void leavesWithOneHashAreNotEqualUnlessTheirValuesAre() {
        Term a = interned.written("Aa");
        Term b = interned.written("BB");

        assertEquals("Aa".hashCode(), "BB".hashCode());
        assertNotEquals(a, b);
    }

    @Test
    void graphsTwoInternersMadeOfOneShapeAreEqual() {
        Term.Interner elsewhere = new Term.Interner();

        Term mine = interned.called(size, List.of(interned.written(1L)));
        Term theirs = elsewhere.called(size, List.of(elsewhere.written(1L)));

        assertEquals(mine, theirs);
        assertEquals(theirs, mine);
    }

    @Test
    void aCallLookedUpIsTheInstanceTheInternerHolds() {
        Term one = interned.written(1L);

        assertNull(interned.calledIfBuilt(size, List.of(one)));

        Term built = interned.called(size, List.of(one));

        assertSame(built, interned.calledIfBuilt(size, List.of(one)));
    }
}
