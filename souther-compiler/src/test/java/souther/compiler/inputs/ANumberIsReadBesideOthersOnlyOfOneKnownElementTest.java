package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.types.BindingId;
import souther.compiler.types.BindingOwner;

import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A comparison takes a number of an element beside its other numbers only where which element it
 * is, is known and is the one the comparison already reads: else two numbers at one position would
 * be put in one form as one number, and cancel or add up to what was not written.
 *
 * <p>Asked of {@link ElementsMet} with the elements written out by hand, which is all it is
 * handed.
 */
class ANumberIsReadBesideOthersOnlyOfOneKnownElementTest {

    private static final ElementsNamed.Slot AN_ITEM = ElementsNamed.Slot.innermostOf(
            TermPath.of("x").then("items").element());

    private static final BindingOwner OWNER = new BindingOwner.OfValue("probe", "f");
    private static final BindingId A = new BindingId(OWNER, 1);
    private static final BindingId B = new BindingId(OWNER, 2);

    private static ElementsNamed through(BindingId... names) {
        return ElementsNamed.of(List.of(names).stream()
                .map(name -> new ElementsNamed.Named(AN_ITEM, name)).toList());
    }

    /** The same element read again is taken; another element of the container is not. */
    @Test
    void oneElementIsTakenAgainAndAnotherIsRefused() {
        ElementsMet met = new ElementsMet();
        assertTrue(met.admits(through(A)));
        assertTrue(met.admits(through(A)));
        assertFalse(met.crowded());
        assertFalse(met.admits(through(B)));
        assertTrue(met.crowded());
    }

    /** A number read through a name whose element is not known is refused, though nothing has
     *  been read of the container before: which element it is, is not said. */
    @Test
    void aNumberOfAnElementNotKnownIsRefused() {
        ElementsMet met = new ElementsMet();
        assertFalse(met.admits(ElementsNamed.of(List.of(), Set.of(AN_ITEM))));
        assertTrue(met.crowded());
    }

    /** And so is one number read through two names for one element. */
    @Test
    void aNumberOfTwoElementsAtOnceIsRefused() {
        ElementsMet met = new ElementsMet();
        assertFalse(met.admits(through(A, B)));
        assertTrue(met.crowded());
    }

    /**
     * What has met an element, or was refused for naming another, is touched, and a number that
     * names no element leaves it as it was: a reader that shares one reading between several
     * numbers shares it only while none of them has met an element, since the next would be read
     * beside what the first met and not as a number of its own.
     */
    @Test
    void aComparisonIsTouchedOnceAnElementIsMetOrRefused() {
        ElementsMet met = new ElementsMet();
        assertTrue(met.untouched());
        assertTrue(met.admits(ElementsNamed.NONE));
        assertTrue(met.untouched());

        assertTrue(met.admits(through(A)));
        assertFalse(met.untouched());

        ElementsMet refused = new ElementsMet();
        assertFalse(refused.admits(ElementsNamed.of(List.of(), Set.of(AN_ITEM))));
        assertFalse(refused.untouched());
    }

    /**
     * What is rewound to a mark is what the mark was taken as, however often it is rewound to it:
     * a reading that began from it and met another element is put back, and so is the next one
     * that begins from it, which a copy handed back as the state to go on from would not be.
     */
    @Test
    void aMarkIsRewoundToAsOftenAsThereAreWaysFromIt() {
        ElementsMet met = new ElementsMet();
        assertTrue(met.admits(through(A)));
        ElementsMet.Mark atTheParting = met.mark();

        assertFalse(met.admits(through(B)));
        met.rewind(atTheParting);
        assertFalse(met.crowded());
        assertTrue(met.admits(through(A)));

        assertFalse(met.admits(through(B)));
        met.rewind(atTheParting);
        assertFalse(met.crowded());
        assertTrue(met.admits(through(A)));
        assertFalse(met.admits(through(B)));
    }

    /** The elements put back are those of the object a reading made on it asks of, which is the
     *  one rewound and not another standing in for it. */
    @Test
    void aMarkRewindsTheObjectItWasTakenOf() {
        ElementsMet met = new ElementsMet();
        ElementsMet.Mark none = met.mark();
        assertTrue(met.admits(through(A)));
        assertFalse(met.untouched());

        met.rewind(none);

        assertTrue(met.untouched());
        assertTrue(met.admits(through(B)));
    }

    /** A number read by itself holds nothing, so there is nothing for it to be touched by. */
    @Test
    void aNumberReadByItselfIsNeverTouched() {
        assertTrue(ElementsMet.NONE.admits(through(A)));
        assertTrue(ElementsMet.NONE.untouched());
    }

    /** A number read by itself is put in no form beside another, and is held to nothing. */
    @Test
    void aNumberReadByItselfIsHeldToNothing() {
        assertTrue(ElementsMet.NONE.admits(ElementsNamed.of(List.of(), Set.of(AN_ITEM))));
    }
}
