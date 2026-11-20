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

    private static final ElementsNamed.Slot A_LINE = ElementsNamed.Slot.innermostOf(
            TermPath.of("x").then("lines").element());

    private static final BindingOwner OWNER = new BindingOwner.OfValue("probe", "f");
    private static final BindingId A = new BindingId(OWNER, 1);
    private static final BindingId B = new BindingId(OWNER, 2);

    private static ElementsNamed through(BindingId... names) {
        return ElementsNamed.of(List.of(names).stream()
                .map(name -> new ElementsNamed.Named(AN_ITEM, name)).toList());
    }

    /** A number of an item read through {@code names}, held where an item stands. */
    private static boolean admits(ElementsMet met, BindingId... names) {
        return met.admits(through(names), Set.of(AN_ITEM));
    }

    /** A number held at {@code at} and read through no name, as what a lookup answers is. */
    private static boolean admitsThroughNoName(ElementsMet met, ElementsNamed.Slot at) {
        return met.admits(ElementsNamed.NONE, Set.of(at));
    }

    /** The same element read again is taken; another element of the container is not. */
    @Test
    void oneElementIsTakenAgainAndAnotherIsRefused() {
        ElementsMet met = new ElementsMet();
        assertTrue(admits(met, A));
        assertTrue(admits(met, A));
        assertFalse(met.crowded());
        assertFalse(admits(met, B));
        assertTrue(met.crowded());
    }

    /** A number read through a name whose element is not known is refused, though nothing has
     *  been read of the container before: which element it is, is not said. */
    @Test
    void aNumberOfAnElementNotKnownIsRefused() {
        ElementsMet met = new ElementsMet();
        assertFalse(met.admits(ElementsNamed.of(List.of(), Set.of(AN_ITEM)), Set.of(AN_ITEM)));
        assertTrue(met.crowded());
    }

    /** And so is one number read through two names for one element. */
    @Test
    void aNumberOfTwoElementsAtOnceIsRefused() {
        ElementsMet met = new ElementsMet();
        assertFalse(admits(met, A, B));
        assertTrue(met.crowded());
    }

    /**
     * A number of an element read through no name is taken where nothing else of the container
     * has been read, and is no element any other read is known to be: an item named after it is
     * refused, and so is another read through no name, which may be another entry.
     */
    @Test
    void anElementReadThroughNoNameStandsBesideNothingElseOfItsContainer() {
        ElementsMet named = new ElementsMet();
        assertTrue(admitsThroughNoName(named, AN_ITEM));
        assertFalse(admits(named, A));
        assertTrue(named.crowded());

        ElementsMet twice = new ElementsMet();
        assertTrue(admitsThroughNoName(twice, AN_ITEM));
        assertFalse(admitsThroughNoName(twice, AN_ITEM));
    }

    /** Nor beside an element a name stands for, read before it. */
    @Test
    void anElementReadThroughNoNameIsRefusedBesideANamedOne() {
        ElementsMet met = new ElementsMet();
        assertTrue(admits(met, A));
        assertFalse(admitsThroughNoName(met, AN_ITEM));
        assertTrue(met.crowded());
    }

    /** An element of another container is another element, whatever it was read through. */
    @Test
    void anElementOfAnotherContainerIsTakenBesideIt() {
        ElementsMet met = new ElementsMet();
        assertTrue(admitsThroughNoName(met, AN_ITEM));
        assertTrue(admitsThroughNoName(met, A_LINE));
        assertFalse(met.crowded());
    }

    /**
     * What is rewound to a mark is what the mark was taken as, however often it is rewound to it:
     * a reading that began from it and met another element is put back, and so is the next one
     * that begins from it, which a copy handed back as the state to go on from would not be.
     */
    @Test
    void aMarkIsRewoundToAsOftenAsThereAreWaysFromIt() {
        ElementsMet met = new ElementsMet();
        assertTrue(admits(met, A));
        ElementsMet.Mark atTheParting = met.mark();

        assertFalse(admits(met, B));
        met.rewind(atTheParting);
        assertFalse(met.crowded());
        assertTrue(admits(met, A));

        assertFalse(admits(met, B));
        met.rewind(atTheParting);
        assertFalse(met.crowded());
        assertTrue(admits(met, A));
        assertFalse(admits(met, B));
    }

    /** The elements put back are those of the object a reading made on it asks of, which is the
     *  one rewound and not another standing in for it: an element read through no name as well. */
    @Test
    void aMarkRewindsTheObjectItWasTakenOf() {
        ElementsMet met = new ElementsMet();
        ElementsMet.Mark none = met.mark();
        assertTrue(admits(met, A));
        assertFalse(admits(met, B));

        met.rewind(none);

        assertFalse(met.crowded());
        assertTrue(admitsThroughNoName(met, AN_ITEM));

        met.rewind(none);

        assertTrue(admits(met, B));
        assertFalse(admits(met, A));
    }

    /** A number read by itself is put in no form beside another, and is held to nothing. */
    @Test
    void aNumberReadByItselfIsHeldToNothing() {
        assertTrue(ElementsMet.NONE.admits(ElementsNamed.of(List.of(), Set.of(AN_ITEM)),
                Set.of(AN_ITEM)));
        assertTrue(admitsThroughNoName(ElementsMet.NONE, AN_ITEM));
        assertTrue(admitsThroughNoName(ElementsMet.NONE, AN_ITEM));
    }
}
