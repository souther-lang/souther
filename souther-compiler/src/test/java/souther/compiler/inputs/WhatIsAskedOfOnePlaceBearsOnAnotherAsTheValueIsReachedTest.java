package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Two places bear on each other ({@link TermPath#bearsOn}) where one stands at, under or around the
 * other as the value is reached, each narrowing to cases set aside, and on nothing else.
 */
class WhatIsAskedOfOnePlaceBearsOnAnotherAsTheValueIsReachedTest {

    private static final TermPath R = TermPath.of("r");
    private static final TermPath ITEMS = R.then("items");
    private static final TermPath PRESENT = R.refine(Refinement.of(new Case.Presence(true)));
    private static final TermPath ABSENT = R.refine(Refinement.of(new Case.Presence(false)));

    private static void assertBoth(boolean bears, TermPath one, TermPath other) {
        if (bears) {
            assertTrue(one.bearsOn(other), () -> one + " bears on " + other);
            assertTrue(other.bearsOn(one), () -> other + " bears on " + one);
        } else {
            assertFalse(one.bearsOn(other), () -> one + " is apart from " + other);
            assertFalse(other.bearsOn(one), () -> other + " is apart from " + one);
        }
    }

    @Test
    void aContainerAndItsElementsBearOnEachOther() {
        assertBoth(true, ITEMS, ITEMS.element());
        assertBoth(true, ITEMS, ITEMS.element().then("price"));
        assertBoth(true, ITEMS, ITEMS);
    }

    @Test
    void aValueAndTheValueNarrowedToACaseBearOnEachOther() {
        assertBoth(true, R.then("code"), PRESENT.then("code"));
        assertBoth(true, PRESENT.then("code"), ABSENT, "two cases of one value exclude each other");
        assertBoth(true, PRESENT, R.then("code"));
        assertBoth(true, PRESENT.then("a"), ABSENT.then("b"),
                "what is asked under two cases of one value excludes each other");
    }

    @Test
    void placesApartAsTheValueIsReachedDoNot() {
        assertBoth(false, R.then("a"), R.then("b"));
        assertBoth(false, PRESENT.then("a"), R.then("b"));
        assertBoth(false, PRESENT.then("a"), PRESENT.then("b"));
        assertBoth(false, ITEMS.element(), R.then("total"));
        assertBoth(false, R, TermPath.of("s"));
    }

    private static void assertBoth(boolean bears, TermPath one, TermPath other, String why) {
        assertBoth(bears, one, other);
        assertTrue(bears == one.bearsOn(other), why);
    }
}
