package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * One place stands at or under another ({@link TermPath#standsAtOrUnder}) where its value is the
 * other's or one inside it as the value is reached: a narrowing to cases on one side only is
 * skipped, and two narrowings of one value to different cases are neither inside the other.
 */
class AValueStandsAtOrUnderAnotherAsTheValueIsReachedTest {

    private static final TermPath R = TermPath.of("r");
    private static final TermPath ITEMS = R.then("items");
    private static final TermPath PRESENT = R.refine(Refinement.of(new Case.Presence(true)));
    private static final TermPath ABSENT = R.refine(Refinement.of(new Case.Presence(false)));

    @Test
    void aNameReadAtAValueIsTheNameReadAtTheValueNarrowedToACase() {
        assertTrue(R.then("code").standsAtOrUnder(PRESENT.then("code")));
        assertTrue(PRESENT.then("code").standsAtOrUnder(R.then("code")));
        assertTrue(PRESENT.standsAtOrUnder(R));
        assertTrue(R.standsAtOrUnder(PRESENT));
    }

    @Test
    void whatIsInsideAValueNarrowedToACaseIsUnderTheValue() {
        assertTrue(PRESENT.then("code").standsAtOrUnder(R));
        assertTrue(R.then("code").then("digit").standsAtOrUnder(PRESENT.then("code")));
        assertFalse(R.standsAtOrUnder(PRESENT.then("code")));
        assertFalse(PRESENT.then("code").standsAtOrUnder(R.then("code").then("digit")));
    }

    /** Which case a value is stands around whatever is asked under another case of it. */
    @Test
    void twoCasesOfOneValueAreNeitherUnderTheOther() {
        assertFalse(PRESENT.standsAtOrUnder(ABSENT));
        assertFalse(PRESENT.then("a").standsAtOrUnder(ABSENT));
        assertFalse(ABSENT.standsAtOrUnder(PRESENT.then("a")));
        assertFalse(PRESENT.then("a").standsAtOrUnder(ABSENT.then("b")));
    }

    @Test
    void placesApartAreNeitherUnderTheOther() {
        assertFalse(R.then("a").standsAtOrUnder(R.then("b")));
        assertFalse(PRESENT.then("a").standsAtOrUnder(R.then("b")));
        assertFalse(ITEMS.element().standsAtOrUnder(R.then("total")));
        assertFalse(R.standsAtOrUnder(TermPath.of("s")));
    }

    /** Two cases of one value bear on each other ({@link TermPath#bearsOn}), as each excludes the
     *  other, and neither stands at, under or around the other. */
    @Test
    void twoCasesOfOneValueBearOnEachOtherAndStandApart() {
        assertTrue(PRESENT.then("a").bearsOn(ABSENT.then("a")));
        assertFalse(PRESENT.then("a").standsAtUnderOrAround(ABSENT.then("a")));
        assertFalse(PRESENT.standsAtUnderOrAround(ABSENT.then("b")));
        assertTrue(PRESENT.then("a").standsAtUnderOrAround(R));
        assertTrue(R.then("a").standsAtUnderOrAround(PRESENT.then("a").then("b")));
    }

    /**
     * Over every pair of a set of places: a place at or under another step for step stands at or
     * under it; one stands at, under or around another where one of the two stands at or under the
     * other; and that bears on it ({@link TermPath#bearsOn}) — which, where neither stands at,
     * under or around the other, is two cases of one value.
     */
    @Test
    void itIsTheOneWayHalfOfBearingThatExtendsBeingInsideStepForStep() {
        List<TermPath> places = List.of(R, ITEMS, ITEMS.element(), ITEMS.element().then("price"),
                R.then("code"), R.then("code").then("digit"), PRESENT, ABSENT,
                PRESENT.then("code"), PRESENT.then("a"), ABSENT.then("b"), R.then("total"),
                TermPath.of("s"));
        for (TermPath one : places) {
            for (TermPath other : places) {
                String pair = one + " and " + other;
                if (one.isAtOrUnder(other)) {
                    assertTrue(one.standsAtOrUnder(other), pair);
                }
                assertEquals(one.standsAtOrUnder(other) || other.standsAtOrUnder(one),
                        one.standsAtUnderOrAround(other), pair);
                if (one.standsAtUnderOrAround(other)) {
                    assertTrue(one.bearsOn(other), pair);
                }
                if (one.bearsOn(other) && !one.standsAtUnderOrAround(other)) {
                    assertTrue(narrows(one) && narrows(other), pair);
                }
            }
        }
    }

    private static boolean narrows(TermPath path) {
        return path.steps().stream().anyMatch(step -> step instanceof TermPath.Step.Refine);
    }
}
