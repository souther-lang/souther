package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.Case;
import souther.compiler.inputs.Refinement;
import souther.compiler.inputs.TermPath;

import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A tie of the way is accounted for place by place: what accounts for the lengths of one string
 * is a claim made of that string, and a tie that reads another place the relation reads is not met
 * by it.
 */
class AStopOfTheWayIsAccountedForOnlyAtThePlacesWhoseLengthsAreAccountedForTest {

    private static final TermPath TAG = TermPath.of("tag");
    private static final TermPath OTHER = TermPath.of("other");
    private static final TermPath COUNT = TermPath.of("n");

    private static DemandReading.Tie between(TermPath... places) {
        return DemandReading.Tie.between(new LinkedHashSet<>(List.of(places)));
    }

    @Test
    void aTieOfAReadPlaceWhoseLengthsAreAccountedForIsAccountedFor() {
        assertTrue(UndividedByARelation.readsOnlyWhatIsAccountedFor(between(TAG, COUNT),
                List.of(TAG, OTHER), Set.of(TAG)));
    }

    @Test
    void aTieOfAReadPlaceNothingAccountsForIsNot() {
        assertFalse(UndividedByARelation.readsOnlyWhatIsAccountedFor(between(TAG, COUNT),
                List.of(TAG, OTHER), Set.of()));
    }

    /** What accounts for the other string's lengths is a claim made of the other string. */
    @Test
    void aTieOfAReadPlaceIsNotAccountedForByAnotherPlaceBeingSo() {
        assertFalse(UndividedByARelation.readsOnlyWhatIsAccountedFor(between(TAG, COUNT),
                List.of(TAG, OTHER), Set.of(OTHER)));
    }

    @Test
    void aTieOfTwoReadPlacesIsAccountedForOnlyWhereBothAre() {
        assertFalse(UndividedByARelation.readsOnlyWhatIsAccountedFor(between(TAG, OTHER),
                List.of(TAG, OTHER), Set.of(TAG)));
        assertTrue(UndividedByARelation.readsOnlyWhatIsAccountedFor(between(TAG, OTHER),
                List.of(TAG, OTHER), Set.of(TAG, OTHER)));
    }

    /**
     * A tie bears on a read as the value is reached, and what accounts for a place accounts only
     * for what is that place or inside it step for step: what is shown of a value narrowed to one
     * case is not shown of it narrowed to another, nor of the value, though each bears on the
     * other; and what is shown of what a value holds is not shown of the value.
     */
    @Test
    void whatAccountsForAPlaceAccountsForNoPlaceItOnlyBearsOn() {
        TermPath tagged = TermPath.of("t");
        TermPath one = tagged.refine(Refinement.of(new Case.Presence(true))).then("s");
        TermPath other = tagged.refine(Refinement.of(new Case.Presence(false))).then("s");
        TermPath unnarrowed = tagged.then("s");

        assertFalse(UndividedByARelation.readsOnlyWhatIsAccountedFor(between(other, COUNT),
                List.of(other), Set.of(one)));
        assertFalse(UndividedByARelation.readsOnlyWhatIsAccountedFor(between(unnarrowed, COUNT),
                List.of(unnarrowed), Set.of(one)));
        assertFalse(UndividedByARelation.readsOnlyWhatIsAccountedFor(between(TAG, COUNT),
                List.of(TAG), Set.of(TAG.element())));
        assertTrue(UndividedByARelation.readsOnlyWhatIsAccountedFor(between(TAG, COUNT),
                List.of(TAG.element()), Set.of(TAG)));
    }

    /** A tie of a value narrowed to a case bears on the value read without the narrowing. */
    @Test
    void aTieBearsOnAReadAsTheValueIsReached() {
        TermPath tagged = TermPath.of("t");
        TermPath narrowed = tagged.refine(Refinement.of(new Case.Presence(true))).then("s");

        assertFalse(UndividedByARelation.readsOnlyWhatIsAccountedFor(between(narrowed, COUNT),
                List.of(tagged.then("s")), Set.of()));
    }

    @Test
    void aTieThatNamesNoPlaceTheRelationReadsNeedsNoAccounting() {
        assertTrue(UndividedByARelation.readsOnlyWhatIsAccountedFor(between(COUNT),
                List.of(TAG, OTHER), Set.of()));
    }

    /** A tie is kept in a set of those a proof accounts for, so it is not changed after. */
    @Test
    void aTieKeepsTheOrderOfItsPlacesAndCannotBeChangedThroughThem() {
        Set<TermPath> made = new LinkedHashSet<>(List.of(COUNT, TAG));
        DemandReading.Tie tie = DemandReading.Tie.between(made);
        made.add(OTHER);

        assertEquals(List.of(COUNT, TAG), List.copyOf(tie.places()));
        assertThrows(UnsupportedOperationException.class, () -> tie.places().add(OTHER));
    }
}
