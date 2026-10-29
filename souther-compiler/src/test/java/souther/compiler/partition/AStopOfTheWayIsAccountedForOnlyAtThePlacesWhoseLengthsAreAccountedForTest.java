package souther.compiler.partition;

import org.junit.jupiter.api.Test;

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
