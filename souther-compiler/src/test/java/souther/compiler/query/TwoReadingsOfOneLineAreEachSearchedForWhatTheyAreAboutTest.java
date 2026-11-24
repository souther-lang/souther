package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.partition.Criterion;
import souther.compiler.partition.Level;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Two readings of one line read at one place are put together as one reading, and whether each
 * was searched at a point is each one's own.
 *
 * <p>The run beside the line can stop at a different line in each, so the point of the author's
 * line each is about there can differ, and one can be about a point a row meets while the other is
 * about one no row does. Put together, a search either made is a search of the point, and the point
 * is left unsearched only where neither searched, one left it, and no row stands at it.
 */
class TwoReadingsOfOneLineAreEachSearchedForWhatTheyAreAboutTest {

    private static final Criterion AT_ONE = new Criterion.AtTheLevel(Level.OfTheQuantity.of(1));

    @Test
    void oneLeftUnsearchedBesideOneSearchedIsAPointSearched() {
        for (ItemAssessment.Owed[] pair : new ItemAssessment.Owed[][] {
                {unsearched(), searched()}, {searched(), unsearched()}}) {
            ItemAssessment.Owed both = (ItemAssessment.Owed) Coverages.together(pair[0], pair[1]);
            assertTrue(both.searches().ran(), "the search one of them made is the point's");
            assertFalse(both.unneeded(), "and the point was searched, whichever came first");
        }
    }

    @Test
    void bothLeftUnsearchedIsAPointLeftUnsearched() {
        ItemAssessment.Owed both = (ItemAssessment.Owed) Coverages.together(unsearched(),
                unsearched());
        assertTrue(both.unneeded());
        assertFalse(both.searches().ran());
    }

    @Test
    void oneLeftUnsearchedBesideARowAtThePointIsNoSearchToLeave() {
        for (ItemAssessment.Owed[] pair : new ItemAssessment.Owed[][] {
                {unsearched(), aRowAtIt()}, {aRowAtIt(), unsearched()}}) {
            ItemAssessment.Owed both = (ItemAssessment.Owed) Coverages.together(pair[0], pair[1]);
            assertFalse(both.worthSearching(), "a row stands at the point");
            assertFalse(both.unneeded(), "so there was no search to leave");
        }
    }

    @Test
    void aPointIsLeftUnsearchedOnlyWhereItIsWorthAValueAndNothingWasSearched() {
        assertThrows(IllegalArgumentException.class, () -> new ItemAssessment.Owed(AT_ONE,
                rowAtIt(), ItemAssessment.WritabilityProjection.NOT_COMPUTED,
                SearchOutcomes.none(), true), "a point a row stands at");
        assertThrows(IllegalArgumentException.class, () -> new ItemAssessment.Owed(AT_ONE,
                noRows(), ItemAssessment.WritabilityProjection.NOT_COMPUTED,
                SearchOutcomes.of(attempt()), true), "a point searched");
    }

    private static ItemAssessment.Owed unsearched() {
        return new ItemAssessment.Owed(AT_ONE, noRows(),
                ItemAssessment.WritabilityProjection.NOT_COMPUTED, SearchOutcomes.none(), true);
    }

    private static ItemAssessment.Owed searched() {
        return new ItemAssessment.Owed(AT_ONE, noRows(),
                ItemAssessment.WritabilityProjection.NOT_COMPUTED, SearchOutcomes.of(attempt()),
                false);
    }

    private static ItemAssessment.Owed aRowAtIt() {
        return new ItemAssessment.Owed(AT_ONE, rowAtIt(),
                ItemAssessment.WritabilityProjection.NOT_COMPUTED, SearchOutcomes.none(), false);
    }

    private static Measurement<ItemAssessment.Coverage> noRows() {
        return new Measurement.NotMeasured<>(ItemAssessment.Coverage.NotAsked.NO_ROWS);
    }

    private static Measurement<ItemAssessment.Coverage> rowAtIt() {
        return new Measurement.Complete<>(new ItemAssessment.Coverage.Hit(RowWitnesses.ANOTHER_ROW));
    }

    private static ItemAssessment.Attempt attempt() {
        return new ItemAssessment.Attempt.Unavailable(ItemAssessment.Attempt.Reason.NO_CLASSES);
    }
}
