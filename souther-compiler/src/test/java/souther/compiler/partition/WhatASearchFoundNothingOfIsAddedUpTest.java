package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Which of the three ways a search comes back with nothing, and the order between them.
 *
 * <p>The rule is short and is the whole of what a caller may say when it found nothing, so it is
 * asked here rather than at each search. Written at each of them, a search that had stopped and one
 * that had tried everything ended in the same sentence — and the two send a reader to different
 * work: one to widen a search, the other to change a rule.
 */
class WhatASearchFoundNothingOfIsAddedUpTest {

    /** Nothing was searched, which is not a search that came back empty. */
    @Test
    void withNoReadingThereWasNoSearch() {
        assertEquals(Completeness.Nothing.NO_READING, Completeness.NOTHING_YET.found());
    }

    /** Every reading searched until its candidates ran out. */
    @Test
    void everyReadingSearchedToTheEndIsHavingLookedEverywhere() {
        assertEquals(Completeness.Nothing.LOOKED_EVERYWHERE,
                Completeness.NOTHING_YET.searched().searched().found());
    }

    /**
     * One reading stopped is the search having stopped, whatever the others came to.
     *
     * <p>Both ways round, because this is the one place the order between them is decided. A search
     * with candidates it never tried is incomplete however many of its other readings were walked to
     * the end, and read the other way it would answer "everything was refused" over a space it never
     * entered.
     */
    @Test
    void oneReadingCutShortIsTheSearchHavingStopped() {
        assertEquals(Completeness.Nothing.SEARCH_STOPPED,
                Completeness.NOTHING_YET.searched().cutShort().searched().found(),
                "a reading searched after the one that stopped does not undo the stopping");
        assertEquals(Completeness.Nothing.SEARCH_STOPPED,
                Completeness.NOTHING_YET.cutShort().searched().found());
    }

    /** A reading that was stopped is still a reading that was searched. */
    @Test
    void aReadingThatWasStoppedIsStillOneThatWasSearched() {
        assertEquals(new Completeness(true, true), Completeness.NOTHING_YET.cutShort(),
                "the bound stopped a search rather than saying there was none");
    }
}
