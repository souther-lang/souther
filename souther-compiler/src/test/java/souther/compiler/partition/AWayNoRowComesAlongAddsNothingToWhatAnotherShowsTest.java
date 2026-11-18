package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.FilingCoordinate;
import souther.compiler.inputs.TermPath;

import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Rows that may come along either of two ways are what each shows together, and a way no row comes
 * along contributes no row: what the other shows stands. Of its own it shows nothing of any place:
 * every place is left undivided over rows there are none of, which shows none.
 */
class AWayNoRowComesAlongAddsNothingToWhatAnotherShowsTest {

    private static final FilingCoordinate X = FilingCoordinate.at(TermPath.of("x"));

    private static final UndividedByARelation.WhatItLeaves SHOWS_X =
            new UndividedByARelation.WhatItLeaves(Set.of(X), Map.of());

    private static final UndividedByARelation.WhatItLeaves NO_ROW =
            UndividedByARelation.WhatItLeaves.NO_ROW_COMES_ALONG;

    @Test
    void whatTheOtherShowsStandsWhicheverWayIsAskedFirst() {
        assertEquals(SHOWS_X, SHOWS_X.alongBoth(NO_ROW));
        assertEquals(SHOWS_X, NO_ROW.alongBoth(SHOWS_X));
    }

    @Test
    void whereNoRowComesAlongEitherNoRowComesAlongTheTwo() {
        assertEquals(NO_ROW, NO_ROW.alongBoth(NO_ROW));
    }

    @Test
    void aWayNoRowComesAlongShowsNoPlaceUndivided() {
        assertFalse(NO_ROW.rowsArrive());
        assertTrue(NO_ROW.undivided().isEmpty());
        assertTrue(NO_ROW.alsoUndivided(Set.of(X)).undivided().isEmpty());
        assertThrows(IllegalArgumentException.class,
                () -> new UndividedByARelation.WhatItLeaves(Set.of(X), Map.of(), false, Set.of()));
    }
}
