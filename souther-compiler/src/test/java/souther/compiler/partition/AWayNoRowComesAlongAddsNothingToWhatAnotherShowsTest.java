package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.FilingCoordinate;
import souther.compiler.inputs.TermPath;

import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Rows that may come along either of two ways are what each shows together, and a way no row comes
 * along contributes no row: what the other shows stands.
 */
class AWayNoRowComesAlongAddsNothingToWhatAnotherShowsTest {

    private static final FilingCoordinate X = FilingCoordinate.at(TermPath.of("x"));

    private static final UndividedByARelation.WhatItLeaves SHOWS_X =
            new UndividedByARelation.WhatItLeaves(Set.of(X), Map.of());

    private static final UndividedByARelation.WhatItLeaves NO_ROW =
            UndividedByARelation.WhatItLeaves.ofAWayNoRowComesAlong(Set.of(X));

    @Test
    void whatTheOtherShowsStandsWhicheverWayIsAskedFirst() {
        assertEquals(SHOWS_X, SHOWS_X.alongBoth(NO_ROW));
        assertEquals(SHOWS_X, NO_ROW.alongBoth(SHOWS_X));
    }

    @Test
    void whereNoRowComesAlongEitherNoRowComesAlongTheTwo() {
        assertEquals(NO_ROW, NO_ROW.alongBoth(NO_ROW));
    }
}
