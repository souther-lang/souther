package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A relation of a quantity to a place implies another facing the same way when its place is
 * further out, or at the same place when it is the stricter.
 */
class WhatARelationToAPlaceImpliesTest {

    private static final int FURTHER = 1;
    private static final int SAME = 0;
    private static final int NEARER = -1;

    @Test
    void aLowerBoundFurtherUpImpliesOneNearer() {
        assertTrue(StatementsOnClasses.follows(true, false, false, FURTHER));
        assertFalse(StatementsOnClasses.follows(true, false, false, NEARER));
    }

    @Test
    void anUpperBoundFurtherDownImpliesOneNearer() {
        assertTrue(StatementsOnClasses.follows(false, false, false, NEARER));
        assertFalse(StatementsOnClasses.follows(false, false, false, FURTHER));
    }

    @Test
    void atOnePlaceTheStricterImpliesTheOtherAndNotTheReverse() {
        assertTrue(StatementsOnClasses.follows(true, true, false, SAME));
        assertFalse(StatementsOnClasses.follows(true, false, true, SAME));
        assertTrue(StatementsOnClasses.follows(false, true, false, SAME));
        assertFalse(StatementsOnClasses.follows(false, false, true, SAME));
    }

    @Test
    void atOnePlaceRelationsOfOneStrictnessImplyEachOther() {
        assertTrue(StatementsOnClasses.follows(true, false, false, SAME));
        assertTrue(StatementsOnClasses.follows(true, true, true, SAME));
    }
}
