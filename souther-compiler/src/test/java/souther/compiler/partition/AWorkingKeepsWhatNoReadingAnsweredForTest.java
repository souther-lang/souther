package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.WhatARelationLeavesUndivided.Told;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A stop a reading left untold is carried by the working it was told in, through everything that
 * makes one working of several or of one, so that a reading that stands in for another does not
 * leave it behind ({@link UndividedByARelation.Working#aStopUntold}).
 */
class AWorkingKeepsWhatNoReadingAnsweredForTest {

    private static final UndividedByARelation.Working LEAVING = new UndividedByARelation.Working(
            List.of(), Told.SOME, true, List.of(), true);

    private static final UndividedByARelation.Working SOME =
            new UndividedByARelation.Working(List.of(), Told.SOME);

    @Test
    void itIsKeptWhereARunWorksOutWhatItLeavesAfterOtherThings() {
        assertTrue(SOME.after(LEAVING).aStopUntold());
        assertTrue(LEAVING.after(SOME).aStopUntold());
    }

    @Test
    void itIsKeptForARelationNotEveryRunReaches() {
        assertTrue(LEAVING.notOnEveryRun().aStopUntold());
    }

    @Test
    void itIsKeptWhereReadingsAgreeAndWhereTheyDoNot() {
        assertTrue(UndividedByARelation.Working.together(List.of(SOME, LEAVING)).aStopUntold());
        UndividedByARelation.Working told =
                new UndividedByARelation.Working(List.of(), Told.EVERY);
        assertTrue(UndividedByARelation.Working.together(List.of(told, LEAVING)).aStopUntold());
    }
}
