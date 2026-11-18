package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.core.Core;
import souther.compiler.diag.SourcePos;
import souther.compiler.inputs.WhatARelationLeavesUndivided.Told;
import souther.compiler.types.Type;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What a reading met and could place nowhere is carried by the working it was told in, through
 * everything that makes one working of several or of one, so that a reading that stands in for
 * another does not leave it behind ({@link UndividedByARelation.Working#unplaced}).
 */
class AWorkingKeepsWhatNoReadingAnsweredForTest {

    private static final Core NODE = new Core.Int(1, Type.INT, new SourcePos(1, 1));

    private static final UndividedByARelation.Working LEAVING = new UndividedByARelation.Working(
            List.of(), Told.SOME, true, List.of(), List.of(NODE));

    private static final UndividedByARelation.Working SOME =
            new UndividedByARelation.Working(List.of(), Told.SOME);

    @Test
    void itIsKeptWhereARunWorksOutWhatItLeavesAfterOtherThings() {
        assertEquals(List.of(NODE), SOME.after(LEAVING).unplaced());
        assertEquals(List.of(NODE), LEAVING.after(SOME).unplaced());
    }

    @Test
    void itIsKeptForARelationNotEveryRunReaches() {
        assertEquals(List.of(NODE), LEAVING.notOnEveryRun().unplaced());
    }

    @Test
    void itIsKeptWhereReadingsAgreeAndWhereTheyDoNot() {
        assertEquals(List.of(NODE),
                UndividedByARelation.Working.together(List.of(SOME, LEAVING)).unplaced());
        UndividedByARelation.Working told =
                new UndividedByARelation.Working(List.of(), Told.EVERY);
        assertEquals(List.of(NODE),
                UndividedByARelation.Working.together(List.of(told, LEAVING)).unplaced());
    }
}
