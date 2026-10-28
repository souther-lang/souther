package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A line drawn on several applications of one comparison is told the operations of the
 * applications together: a row arrives along one of them, so what one application told is not what
 * a row of another gets past.
 */
class WhatSeveralReadingsOfOneRelationTellTogetherTest {

    @Test
    void readingsThatAgreeTellWhatTheyAgreeOn() {
        UndividedByARelation.Working same = UndividedByARelation.Working.NOTHING;
        assertEquals(same, UndividedByARelation.Working.together(List.of(same, same)));
    }

    @Test
    void readingsThatDifferTellNothingThatHoldsOfEveryRow() {
        assertEquals(UndividedByARelation.Working.UNREAD,
                UndividedByARelation.Working.together(List.of(
                        UndividedByARelation.Working.NOTHING,
                        UndividedByARelation.Working.UNREAD)));
    }
}
