package souther.test;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * Only a row is called a row.
 *
 * <p>The rule this repository holds every module to, said here about this one — including about the
 * module the rule's own spelling lives in. What is checked is {@link TheBareRowNames} and what does
 * the checking is {@link TheBareRowNames}, which is the same arrangement as a compiler compiling
 * itself: it does not make the answer true, and it does mean the rule is not written somewhere it
 * exempts.
 */
class OnlyARowIsCalledARowTest {

    /** Nothing here is called {@code row} or {@code rows}, because nothing here is a row. */
    @Test
    void nothingHereIsCalledARow() {
        assertEquals(List.of(), TheBareRowNames.takenIn(compiled(), _ -> false),
                "what a test is given holds no rows, so a declaration of it named for one is named"
                        + " for something it is not");
    }

    /** And no type of it is called {@code Row} or {@code Rows}. */
    @Test
    void andNoTypeOfItIsCalledARow() {
        assertEquals(List.of(), TheBareRowNames.typesIn(compiled()),
                "a type called Row or Rows is a row, and none of these is");
    }

    /** And both are over this module's classes rather than over nothing. */
    @Test
    void andBothAreOverThisModule() {
        assertFalse(compiled().classes().isEmpty(), "the walk reads this module's classes");
    }

    private static WhatAModuleDeclares compiled() {
        return WhatAModuleDeclares.of(RepositoryLayout.class);
    }
}
