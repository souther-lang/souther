package souther.build.driver;

import org.junit.jupiter.api.Test;

import souther.test.TheBareRowNames;
import souther.test.WhatAModuleDeclares;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * Only a row is called a row.
 *
 * <p>The rule this repository holds every module to, said here about this one. What this module
 * hands over is a compile and what it holds is the driving of one; a row of an {@code example} is
 * the compiler's, so the rule has no admitting side to state here and the prohibition is the whole
 * of it.
 *
 * <p>Written where nothing violates it, because where the next one will be written is not something
 * a boundary predicts.
 */
class OnlyARowIsCalledARowTest {

    /** Nothing here is called {@code row} or {@code rows}, because nothing here is a row. */
    @Test
    void nothingHereIsCalledARow() {
        assertEquals(List.of(), TheBareRowNames.takenIn(compiled(), _ -> false),
                "the build driver holds no rows, so a declaration of it named for one is named for"
                        + " something it is not");
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
        return WhatAModuleDeclares.of(CompilerBuildDriver.class);
    }
}
