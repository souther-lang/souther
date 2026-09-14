package souther.runtime;

import org.junit.jupiter.api.Test;

import souther.test.TheBareRowNames;
import souther.test.WhatAModuleDeclares;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * Only a row is called a row.
 *
 * <p>The rule this repository holds every module to, said here about this one. A row of an
 * {@code example} is a compiler type and the run time does not reach the compiler, so there is
 * nothing here that could be one: the rule has no admitting side to state and the prohibition is
 * the whole of it.
 *
 * <p>Written where nothing violates it, because where the next one will be written is not something
 * a boundary predicts. The two this branch found were in modules nobody had looked at, and guarding
 * only the modules a census turned something up in is making the census the rule.
 *
 * <p><b>Its own module, not a walk over the reactor.</b> A check reaching across to a sibling's
 * {@code target/classes} would be reading whatever a previous build left there. Each module says
 * this about itself, over the classes it was just built into.
 */
class OnlyARowIsCalledARowTest {

    /** Nothing here is called {@code row} or {@code rows}, because nothing here is a row. */
    @Test
    void nothingHereIsCalledARow() {
        assertEquals(List.of(), TheBareRowNames.takenIn(compiled(), _ -> false),
                "the run time holds no rows, so a declaration of it named for one is named for"
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
        return WhatAModuleDeclares.of(Behavior.class);
    }
}
