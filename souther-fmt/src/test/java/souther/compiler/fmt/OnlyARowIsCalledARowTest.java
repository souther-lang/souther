package souther.compiler.fmt;

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
 * {@code example} is a compiler type and the formatter is not under the compiler, so there is
 * nothing here that could be one: the rule has no admitting side to state and the prohibition is
 * the whole of it. Declaring a row here would mean saying which type that is and what may hold one,
 * which is what the compiler's own copy of this does.
 *
 * <p><b>Its own module, not a walk over the reactor.</b> A check reaching across to a sibling's
 * {@code target/classes} would be reading whatever a previous build left there — the reactor builds
 * these in an order, so what is on disk beside a module at any moment is not what this run
 * compiled. Each module says this about itself, over the classes it was just built into.
 */
class OnlyARowIsCalledARowTest {

    /** Nothing here is called {@code row} or {@code rows}, because nothing here is a row. */
    @Test
    void nothingHereIsCalledARow() {
        assertEquals(List.of(), TheBareRowNames.takenIn(compiled(), _ -> false),
                "the formatter holds no rows, so a declaration of it named for one is named for"
                        + " something it is not");
    }

    /** And no type of it is called {@code Row} or {@code Rows}. */
    @Test
    void andNoTypeOfItIsCalledARow() {
        assertEquals(List.of(), TheBareRowNames.typesIn(compiled()),
                "a type called Row or Rows is a row, and none of these is");
    }

    /**
     * And both are over this module's classes rather than over nothing.
     *
     * <p>A prohibition passes on an empty answer, which is also what a reading that found no
     * classes would give. That the reading names every declaration of a name is held to where the
     * reading lives; what is asked here is that it was given this module to read.
     */
    @Test
    void andBothAreOverThisModule() {
        assertFalse(compiled().classes().isEmpty(), "the walk reads this module's classes");
    }

    private static WhatAModuleDeclares compiled() {
        return WhatAModuleDeclares.of(Columns.class);
    }
}
