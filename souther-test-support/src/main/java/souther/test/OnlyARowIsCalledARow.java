package souther.test;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * Only a row is called a row, said about a module that declares no row type.
 *
 * <p>Only the compiler declares a row, so every other module has no admitting side to state and the
 * prohibition is the whole of the rule. Each such module extends this once in its own tests, naming
 * one of its own classes, so the check reads the classes that module was just built into rather
 * than whatever a previous build left beside a sibling.
 */
public abstract class OnlyARowIsCalledARow {

    private final Class<?> anchor;
    private final String holdsNoRows;

    /**
     * @param anchor      a class of the module under the rule
     * @param holdsNoRows what the module is, said as holding no rows, for the failure message
     */
    protected OnlyARowIsCalledARow(Class<?> anchor, String holdsNoRows) {
        this.anchor = anchor;
        this.holdsNoRows = holdsNoRows;
    }

    /** Nothing here is called {@code row} or {@code rows}, because nothing here is a row. */
    @Test
    public void nothingHereIsCalledARow() {
        assertEquals(List.of(), TheBareRowNames.takenIn(compiled(), _ -> false),
                holdsNoRows + ", so a declaration of it named for one is named for something it is"
                        + " not");
    }

    /** And no type of it is called {@code Row} or {@code Rows}. */
    @Test
    public void andNoTypeOfItIsCalledARow() {
        assertEquals(List.of(), TheBareRowNames.typesIn(compiled()),
                "a type called Row or Rows is a row, and none of these is");
    }

    /**
     * And both are over this module's classes rather than over nothing.
     *
     * <p>A prohibition passes on an empty answer, which is also what a reading that found no
     * classes would give. What is asked here is that the reading was given this module to read.
     */
    @Test
    public void andBothAreOverThisModule() {
        assertFalse(compiled().classes().isEmpty(), "the walk reads this module's classes");
    }

    private WhatAModuleDeclares compiled() {
        return WhatAModuleDeclares.of(anchor);
    }
}
