package souther.lsp;

import org.junit.jupiter.api.Test;

import souther.test.TheBareRowNames;
import souther.test.WhatAModuleDeclares;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * Only a row is called a row.
 *
 * <p>The rule this repository holds every module to, said here about this one. This module asks the
 * compiler about rows and hands an editor what it answered; what it holds of its own is an
 * editor's, so the rule has no admitting side to state here and the prohibition is the whole of it.
 *
 * <p>Which is the case the rule is most worth having in: a reader here meets both vocabularies at
 * once, and a name that says row while holding an offer, a count or a position is read as the
 * compiler's word for a line.
 */
class OnlyARowIsCalledARowTest {

    /** Nothing here is called {@code row} or {@code rows}, because nothing here is a row. */
    @Test
    void nothingHereIsCalledARow() {
        assertEquals(List.of(), TheBareRowNames.takenIn(compiled(), _ -> false),
                "the language server holds no rows of its own, so a declaration of it named for one"
                        + " is named for something it is not");
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
        return WhatAModuleDeclares.of(LspMethod.class);
    }
}
