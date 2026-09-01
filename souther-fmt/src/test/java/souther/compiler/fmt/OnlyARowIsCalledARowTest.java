package souther.compiler.fmt;

import org.junit.jupiter.api.Test;

import souther.test.WhatAModuleDeclares;

import java.lang.classfile.ClassModel;
import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * Only a row is called a row.
 *
 * <p>The same rule the compiler holds itself to, said here about this module: the bare names
 * {@code row} and {@code rows}, and the bare types {@code Row} and {@code Rows}, are a row's.
 * Everything that is merely about one — what a row is written as, where it starts, how wide it is —
 * says what it is instead.
 *
 * <p><b>Nothing here may take them at all.</b> A row of an {@code example} is a compiler type, and
 * this module does not depend on the compiler; there is nothing it could hold that is a row. So the
 * rule has no admitting side to state, and the prohibition is the whole of it. Declaring a row here
 * would mean saying which type that is, and then saying what may hold one — which is what the
 * compiler's own copy of this does.
 *
 * <p><b>Its own module, not a walk over the reactor.</b> A check reaching across to a sibling's
 * {@code target/classes} would be reading whatever a previous build left there: the reactor builds
 * this module after the compiler and before nothing, so what exists beside it at any moment is not
 * what this run compiled. Each module says this about itself, over the classes it was just built
 * into.
 */
class OnlyARowIsCalledARowTest {

    private static final Set<String> RESERVED_MEMBERS = Set.of("row", "rows");

    private static final Set<String> RESERVED_TYPES = Set.of("Row", "Rows");

    /** Nothing here is called {@code row} or {@code rows}, because nothing here is a row. */
    @Test
    void nothingHereIsCalledARow() {
        List<String> wrong = new ArrayList<>();
        for (WhatAModuleDeclares.Declared each : compiled().taking(RESERVED_MEMBERS)) {
            wrong.add(each.shown());
        }
        assertEquals(List.of(), wrong,
                "the formatter holds no rows, so a declaration of it named for one is named for"
                        + " something it is not");
    }

    /** And no type of it is called {@code Row} or {@code Rows}. */
    @Test
    void andNoTypeOfItIsCalledARow() {
        List<String> wrong = new ArrayList<>();
        for (ClassModel each : compiled().classes()) {
            String internal = each.thisClass().asInternalName();
            if (RESERVED_TYPES.contains(simple(internal))) {
                wrong.add(internal);
            }
        }
        assertEquals(List.of(), wrong, "a type called Row or Rows is a row, and none of these is");
    }

    /**
     * And both are over this module's classes rather than over nothing.
     *
     * <p>The prohibition passes on an empty answer, which is also what a reading that found no
     * declarations at all would give. So it is asked for a name this module does have — the other
     * half of the stop that started this — and the two answers together say the reading works and
     * the reserved name is not in it.
     */
    @Test
    void andBothAreOverThisModule() {
        assertFalse(compiled().classes().isEmpty(), "the walk reads this module's classes");
        assertFalse(compiled().taking(Set.of("connector")).isEmpty(),
                "and reads the declarations of them");
    }

    private static String simple(String internal) {
        String last = internal.substring(internal.lastIndexOf('/') + 1);
        return last.substring(last.lastIndexOf('$') + 1);
    }

    private static WhatAModuleDeclares compiled() {
        return WhatAModuleDeclares.of(Columns.class);
    }
}
