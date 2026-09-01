package souther.compiler.diag;

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
 * {@code row} and {@code rows}, and the bare types {@code Row} and {@code Rows}, are a row's. A row
 * of an {@code example} is a compiler type and this module is under the compiler, so there is
 * nothing here that could be one — the rule has no admitting side to state and the prohibition is
 * the whole of it.
 *
 * <p><b>Except what a message carries.</b> A {@link souther.compiler.diag.msg.Message} is a record
 * whose component names are read back by name: they are the placeholders a catalog entry writes
 * ({@code The row says {row}}), and they are the keys the JSON renderer puts a diagnostic's values
 * under. So a component called {@code row} is not this module calling something a row — it is the
 * word the sentence uses, in two languages and on a wire, and renaming it would move a published
 * key to say something about Java. Serialized vocabulary is outside this rule wherever it appears,
 * as a report's JSON key {@code "rows"} is.
 *
 * <p>Which is why the exception is taken from what a class implements rather than from a list of
 * the ones there are today. A message written next year carries the same wire and would otherwise
 * have to be remembered.
 *
 * <p><b>Its own module, not a walk over the reactor.</b> A check reaching across to a sibling's
 * {@code target/classes} would be reading whatever a previous build left there. Each module says
 * this about itself, over the classes it was just built into.
 */
class OnlyARowIsCalledARowTest {

    private static final Set<String> RESERVED_MEMBERS = Set.of("row", "rows");

    private static final Set<String> RESERVED_TYPES = Set.of("Row", "Rows");

    private static final String MESSAGE = "souther/compiler/diag/msg/Message";

    /** Nothing here is called {@code row} or {@code rows}, except what a message says. */
    @Test
    void nothingHereIsCalledARow() {
        List<String> wrong = new ArrayList<>();
        for (WhatAModuleDeclares.Declared each : compiled().taking(RESERVED_MEMBERS)) {
            if (!isAMessage(each.owner())) {
                wrong.add(each.shown());
            }
        }
        assertEquals(List.of(), wrong,
                "nothing under the compiler holds a row, so a declaration of it named for one is"
                        + " named for something it is not");
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
     * And the exception is over something.
     *
     * <p>A prohibition with an exception nothing meets is a prohibition, and this one is written
     * because messages do carry the word. Meeting nothing, it would be the wrong shape of rule and
     * nobody would find out.
     */
    @Test
    void andWhatAMessageSaysIsWhyThereIsAnException() {
        List<String> excused = new ArrayList<>();
        for (WhatAModuleDeclares.Declared each : compiled().taking(RESERVED_MEMBERS)) {
            if (isAMessage(each.owner())) {
                excused.add(each.shown());
            }
        }
        assertFalse(excused.isEmpty(), "a message carries the word this rule reserves");
    }

    /** Whether {@code of} is a message, whose component names are a catalog's and a wire's. */
    private static boolean isAMessage(ClassModel of) {
        return of.interfaces().stream()
                .anyMatch(each -> each.asInternalName().equals(MESSAGE)
                        || each.asInternalName().startsWith(MESSAGE + "$")
                        || implementsAMessage(each.asInternalName()));
    }

    private static boolean implementsAMessage(String internal) {
        for (ClassModel each : compiled().classes()) {
            if (each.thisClass().asInternalName().equals(internal)) {
                return each.interfaces().stream()
                        .anyMatch(one -> one.asInternalName().equals(MESSAGE));
            }
        }
        return false;
    }

    private static String simple(String internal) {
        String last = internal.substring(internal.lastIndexOf('/') + 1);
        return last.substring(last.lastIndexOf('$') + 1);
    }

    private static WhatAModuleDeclares compiled() {
        return WhatAModuleDeclares.of(Diagnostic.class);
    }
}
