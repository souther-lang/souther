package souther.compiler.diag;

import org.junit.jupiter.api.Test;

import souther.test.TheBareRowNames;
import souther.test.WhatAModuleDeclares;

import java.lang.classfile.ClassModel;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Only a row is called a row.
 *
 * <p>The rule this repository holds every module to, said here about this one: the bare names
 * {@code row} and {@code rows}, and the bare types {@code Row} and {@code Rows}, are a row's. A row
 * of an {@code example} is a compiler type and this module is under the compiler, so there is
 * nothing here that could be one — the rule has no admitting side to state and the prohibition is
 * the whole of it.
 *
 * <p><b>Except a component of a message.</b> A {@link souther.compiler.diag.msg.Message} is a record
 * whose component names are read back by name: they are the placeholders a catalog entry writes
 * ({@code The row says {row}}), in every language it is written in, and the keys the JSON renderer
 * puts a diagnostic's values under. So a component called {@code row} is not this module calling
 * something a row — it is the word the sentence uses, on a wire, and renaming it would move a
 * published key to say something about Java. Serialized vocabulary is outside this rule wherever it
 * appears, as a report's JSON key {@code "rows"} is.
 *
 * <p>Which is the component and nothing beside it. A field or a method of a message goes by no
 * catalog and no wire, so the reason does not reach it, and excusing the class rather than the
 * component would excuse what the reason does not cover.
 *
 * <p>The exception is taken from what a class implements rather than from a list of the messages
 * there are today: one written next year carries the same wire and would otherwise have to be
 * remembered.
 */
class OnlyARowIsCalledARowTest {

    private static final String MESSAGE = "souther/compiler/diag/msg/Message";

    /** Nothing here is called {@code row} or {@code rows}, except what a message says. */
    @Test
    void nothingHereIsCalledARow() {
        assertEquals(List.of(), TheBareRowNames.takenIn(compiled(),
                        each -> each.kind() == WhatAModuleDeclares.Kind.RECORD_COMPONENT
                                && isAMessage(each.owner())),
                "nothing under the compiler holds a row, so a declaration of it named for one is"
                        + " named for something it is not");
    }

    /** And no type of it is called {@code Row} or {@code Rows}. */
    @Test
    void andNoTypeOfItIsCalledARow() {
        assertEquals(List.of(), TheBareRowNames.typesIn(compiled()),
                "a type called Row or Rows is a row, and none of these is");
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
        assertTrue(compiled().taking(TheBareRowNames.MEMBERS).stream()
                        .anyMatch(each -> each.kind() == WhatAModuleDeclares.Kind.RECORD_COMPONENT
                                && isAMessage(each.owner())),
                "a message carries the word this rule reserves");
    }

    /** Whether {@code of} is a message, whose component names are a catalog's and a wire's. */
    private static boolean isAMessage(ClassModel of) {
        return of.interfaces().stream()
                .anyMatch(each -> each.asInternalName().equals(MESSAGE)
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

    private static WhatAModuleDeclares compiled() {
        return WhatAModuleDeclares.of(Diagnostic.class);
    }
}
