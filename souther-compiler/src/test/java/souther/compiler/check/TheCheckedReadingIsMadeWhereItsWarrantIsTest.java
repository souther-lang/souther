package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.WhatWasCompiled;

import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * What the check settled is answered to a reading that has one, and is not there for the asking.
 *
 * <p>{@link CheckedDeclarations} does one thing no other reading of the declarations may: a
 * declaration it can see that the check settled nothing about is a broken world rather than a value
 * with no fields. That is true of a reading downstream of the module having checked, and false of
 * every other — a measurement of a module that did not check reaches declarations the check said
 * nothing about, and turning one of those into a fault would report a compiler defect where the
 * answer is that nothing could be measured.
 *
 * <p>So the warrant is where the reading is made, and this is what says it stays there. Written as
 * a rule about who may build one rather than as a sentence in a javadoc: the caller that wanders in
 * with a {@code Db} and a scope is the one this exists to stop, and it will be written by whoever
 * has neither this file nor that javadoc in front of them.
 *
 * <p>Read off the class files. A constructor call is in the calling class's constant pool whatever
 * it is spelled like, and a lambda's body is compiled into the class that wrote it, so a caller
 * cannot get out of this by writing the call somewhere shorter.
 */
class TheCheckedReadingIsMadeWhereItsWarrantIsTest {

    /**
     * The reading that has the warrant: what runs a module's rows, which answers nothing at all
     * where the module did not check.
     *
     * <p>The snapshot's own reading of the same thing is not here because Java already says it —
     * what a checked program's declarations are made of is answered by a type of that package that
     * nothing outside it can build, and it is built after the language's verdict is asked for.
     */
    private static final List<String> WARRANTED =
            List.of("souther.compiler.query.ExampleExecutions");

    @Test
    void onlyAReadingDownstreamOfACheckBuildsOne() {
        assertEquals(List.of(), WhatWasCompiled.callersOf(CheckedDeclarations.class, "<init>")
                .stream().filter(each -> !WARRANTED.contains(each)).toList(),
                "a reading with no warrant for it built what the check settled");
    }

    /**
     * And the rule is about something: one of them does build one.
     *
     * <p>A walk that reached nothing answers the same as one that reached everything and found
     * nothing wrong with it.
     */
    @Test
    void andOneOfThemDoes() {
        Set<String> builders = WhatWasCompiled.callersOf(CheckedDeclarations.class, "<init>");
        assertFalse(builders.isEmpty(), "nothing builds it, so the rule above saw no classes");
    }
}
