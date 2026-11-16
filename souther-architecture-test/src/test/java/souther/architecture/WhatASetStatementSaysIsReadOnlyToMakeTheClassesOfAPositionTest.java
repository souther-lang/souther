package souther.architecture;

import org.junit.jupiter.api.Test;

import java.lang.classfile.ClassModel;
import java.lang.classfile.CodeElement;
import java.lang.classfile.MethodModel;
import java.lang.classfile.instruction.InvokeInstruction;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Who reads the strings a rule's statement puts on each side of a position, and what it does with
 * them.
 *
 * <p>The sets of a statement are over strings with no greatest length (ADR-0130), so they say what
 * is so of the strings without that edge, and are not a proof that a value is there to be had. They
 * make an obligation: a class a row is owed for. A reader that took them as a proof of something
 * met would go wrong exactly at the edge — a string the unlimited world gives a partner and no
 * value does would be shown to have one — so what meets an obligation is a row that ran, and no
 * set of a statement stands in for one.
 *
 * <p>The class and not the method: what a reader does with a statement is a fact about the reader.
 * A reader that is not here has not said, and it says so here before it reads one.
 */
class WhatASetStatementSaysIsReadOnlyToMakeTheClassesOfAPositionTest {

    private static final CompiledOutputs COMPILED = CompiledOutputs.ofWhatThisRepositoryPublishes();

    private static final String STATEMENT = "souther/compiler/partition/SetStatement";

    /** What a statement says, which is what the classes of a position are made of. */
    private static final Set<String> SAYS = Set.of("whenTrue", "whenFalse", "notShown",
            "notReached", "notCounted");

    /** Who reads it, and what it makes of it. */
    private static final Map<String, String> READERS = Map.of(
            "souther/compiler/partition/Classing",
            "makes the classes of a position out of the strings on each side, which are the"
                    + " obligations a row is owed for; what meets one is a row that ran, which is"
                    + " no reader of a statement");

    @Test
    void everyReaderOfWhatAStatementSaysHasSaidWhatItDoesWithIt() {
        TreeSet<String> readers = new TreeSet<>();
        for (ClassModel each : COMPILED.all()) {
            String caller = each.thisClass().asInternalName();
            if (caller.equals(STATEMENT) || caller.startsWith(STATEMENT + "$")) {
                continue;
            }
            for (MethodModel method : each.methods()) {
                method.code().ifPresent(code -> {
                    for (CodeElement element : code) {
                        if (element instanceof InvokeInstruction invoked
                                && invoked.owner().name().stringValue().equals(STATEMENT)
                                && SAYS.contains(invoked.name().stringValue())) {
                            readers.add(caller);
                        }
                    }
                });
            }
        }

        assertEquals(new TreeSet<>(READERS.keySet()), readers,
                "a reader of the strings a statement puts on each side is one that has said what it"
                        + " does with them, which is never to take them for a value that is there: "
                        + READERS);
    }
}
