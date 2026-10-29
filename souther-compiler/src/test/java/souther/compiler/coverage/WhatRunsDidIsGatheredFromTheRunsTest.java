package souther.compiler.coverage;

import org.junit.jupiter.api.Test;
import souther.compiler.WhatWasCompiled;

import java.lang.classfile.ClassModel;
import java.lang.classfile.MethodModel;
import java.lang.classfile.instruction.InvokeInstruction;
import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What the runs of a module did is gathered from the runs, and by nothing that writes the places
 * down itself.
 *
 * <p>{@link ReachEvidence#of} takes the places a reading is corrected by as they are written, which
 * is what a test needs to put a reading a run it never had. A method of the compiler calling it
 * would be a reader that decides which kinds of place to hand over, which is the omission
 * {@link ReachEvidence#ofRuns} exists to make impossible: a kind left out reads as a kind no run
 * did.
 *
 * <p>Read off the compiled classes of this module, so a reader written in the CLI or the language
 * server would not be counted here.
 */
class WhatRunsDidIsGatheredFromTheRunsTest {

    private static final String EVIDENCE = "souther/compiler/coverage/ReachEvidence";

    @Test
    void noMethodOfTheCompilerWritesTheEvidenceDown() {
        List<String> writers = new ArrayList<>();
        for (ClassModel model : WhatWasCompiled.compiled().all()) {
            String from = model.thisClass().asInternalName().replace('/', '.').replace('$', '.');
            for (MethodModel method : model.methods()) {
                method.code().ifPresent(code -> code.forEach(element -> {
                    if (element instanceof InvokeInstruction call
                            && call.owner().asInternalName().equals(EVIDENCE)
                            && call.name().stringValue().equals("of")) {
                        writers.add(from + "." + method.methodName().stringValue());
                    }
                }));
            }
        }
        assertEquals(List.of(), writers,
                "evidence of what runs did is made from the runs, with ReachEvidence.ofRuns");
    }
}
