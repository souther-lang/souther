package souther.architecture;

import org.junit.jupiter.api.Test;

import java.lang.classfile.ClassModel;
import java.lang.classfile.CodeModel;
import java.lang.classfile.MethodModel;
import java.lang.classfile.Opcode;
import java.lang.classfile.instruction.FieldInstruction;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * Whether a reading of a comparison told every operation that may end a run, and whether it left
 * a stop untold, are written by what the reading told and by nothing else.
 *
 * <p>The two are one fact read two ways: an operation left out of what was told is a stop told by
 * nothing, unless its owner shows working it out ends none. Written apart, one was set without the
 * other — an operation dropped from what was told and no stop said — and the report said nothing
 * of a run that stopped. So each is written only by the operations of what was told that say
 * which it was ({@code WhatWasTold#passedOver} and the ones beside it), and a reader that left
 * something out goes through one of them.
 *
 * <p>Read off the compiled classes: a write is a {@code putfield} however the source spells it,
 * and a nested class's private field is written by its outer class without a word in between.
 */
class WhatAReadingLeavesUntoldIsWrittenByWhatItToldTest {

    private static final CompiledOutputs COMPILED = CompiledOutputs.ofWhatThisRepositoryPublishes();

    private static final String TOLD = "souther/compiler/partition/AffineReading$WhatWasTold";

    private static final Set<String> FLAGS = Set.of("exact", "aStopUntold");

    @Test
    void theFlagsAreWrittenOnlyByWhatWasTold() {
        TreeSet<String> written = new TreeSet<>();
        int found = 0;
        for (ClassModel each : COMPILED.all()) {
            String owner = each.thisClass().asInternalName();
            for (MethodModel method : each.methods()) {
                CodeModel code = method.code().orElse(null);
                if (code == null) {
                    continue;
                }
                for (var element : code) {
                    if (element instanceof FieldInstruction field
                            && field.opcode() == Opcode.PUTFIELD
                            && field.owner().asInternalName().equals(TOLD)
                            && FLAGS.contains(field.name().stringValue())) {
                        found++;
                        if (!owner.equals(TOLD)) {
                            written.add(owner + "#" + method.methodName().stringValue()
                                    + " writes " + field.name().stringValue());
                        }
                    }
                }
            }
        }
        assertFalse(found == 0, "no write of the flags was found, so this asked nothing");
        assertEquals(new TreeSet<String>(), written,
                "a flag of what a reading told is written outside what was told: say what was"
                        + " left out through WhatWasTold#passedOver or the operations beside it");
    }
}
