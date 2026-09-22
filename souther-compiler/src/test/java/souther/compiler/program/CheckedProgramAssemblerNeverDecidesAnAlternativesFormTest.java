package souther.compiler.program;

import souther.compiler.WhatWasCompiled;

import org.junit.jupiter.api.Test;

import java.lang.classfile.ClassModel;
import java.lang.classfile.constantpool.MethodRefEntry;
import java.lang.classfile.constantpool.PoolEntry;
import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * {@link CheckedProgramAssembler} never calls {@code Boundary.of} — whether a set of alternatives
 * is a bare tag or a discriminated object is asked of the store ({@code query.Shapes.TypeAlternatives}),
 * which answers it once, never settled a second time by the one place that projects it onto what an
 * output outside this compiler reads.
 *
 * <p>Held syntactically and not by reading, for the reason {@code TheBoundaryRepresentationIsHeldWhereItWasDerivedTest}
 * gives for the same choice: a shape is what a later change reaches for first, and a call to
 * {@code Boundary.of} added back here — to save a query round trip, say — would be exactly that,
 * with nothing above it saying why it should not be there.
 */
class CheckedProgramAssemblerNeverDecidesAnAlternativesFormTest {

    @Test
    void noCallToBoundaryOfIsCompiledIntoTheAssembler() {
        List<String> found = new ArrayList<>();
        for (ClassModel model : WhatWasCompiled.compiled().all()) {
            if (!model.thisClass().asInternalName()
                    .equals("souther/compiler/program/CheckedProgramAssembler")) {
                continue;
            }
            for (PoolEntry entry : model.constantPool()) {
                if (entry instanceof MethodRefEntry ref
                        && ref.owner().asInternalName().equals("souther/compiler/check/Boundary")
                        && ref.name().stringValue().equals("of")) {
                    found.add(model.thisClass().asInternalName());
                }
            }
        }
        assertEquals(List.of(), found,
                "CheckedProgramAssembler calls Boundary.of directly, which is the program-facing"
                        + " assembler deciding a Type -> answer question that the check stage answers"
                        + " once and this is meant only to project");
    }
}
