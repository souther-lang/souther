package souther.architecture;

import org.junit.jupiter.api.Test;
import souther.compiler.types.BinOp;

import java.lang.classfile.ClassModel;
import java.lang.classfile.CodeElement;
import java.lang.classfile.CodeModel;
import java.lang.classfile.Instruction;
import java.lang.classfile.MethodModel;
import java.lang.classfile.Opcode;
import java.lang.classfile.instruction.BranchInstruction;
import java.lang.classfile.instruction.FieldInstruction;
import java.lang.classfile.instruction.InvokeInstruction;
import java.util.ArrayList;
import java.util.List;
import java.util.Optional;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What {@code &&} and {@code ||} do with their two sides is asked of the operator, and never read
 * off which of the two it is.
 *
 * <p>Two questions, each with one owner. When the right side runs is
 * {@link BinOp#rightRunsWhenLeftIs} (and {@link BinOp#stopsWhenItsAnswerIsSettled}); what the two
 * conditions come to together is {@code ConditionJoin}, and which operators join two at all
 * {@link BinOp#joinsTwoConditions}. A reader comparing an operator with {@code AND} or {@code OR}
 * writes one of those answers again, and one that writes when the right runs for itself can leave
 * it out, reading the right of {@code &&} as run on every run and sites no run reaches as reached.
 * A {@code switch} over every operator is not such a comparison: the language adding one stops
 * the build there.
 */
class WhatAnOperatorDoesWithItsTwoSidesIsAskedOfTheOperatorTest {

    private static final String OPERATOR = "souther/compiler/types/BinOp";
    private static final Set<String> CONNECTIVES = Set.of("AND", "OR");

    /** The owners themselves, the one place each answer is written. */
    private static final Set<String> OWNERS = Set.of(OPERATOR,
            "souther/compiler/semantics/ConditionJoin");

    @Test
    void noReaderComparesAnOperatorWithAConnective() {
        List<String> comparing = new ArrayList<>();
        for (ClassModel each : CompiledOutputs.ofWhatThisRepositoryPublishes().all()) {
            if (!OWNERS.contains(each.thisClass().asInternalName())) {
                comparing.addAll(comparisonsIn(each));
            }
        }
        assertEquals(List.of(), comparing,
                "ask the operator when its right side runs, or ConditionJoin what it joins,"
                        + " rather than which connective it is");
    }

    /** And the walk finds such a comparison where there is one, so the empty answer above means
     *  something. */
    @Test
    void theWalkFindsAComparisonWhereThereIsOne() {
        String name = Comparing.class.getName().replace('.', '/');
        Optional<ClassModel> fixture = CompiledOutputs.ofEverythingCompiledHere().find(name);
        assertTrue(fixture.isPresent(), "the fixture below is compiled here");
        assertEquals(List.of(name + "#stopsEarly"), comparisonsIn(fixture.get()));
    }

    /** A reader written the way this closes. */
    static final class Comparing {
        static boolean stopsEarly(BinOp op) {
            return op == BinOp.AND || op == BinOp.OR;
        }
    }

    /** Every method of {@code model} that compares something with a connective by identity or
     *  by {@code equals}. */
    private static List<String> comparisonsIn(ClassModel model) {
        Set<String> out = new TreeSet<>();
        for (MethodModel method : model.methods()) {
            Optional<CodeModel> code = method.code();
            if (code.isEmpty()) {
                continue;
            }
            int sinceAConnective = -1;
            for (CodeElement element : code.get()) {
                if (!(element instanceof Instruction instruction)) {
                    continue;
                }
                if (instruction instanceof FieldInstruction field
                        && field.opcode() == Opcode.GETSTATIC
                        && field.owner().asInternalName().equals(OPERATOR)
                        && CONNECTIVES.contains(field.name().stringValue())) {
                    sinceAConnective = 0;
                    continue;
                }
                if (sinceAConnective >= 0 && comparing(instruction)) {
                    out.add(model.thisClass().asInternalName() + "#"
                            + method.methodName().stringValue());
                }
                sinceAConnective = sinceAConnective < 0 || sinceAConnective >= 1 ? -1
                        : sinceAConnective + 1;
            }
        }
        return new ArrayList<>(out);
    }

    /** Whether {@code instruction} compares the two references on top of the stack. */
    private static boolean comparing(Instruction instruction) {
        return (instruction instanceof BranchInstruction branch
                && (branch.opcode() == Opcode.IF_ACMPEQ || branch.opcode() == Opcode.IF_ACMPNE))
                || (instruction instanceof InvokeInstruction invoke
                && invoke.name().stringValue().equals("equals"));
    }
}
