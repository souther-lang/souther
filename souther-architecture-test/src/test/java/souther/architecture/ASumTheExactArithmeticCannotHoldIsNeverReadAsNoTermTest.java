package souther.architecture;

import org.junit.jupiter.api.Test;

import java.lang.classfile.ClassModel;
import java.lang.classfile.Instruction;
import java.lang.classfile.MethodModel;
import java.lang.classfile.Opcode;
import java.lang.classfile.instruction.InvokeDynamicInstruction;
import java.lang.classfile.instruction.InvokeInstruction;
import java.lang.constant.ConstantDesc;
import java.lang.constant.DirectMethodHandleDesc;
import java.util.ArrayList;
import java.util.List;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * A sum of two coefficients that the exact arithmetic cannot hold is not a term that is gone.
 *
 * <p>{@code Map.merge} drops the key when the function it is handed answers null. A sum written as
 * {@code before.plus(now).orNull()} answers null for a sum that went unheld, so a merge of two
 * weights of one atom drops the atom — and a form without an atom is a form that says nothing of
 * it, which is a relation with a term taken out and not a relation that could not be written. The
 * answer a reader must have of a failed sum is that it failed, and it is the caller of the merge
 * that can say so: it looks at what the merge answered and stops there.
 *
 * <p>So a merge whose function turns an unheld sum into null is held to its answer being looked at.
 * The answer thrown away — a {@code pop} after the call — is the sum lost without a word.
 *
 * <p>Read off the compiled classes of what this repository publishes: the method that calls
 * {@code merge} hands it a lambda, and the lambda is a method of the same class that calls
 * {@code orNull}.
 */
class ASumTheExactArithmeticCannotHoldIsNeverReadAsNoTermTest {

    private static final CompiledOutputs COMPILED = CompiledOutputs.ofWhatThisRepositoryPublishes();

    @Test
    void noMergeThatTurnsAFailedSumIntoNullThrowsItsAnswerAway() {
        assertEquals(List.of(), mergesThatLoseAFailedSum(true),
                "a merge whose function answers null for a sum that could not be held drops the"
                        + " key; look at what the merge answered, or add the weights with"
                        + " LinearForm.sum, which says that it failed");
    }

    /** The control: the merges that do look are read by the same walk. Without it the assertion
     *  above would hold of a walk that read nothing. */
    @Test
    void theMergesThatLookAtTheirAnswerAreSeenByTheSameWalk() {
        assertFalse(mergesThatLoseAFailedSum(false).isEmpty(),
                () -> "the walk saw no merge that turns a failed sum into null");
    }

    /** The methods that merge with a function answering null for an unheld sum: those that throw
     *  the answer away where {@code thrownAwayIsWhatIsAsked}, and those that look at it where
     *  not. */
    private static List<String> mergesThatLoseAFailedSum(boolean thrownAwayIsWhatIsAsked) {
        TreeSet<String> out = new TreeSet<>();
        for (ClassModel owner : COMPILED.all()) {
            String name = owner.thisClass().asInternalName();
            for (MethodModel method : owner.methods()) {
                List<Instruction> code = instructionsOf(method);
                if (!handsAFunctionThatAnswersNull(owner, code)) {
                    continue;
                }
                for (int i = 0; i < code.size(); i++) {
                    if (!merges(code.get(i))) {
                        continue;
                    }
                    int next = i + 1;
                    while (next < code.size()
                            && code.get(next).opcode() == Opcode.CHECKCAST) {
                        next++;
                    }
                    boolean thrownAway = next < code.size() && code.get(next).opcode() == Opcode.POP;
                    if (thrownAway == thrownAwayIsWhatIsAsked) {
                        out.add(name + "#" + method.methodName().stringValue());
                    }
                }
            }
        }
        return new ArrayList<>(out);
    }

    private static boolean merges(Instruction instruction) {
        return instruction instanceof InvokeInstruction call
                && call.name().equalsString("merge")
                && call.owner().asInternalName().startsWith("java/util/")
                && call.type().stringValue()
                        .equals("(Ljava/lang/Object;Ljava/lang/Object;"
                                + "Ljava/util/function/BiFunction;)Ljava/lang/Object;");
    }

    /** Whether a lambda this method hands on is a method of {@code owner} that calls
     *  {@code orNull} on an answer of the exact arithmetic. */
    private static boolean handsAFunctionThatAnswersNull(ClassModel owner,
                                                         List<Instruction> code) {
        for (Instruction each : code) {
            if (!(each instanceof InvokeDynamicInstruction dynamic)) {
                continue;
            }
            for (ConstantDesc argument : dynamic.bootstrapArgs()) {
                if (argument instanceof DirectMethodHandleDesc handle
                        && handle.owner().descriptorString()
                                .equals("L" + owner.thisClass().asInternalName() + ";")
                        && handle.methodName().startsWith("lambda$")
                        && callsOrNull(owner, handle.methodName())) {
                    return true;
                }
            }
        }
        return false;
    }

    private static boolean callsOrNull(ClassModel owner, String lambda) {
        for (MethodModel method : owner.methods()) {
            if (method.methodName().equalsString(lambda)) {
                for (Instruction each : instructionsOf(method)) {
                    if (each instanceof InvokeInstruction call
                            && call.name().equalsString("orNull")
                            && call.owner().asInternalName().startsWith("souther/compiler/numeric/")) {
                        return true;
                    }
                }
            }
        }
        return false;
    }

    private static List<Instruction> instructionsOf(MethodModel method) {
        return method.code().map(code -> code.elementList().stream()
                .filter(Instruction.class::isInstance)
                .map(Instruction.class::cast)
                .toList()).orElse(List.of());
    }
}
