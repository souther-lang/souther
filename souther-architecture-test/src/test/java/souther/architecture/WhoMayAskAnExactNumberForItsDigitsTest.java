package souther.architecture;

import org.junit.jupiter.api.Test;

import java.lang.classfile.ClassModel;
import java.lang.classfile.CodeElement;
import java.lang.classfile.CodeModel;
import java.lang.classfile.MethodModel;
import java.lang.classfile.instruction.InvokeInstruction;
import java.util.List;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * In {@code souther-compiler}, a number the exact arithmetic worked out is asked for its digits only
 * through a member that says, in its type, whether the host had room to write them.
 *
 * <p>Writing a ratio out as a decimal has three answers: the number is one, no decimal is it, and
 * the host has no room for the digits of the one that is. The third is a fact about the run and says
 * nothing about which values exist, so a reader that meets it as an exception ends the compile with
 * an internal error, and one that catches it into {@code null} says that no value exists.
 * {@code ExactRatio#writtenDecimal} and {@code Count#written} carry it apart from the second and
 * leave what it means to the reader that asks.
 *
 * <p>Two things are held. No member that turns a ratio into digits and throws for want of room
 * exists, so a reader cannot ask one; and the arithmetic that throws is reached from one class,
 * whose total member wraps it and whose spelling asks first whether the digits are few. What a
 * reader does with an unheld answer is its own, and is said where it is decided.
 */
class WhoMayAskAnExactNumberForItsDigitsTest {

    private static final CompiledOutputs COMPILED = CompiledOutputs.ofWhatThisRepositoryPublishes();

    private static final String THE_ARITHMETIC = "souther/exact/ExactArithmetic";

    /** The members a reader once asked and that threw for want of room, by owner and name. */
    private static final List<String> THAT_THROW = List.of(
            "souther/compiler/numeric/ExactRatio#asWrittenDecimal",
            "souther/compiler/numeric/Count#at(ExactRatio)",
            "souther/compiler/numeric/Count#number(ExactRatio)");

    @Test
    void noMemberTurnsAnExactNumberIntoDigitsAndThrowsForWantOfRoom() {
        TreeSet<String> declared = new TreeSet<>();
        for (ClassModel owner : COMPILED.classesOf(COMPILED.module("souther-compiler"))) {
            String name = owner.thisClass().asInternalName();
            for (MethodModel method : owner.methods()) {
                String member = method.methodName().stringValue();
                String descriptor = method.methodTypeSymbol().displayDescriptor();
                if (name.equals("souther/compiler/numeric/ExactRatio")
                        && member.equals("asWrittenDecimal")) {
                    declared.add(name + "#" + member);
                }
                if (name.equals("souther/compiler/numeric/Count")
                        && (member.equals("at") || member.equals("number"))
                        && descriptor.startsWith("(souther.compiler.numeric.ExactRatio)")) {
                    declared.add(name + "#" + member + "(ExactRatio)");
                }
            }
        }
        assertEquals(List.of(), List.copyOf(declared),
                "a reader asking one of " + THAT_THROW + " ends the compile with an internal error"
                        + " where the host has no room, or says no value exists; the members that"
                        + " answer are ExactRatio#writtenDecimal and Count#written");
    }

    @Test
    void theArithmeticThatThrowsForWantOfRoomIsReachedFromExactRatioOnly() {
        assertEquals(List.of("souther/compiler/numeric/ExactRatio"), callingTheArithmetic(),
                "digits are written out by ExactArithmetic#written, which throws where the host has"
                        + " no room; ExactRatio is where that is turned into an answer, or held to"
                        + " the numbers whose spelling is short");
    }

    /** And the walk sees a call at all, so an empty answer above would mean something. */
    @Test
    void theWalkFindsTheCallInTheTotalMember() {
        assertTrue(!callingTheArithmetic().isEmpty(),
                "the total member is built on the arithmetic, so a walk finding no call finds nothing");
    }

    private static List<String> callingTheArithmetic() {
        TreeSet<String> rows = new TreeSet<>();
        for (ClassModel owner : COMPILED.classesOf(COMPILED.module("souther-compiler"))) {
            for (MethodModel method : owner.methods()) {
                for (CodeModel code : method.code().stream().toList()) {
                    for (CodeElement element : code) {
                        if (element instanceof InvokeInstruction invoke
                                && invoke.owner().asInternalName().equals(THE_ARITHMETIC)
                                && invoke.name().stringValue().equals("written")) {
                            rows.add(owner.thisClass().asInternalName());
                        }
                    }
                }
            }
        }
        return List.copyOf(rows);
    }
}
