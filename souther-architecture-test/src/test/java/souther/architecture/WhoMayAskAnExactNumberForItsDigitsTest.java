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
    void theArithmeticThatThrowsForWantOfRoomIsReachedFromFourMethodsOfExactRatioOnly() {
        String ratio = "souther/compiler/numeric/ExactRatio";
        assertEquals(List.of(
                        // Held to the numbers whose spelling is short, which is asked first.
                        ratio + "#asFraction",
                        ratio + "#spelled",
                        // A whole number, which the arithmetic answers or refuses as an answer.
                        ratio + "#wholeNumber",
                        // The private writer, which only the total member reaches (below).
                        ratio + "#written"),
                callingTheArithmetic(),
                "digits are written out by ExactArithmetic#written, which throws where the host has"
                        + " no room, and a method of ExactRatio that reaches it is either held to"
                        + " short spellings or answers with what it holds; a new one that hands the"
                        + " digits to a reader under any name is the partial member back, and is"
                        + " added here only with the case for it");
    }

    /**
     * The member that writes the digits and throws is private, and one method reaches it.
     *
     * <p>Held apart from the names above, which only say what once existed: a new member that
     * hands the throwing writer to a reader under another name would be the same defect back, and
     * this is what stops it. The total member is the only way in, and its answer is what a reader
     * reads.
     */
    @Test
    void theWriterThatThrowsIsPrivateAndOnlyTheTotalMemberReachesIt() {
        String ratio = "souther/compiler/numeric/ExactRatio";
        TreeSet<String> reaching = new TreeSet<>();
        boolean isPrivate = false;
        boolean found = false;
        for (ClassModel owner : COMPILED.classesOf(COMPILED.module("souther-compiler"))) {
            for (MethodModel method : owner.methods()) {
                if (owner.thisClass().asInternalName().equals(ratio)
                        && method.methodName().stringValue().equals("written")
                        && method.methodTypeSymbol().parameterCount() == 0) {
                    found = true;
                    isPrivate = method.flags().has(java.lang.reflect.AccessFlag.PRIVATE);
                }
                for (CodeModel code : method.code().stream().toList()) {
                    for (CodeElement element : code) {
                        if (element instanceof InvokeInstruction invoke
                                && invoke.owner().asInternalName().equals(ratio)
                                && invoke.name().stringValue().equals("written")
                                && invoke.typeSymbol().parameterCount() == 0) {
                            String from = method.methodName().stringValue();
                            reaching.add(owner.thisClass().asInternalName() + "#"
                                    + (from.startsWith("lambda$writtenDecimal$")
                                            ? "writtenDecimal" : from));
                        }
                    }
                }
            }
        }
        assertTrue(found, "the writer is in ExactRatio, so a walk not finding it finds nothing");
        assertTrue(isPrivate, "a writer a reader can name is a way to ask for digits that throws");
        assertEquals(List.of(ratio + "#writtenDecimal"), List.copyOf(reaching),
                "the writer that throws is reached from the total member alone");
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
                            String from = method.methodName().stringValue();
                            // A lambda is its method's own code, whatever javac numbers it.
                            java.util.regex.Matcher lambda =
                                    java.util.regex.Pattern.compile("lambda\\$(.+)\\$\\d+")
                                            .matcher(from);
                            rows.add(owner.thisClass().asInternalName() + "#"
                                    + (lambda.matches() ? lambda.group(1) : from));
                        }
                    }
                }
            }
        }
        return List.copyOf(rows);
    }
}
