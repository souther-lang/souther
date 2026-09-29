package souther.architecture;

import org.junit.jupiter.api.Test;

import java.lang.classfile.ClassModel;
import java.lang.classfile.CodeElement;
import java.lang.classfile.CodeModel;
import java.lang.classfile.MethodModel;
import java.lang.classfile.instruction.InvokeInstruction;
import java.util.List;
import java.util.Map;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * In {@code souther-compiler}, a number the exact arithmetic worked out is asked for its digits
 * through a member that throws only at the call sites below.
 *
 * <p>Three members turn an exact ratio into a decimal or a count and can refuse: {@code
 * ExactRatio#asWrittenDecimal}, {@code Count#at(ExactRatio)} and {@code Count#number(ExactRatio)}.
 * Each answers {@code null} (or refuses the caller's premise) where no decimal is the number, and
 * <em>throws</em> where the host has no room to write the digits out. The second is a fact about
 * the run and says nothing about which values exist, so a reader that meets it as an exception ends
 * the compile with an internal error, and one that catches it into {@code null} says that no value
 * exists. What a reasoning class asks instead is {@code ExactRatio#writtenDecimal} or {@code
 * Count#written}, which carry the two apart in their type and leave the meaning to the reader.
 *
 * <p>The list is closed. A class not on it that asks a partial member for digits is a reader that
 * has not said what the host running out of room means to it. A row is removed by moving its reader
 * onto the total member, and is never added to.
 *
 * <p>Each row says what its reader does with the answer. Where the number is a sum or a product of
 * counts a carrier already holds, its digits are those of the operands and one more place, and the
 * host has room for it wherever it had room for them. Where the number comes out of a form's own
 * ratios — a coefficient, a cut, a quotient of them — a model's constants can put its digits past
 * the host, and the reader lets the failure end the compile.
 *
 * <p>{@code Count#at} and {@code Count#number} are the partial members themselves, and {@code
 * Count#along} reaches them: those rows are the definitions and not readers.
 */
class WhoMayAskAnExactNumberForItsDigitsTest {

    private static final CompiledOutputs COMPILED = CompiledOutputs.ofWhatThisRepositoryPublishes();

    private static final String OF_COUNTS = "a sum of counts a carrier already holds, so the digits are"
            + " the operands' and one place more";
    private static final String OF_A_FORM = "a number out of a form's own ratios, whose digits a"
            + " model's constants can put past the host; the failure ends the compile";

    /** Which partial member each name in a row stands for. */
    private static final Map<String, String> PARTIAL = Map.of(
            "souther/compiler/numeric/ExactRatio asWrittenDecimal()Ljava/math/BigDecimal;",
            "ExactRatio.asWrittenDecimal",
            "souther/compiler/numeric/Count at(Lsouther/compiler/numeric/ExactRatio;)"
                    + "Lsouther/compiler/numeric/Count;",
            "Count.at",
            "souther/compiler/numeric/Count number(Lsouther/compiler/numeric/ExactRatio;)"
                    + "Lsouther/compiler/numeric/Count;",
            "Count.number");

    /** One reader, the member it asks, and what it does with the answer. */
    private record Reader(String row, String why) {}

    private static final List<Reader> STILL_ASKING = List.of(
            new Reader("check/Carrier#halfway -> Count.at", OF_COUNTS),
            new Reader("check/Carrier#oneFrom -> Count.at", OF_COUNTS),
            new Reader("check/IntrinsicNumericFacts#constantOf -> ExactRatio.asWrittenDecimal",
                    OF_A_FORM),
            new Reader("check/OccurrenceValues#wholeValuesAt -> ExactRatio.asWrittenDecimal",
                    OF_COUNTS),
            new Reader("inputs/TermReading#addedUp -> ExactRatio.asWrittenDecimal", OF_COUNTS),
            new Reader("numeric/Count#along -> Count.at", "the definition of the step"),
            new Reader("numeric/Count#at -> ExactRatio.asWrittenDecimal",
                    "the definition of the partial member"),
            new Reader("numeric/Count#number -> Count.at", "the definition of the narrowing"),
            new Reader("partition/CandidateDomain#filling -> ExactRatio.asWrittenDecimal",
                    OF_A_FORM),
            new Reader("partition/CandidateDomain#somewhere -> ExactRatio.asWrittenDecimal",
                    OF_A_FORM),
            new Reader("partition/CandidateDomain#stepping -> ExactRatio.asWrittenDecimal",
                    OF_A_FORM),
            new Reader("partition/ComparedLine#fromTheForm -> Count.at", OF_A_FORM),
            new Reader("partition/ComparedTerms#fromTheForm -> Count.at", OF_A_FORM),
            new Reader("partition/ContainersAddingUp#splitting -> ExactRatio.asWrittenDecimal",
                    OF_COUNTS),
            new Reader("partition/Level#asAPlace -> Count.number", OF_A_FORM),
            new Reader("partition/Level#asAPlaceOrNothing -> Count.at", OF_A_FORM),
            new Reader("partition/LevelRealizer#moved -> Count.at", OF_COUNTS),
            new Reader("partition/LevelRealizer#movedBy -> Count.at", OF_COUNTS),
            new Reader("partition/LevelRealizer$Search#onExactly -> ExactRatio.asWrittenDecimal",
                    OF_A_FORM),
            new Reader("partition/LevelRealizer$Search#solving -> ExactRatio.asWrittenDecimal",
                    OF_A_FORM),
            new Reader("partition/LevelRealizer$Search#walkingExactly"
                    + " -> ExactRatio.asWrittenDecimal", OF_A_FORM),
            new Reader("partition/LevelRealizer$Search#written -> Count.at", OF_A_FORM),
            new Reader("partition/Outwards#onTheCarrier -> Count.at",
                    "catches the failure and answers a place it could not hold"),
            new Reader("partition/TermRealizations#multipliedBack"
                    + " -> ExactRatio.asWrittenDecimal", OF_COUNTS),
            new Reader("partition/TermRealizations#placeAt -> ExactRatio.asWrittenDecimal",
                    OF_A_FORM),
            new Reader("query/AnotherLineTheRowsAllow#movedBy -> Count.at", OF_A_FORM),
            new Reader("semantics/ResultRange#standsAt -> ExactRatio.asWrittenDecimal",
                    OF_COUNTS));

    @Test
    void everyReaderThatAsksForDigitsWithAMemberThatThrowsIsWrittenDownHere() {
        assertEquals(STILL_ASKING.stream().map(Reader::row).toList(), askingForDigits(),
                "a reader asking for the digits of an exact number through a member that throws when"
                        + " the host has no room ends the compile with an internal error there,"
                        + " and one that catches it says no value exists; the total members are"
                        + " ExactRatio#writtenDecimal and Count#written");
    }

    @Test
    void everyRowSaysWhatItsReaderDoesWithTheAnswer() {
        for (Reader each : STILL_ASKING) {
            assertTrue(!each.why().isBlank(), () -> each.row() + " says nothing about its answer");
        }
    }

    /** And the walk sees a call at all, so an empty answer above would mean something. */
    @Test
    void theWalkFindsThePartialMemberDefinedOverTheArithmetic() {
        assertTrue(askingForDigits().contains("numeric/Count#at -> ExactRatio.asWrittenDecimal"),
                "Count.at is built on asWrittenDecimal, so a walk not finding that finds nothing");
    }

    private static List<String> askingForDigits() {
        TreeSet<String> rows = new TreeSet<>();
        for (ClassModel owner : COMPILED.classesOf(COMPILED.module("souther-compiler"))) {
            for (MethodModel method : owner.methods()) {
                for (CodeModel code : method.code().stream().toList()) {
                    for (CodeElement element : code) {
                        if (element instanceof InvokeInstruction invoke) {
                            String called = invoke.owner().asInternalName() + " "
                                    + invoke.name().stringValue() + invoke.type().stringValue();
                            String partial = PARTIAL.get(called);
                            if (partial != null) {
                                rows.add(owner.thisClass().asInternalName()
                                        .replace("souther/compiler/", "") + "#"
                                        + method.methodName().stringValue() + " -> " + partial);
                            }
                        }
                    }
                }
            }
        }
        return List.copyOf(rows);
    }
}
