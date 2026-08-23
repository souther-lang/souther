package souther.compiler.partition;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.PartitionEvidence;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * What a comparison that drew no line is reported as, read off what the comparison is.
 *
 * <p>A table, because the answers are only reviewable together. Each row is one shape of rule, and
 * what tells the rows apart is what the author wrote — not which of this compiler's readers happened
 * to answer first. Written the other way round, the word a report printed came from the arithmetic
 * declining to answer, so two rules of one kind were described as two kinds and two kinds as one.
 *
 * <p>The rows that draw a line are here as well as the rows that do not. A rule the arithmetic reads
 * still says what it could not divide, and pinning only the rules that stop would let one of these
 * quietly become the other.
 */
class WhatStoppedAComparisonIsReadOffWhatItIsTest {

    /**
     * The language's own arithmetic over two positions. It divides neither of them, which is what
     * it says and not something missing here.
     */
    @Test
    void arithmeticOverTwoPositionsRelatesThem() {
        assertEquals(List.of(UndividedPosition.Reason.UNSUPPORTED_PARTITION_SHAPE),
                whyAt(guard("a: Int, b: Int", "Int.add(a, b) > 10"), "a"));
        assertEquals(List.of(UndividedPosition.Reason.UNSUPPORTED_PARTITION_SHAPE),
                whyAt(guard("a: Int, b: Int", "Int.subtract(b, a) > 10"), "b"));
    }

    /**
     * The same arithmetic outside the fragment it is read in. The form was seen and not taken
     * apart, which is a wider reading of forms and not a statement about any operation: the language
     * has an operator for a product, so an author is not being asked to invert anything.
     */
    @Test
    void arithmeticOutsideTheFragmentIsAFormNobodyReads() {
        assertEquals(List.of(UndividedPosition.Reason.UNSUPPORTED_SYNTAX),
                whyAt(guard("a: Int", "Int.multiply(a, a) > 10"), "a"));
    }

    /**
     * An operation answered the value the rule is about. Where the values came from is known and
     * what the rule says about them here is not, which asks for a statement about the operation.
     *
     * <p>Told that its syntax was not read, an author goes looking for a spelling this compiler
     * handles perfectly well.
     */
    @Test
    void anOperationsAnswerIsARuleAboutAValueMadeFromThePosition() {
        assertEquals(List.of(UndividedPosition.Reason.RULE_ABOUT_A_DERIVED_VALUE),
                whyAt(guard("a: Date, b: Date", "Date.daysBetween(a, b) > 10"), "a"));
        assertEquals(List.of(UndividedPosition.Reason.RULE_ABOUT_A_DERIVED_VALUE),
                whyAt(guard("a: Date, b: Date", "Date.daysBetween(a, b) > 10"), "b"));
    }

    /**
     * An operation the library writes in this language is not one of those, and is not an oversight
     * here. {@code Int.abs} has a body, so what stands in the tree by the time anything reads it is
     * the arithmetic that body wrote and not a call — and what stopped the reading is that form.
     *
     * <p>Which is also where the line at zero in this model comes from. Whether a comparison an
     * author cannot open should place one is a question about who owns a partition's contributions,
     * and it is not this one.
     */
    @Test
    void anOperationWrittenInThisLanguageIsTheArithmeticItsBodyWrote() {
        assertEquals(List.of(UndividedPosition.Reason.UNSUPPORTED_SYNTAX),
                whyAt(guard("a: Int", "Int.abs(a) > 10"), "a"));
    }

    /**
     * Which argument an operation was given is part of what the rule is, so both positions are
     * named however the author ordered them.
     */
    @Test
    void bothArgumentsOfAnOperationAreNamed() {
        PartitionEvidence measured = guard("a: Date, b: Date", "Date.daysBetween(b, a) > 10");

        assertEquals(List.of(UndividedPosition.Reason.RULE_ABOUT_A_DERIVED_VALUE),
                whyAt(measured, "a"));
        assertEquals(List.of(UndividedPosition.Reason.RULE_ABOUT_A_DERIVED_VALUE),
                whyAt(measured, "b"));
    }

    private static PartitionEvidence guard(String parameters, String condition) {
        String model = """
                module demo

                data Ok
                data No

                behavior f : (%s) -> Ok | No
                let f (%s) = {
                    guard %s else No
                    Ok
                }
                """.formatted(parameters,
                parameters.replaceAll(":\\s*[A-Za-z<>]+", ""), condition);
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        Map<String, PartitionEvidence> coverage =
                compilation.db().ask(new Adequacy.Coverage("demo")).value();
        assertNotNull(coverage, () -> "the model under test compiles: " + model);
        PartitionEvidence measured = coverage.get("f");
        assertNotNull(measured, () -> "f was measured: " + model);
        return measured;
    }

    /** What a report is told stopped the reading at {@code position}. */
    private static List<UndividedPosition.Reason> whyAt(PartitionEvidence measured,
                                                        String position) {
        return measured.notRead().stream()
                .filter(each -> each.at().equals(position))
                .map(PartitionEvidence.NotRead::reason)
                .toList();
    }
}
