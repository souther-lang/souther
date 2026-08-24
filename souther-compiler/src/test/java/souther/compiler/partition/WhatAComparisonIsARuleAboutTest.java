package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.BehaviorContract;
import souther.compiler.check.Required;
import souther.compiler.check.StatedContract;
import souther.compiler.check.Symbols;
import souther.compiler.core.Core;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.InputReads;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.Scopes;
import souther.compiler.types.BindingId;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * What a comparison is a rule about, which decides what it raises (issue #1013).
 *
 * <p><b>A table of what the two sides read, and nothing else.</b> Each row varies where the values
 * in the comparison come from — a constant, an input the row chooses, the answer the behavior gives
 * — and the classification is what that provenance comes to. How the arithmetic reads the operands
 * is a different axis and is not measured here: {@code a + 1 <= 10} and {@code a <= b - b + 9} both
 * cut one position at nine, and which subject follows from that is issue #1029. A row of this table
 * written over one of those shapes would be two questions under one answer.
 *
 * <p>So the pair row is {@code a <= b} over two positions that stay two, and no row cancels.
 * The one row that puts two provenances in one comparison does it on purpose: {@code value.n + a}
 * reads the answer and names an input, and which of the two decides the classification is exactly
 * what the row fixes.
 */
class WhatAComparisonIsARuleAboutTest {

    /**
     * What one clause's comparison is a rule about, through the classifier a report is built from.
     *
     * <p>The comparison is taken out of the declaration's own rules, which is where the reading
     * that measures a behavior gets it — a clause is read in the representation that keeps the
     * language's operations standing, and one built by hand here would be a shape no clause
     * arrives in.
     */
    private static Required.ComparisonSubject about(String clause) {
        String source = """
                module g

                data Ok = { n: Int }

                behavior f : (a: Int, b: Int) -> Ok
                    ensures %s
                """.formatted(clause);
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        String module = compilation.modules().get(0);
        Symbols symbols = Scopes.derived(compilation.db(), module).value();
        StatedContract stated =
                compilation.db().ask(new Bodies.StatedContracts(module)).value().get("f");
        InputDomain inputs =
                compilation.db().ask(new Adequacy.Inputs(module)).value().get("f");

        assertEquals(1, stated.rules().size(), "the model under test states one rule");
        StatedContract.StatedRule rule = stated.rules().get(0);
        assertEquals(1, rule.conjuncts().size(), "the rule states one comparison");
        Core read = rule.conjuncts().get(0).stated().orNull();
        Core.Binary comparison = assertInstanceOf(Core.Binary.class, read,
                () -> clause + " arrives as a comparison");

        Map<BindingId, String> roots = new LinkedHashMap<>();
        for (BehaviorContract.ContractParam param : stated.params()) {
            roots.putIfAbsent(param.binding(), param.name());
        }
        return ComparisonSubjects.of(comparison,
                InputReads.ofWhatIsDeclared(inputs, roots), symbols, rule.value());
    }

    /** How a row of the table is written down, so that a mismatch names both shapes. */
    private static String named(Required.ComparisonSubject of) {
        return of.getClass().getSimpleName();
    }

    /**
     * The table.
     *
     * <p>One assertion per row, and every row of the table in one test: what each of them fixes is
     * the classification's <em>precedence</em>, and a row read on its own cannot say that the arm
     * above it did not take the comparison first.
     */
    @Test
    void whatTheTwoSidesReadDecidesWhatTheComparisonIsAbout() {
        assertEquals("AnInput", named(about("a <= 20")),
                "an input against a constant is measured at the input");
        assertEquals("Relation", named(about("a <= b")),
                "two inputs are a rule about the pair, and the line is on neither");
        assertEquals("AnswerDependent", named(about("value.n <= 20")),
                "a bound on the answer is not a bound on anything a row chooses");
        assertEquals("AnswerDependent", named(about("value.n <= a")),
                "and neither is one whose other side is an input — issue #1013");
        assertEquals("AnswerDependent", named(about("value.n + a <= 20")),
                "reading the answer decides it, whatever else the same side names");
        assertEquals("NoInput", named(about("20 <= 30")),
                "a comparison of two constants says nothing about an input");
    }

    /**
     * And what each of them raises.
     *
     * <p>Beside the table rather than folded into it. What a comparison is about and what it asks
     * of a measure of coverage are two questions with two answers, and a test that only read the
     * second could not tell an arm that raises nothing from an arm that does not exist.
     */
    @Test
    void anAnswerDependentComparisonRaisesNothingAndSaysWhy() {
        Required required = Required.ofComparison(
                new souther.compiler.check.ComparisonClaim.Cut(true, true),
                about("value.n <= a"));

        assertEquals(List.of(), List.copyOf(required.obligations()),
                "a row cannot be written where this clause stops");
        Required.Irrelevant why = assertInstanceOf(Required.Irrelevant.class, required);
        assertEquals(java.util.Set.of(Required.Because.IT_DEPENDS_ON_THE_ANSWER), why.because(),
                "and the reason is the answer, not that the rule names no position — it names one");
    }
}
