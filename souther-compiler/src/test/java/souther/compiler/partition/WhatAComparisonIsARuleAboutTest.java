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
 * What a comparison is a rule about, which decides what it raises.
 *
 * <p><b>Read off the canonical form, and off nothing else.</b> Which quantity a comparison cuts is
 * the arithmetic's answer, and what the comparison is a rule about follows from that same answer —
 * {@code a + 1 <= 10} and {@code a <= b - b + 9} are both {@code a <= 9}, so both are rules about
 * {@code a}. Worked out beside the line instead, from the operands as they were written, the first
 * came back naming no position and the second came back a rule about a pair: a border was drawn at
 * a position nothing was owed about, and a question was raised about a place the rule never
 * stopped.
 *
 * <p>So the rows vary two things and no third. What the sides read — a constant, an input the row
 * chooses, the answer the behavior gives — and how the arithmetic reads them. A row that varies
 * only the spelling is here to fix that the spelling does not matter.
 */
class WhatAComparisonIsARuleAboutTest {

    /**
     * What one clause's comparison comes to, through the classifier a report is built from.
     *
     * <p>The comparison is taken out of the declaration's own rules, which is where the reading
     * that measures a behavior gets it — a clause is read in the representation that keeps the
     * language's operations standing, and one built by hand here would be a shape no clause
     * arrives in.
     */
    private static ComparisonAssessment about(String params, String clause) {
        String source = """
                module g

                data Ok = { n: Int }
                data Grade = Low | Mid | High

                behavior f : %s -> Ok
                    ensures %s
                """.formatted(params, clause);
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
        return ComparisonAssessment.of("f", comparison,
                InputReads.ofWhatIsDeclared(inputs, roots), symbols,
                inputs.quantities(symbols), rule.value());
    }

    /** The same over two {@code Int} positions, which is what most of the table is written over. */
    private static ComparisonAssessment about(String clause) {
        return about("(a: Int, b: Int)", clause);
    }

    /** How a row of the table is written down, so that a mismatch names both shapes. */
    private static String named(ComparisonAssessment of) {
        return of.getClass().getSimpleName();
    }

    /**
     * The table.
     *
     * <p>One assertion per row, and every row in one test: what each of them fixes is the
     * classification's <em>precedence</em>, and a row read on its own cannot say that the arm above
     * it did not take the comparison first.
     */
    @Test
    void whatTheCanonicalFormCutsDecidesWhatTheComparisonIsAbout() {
        assertEquals("AtAPosition", named(about("a <= 20")),
                "an input against a constant is measured at the input");
        assertEquals("AtAPosition", named(about("a + 1 <= 10")),
                "and so is one the arithmetic has to add up first");
        assertEquals("AtAPosition", named(about("10 >= a + 1")),
                "whichever side of the comparison the position was written on");
        assertEquals("AtAPosition", named(about("2 * a <= 9")),
                "a multiple of one position cuts that position, at four rather than at nine");
        assertEquals("AtAPosition", named(about("a <= b - b + 9")),
                "a position the arithmetic cancels is not one the rule is about");

        assertEquals("AcrossPositions", named(about("a <= b")),
                "two positions that stay two are a rule over both, and the line is on neither");
        assertEquals("AcrossPositions", named(about("a <= b + 1")),
                "a distance is a form over two positions like any other");
        assertEquals("AcrossPositions", named(about("a + b <= 10")),
                "and so is a sum, which is not a distance between them");

        assertEquals("CutsNothing", named(about("a <= a")),
                "a rule every row satisfies cuts no quantity, and it names a position");
        assertEquals("CutsNothing", named(about("a - a <= 0")),
                "however the cancelling was spelled");
        assertEquals("NoInput", named(about("20 <= 30")),
                "a comparison of two constants says nothing about an input");
        assertEquals("Unread", named(about("a * a <= 9")),
                "a form the arithmetic does not take apart is a limit of this compiler");

        assertEquals("AnswerDependent", named(about("value.n <= 20")),
                "a bound on the answer is not a bound on anything a row chooses");
        assertEquals("AnswerDependent", named(about("value.n <= a")),
                "and neither is one whose other side is an input");
        assertEquals("AnswerDependent", named(about("value.n + a <= 20")),
                "reading the answer decides it, whatever else the same side names");
    }

    /**
     * A value singled out is read off the canonical quantity too, and it may name none.
     *
     * <p>Apart from the table above, because what is varied here is the operator against one shape
     * of rule. {@code 2 * a == 8} names four and {@code 2 * a == 9} names no whole number at all,
     * and the second is not a rule this compiler failed to read.
     */
    @Test
    void aSinglingIsReadOffTheQuantityAndMayNameNoValueItHolds() {
        assertEquals(Required.Places.AT_THE_VALUE, places(about("a == 9")),
                "a position against a value it holds names that value");
        assertEquals(Required.Places.AT_THE_VALUE, places(about("a /= 9")),
                "and so does a rule refusing it, which puts the same value in a class of its own");
        assertEquals(Required.Places.AT_THE_VALUE, places(about("2 * a == 8")),
                "twice a position equal to eight names four");
        assertEquals(Required.Places.AT_NO_VALUE, places(about("2 * a == 9")),
                "and equal to nine names no whole number, which is not a reading that stopped");
        assertEquals("AcrossPositions", named(about("a == b")),
                "an equality over two positions singles one out of neither");
        assertEquals("AcrossPositions", named(about("a + b == 10")),
                "and so does one over their sum");
    }

    /**
     * The orders a line can be drawn on, which are not the numeric ones alone.
     *
     * <p>Two strings stand no measurable distance apart and one is still above the other, so a rule
     * ordering them draws a line where they meet. Read as a form over positions whose counts have
     * to add up, that line was lost; read off the operands as written, {@code s <= s} drew one
     * between a position and itself.
     */
    @Test
    void anOrderWithNoCountsUnderItStillDrawsALineWhereTwoPositionsMeet() {
        assertEquals("AcrossPositions", named(about("(s: String, t: String)", "s <= t")),
                "two strings are ordered, and the line is where they meet");
        assertEquals("CutsNothing", named(about("(s: String, t: String)", "s <= s")),
                "and one against itself cuts nothing, on that order like any other");
        assertEquals("AcrossPositions", named(about("(g: Grade, h: Grade)", "g <= h")),
                "an enumeration's cases are ordered by the sum they are of");
        assertEquals("AtAPosition", named(about("(g: Grade)", "g == Mid")),
                "and a case written against one of them is a value of that position");
        assertEquals("AtAPosition", named(about("(s: String)", "s == \"m\"")),
                "a string against a written string is read where the arithmetic cannot go");
    }

    /**
     * A rule that cuts where the quantity never runs.
     *
     * <p>Its own answer and not a reading that stopped. A length is never negative, so the rule was
     * read in full and what it says is that no row satisfies it — there is no border, and no class
     * for the position to be divided into.
     */
    @Test
    void aLineTheQuantityDoesNotReachIsUnderstoodRatherThanUnread() {
        assertEquals("OutsideTheDomain",
                named(about("(xs: List<Int>)", "List.length(xs) <= -1")),
                "a length below zero is a line the quantity never reaches");
        assertEquals("AtAPosition", named(about("(xs: List<Int>)", "List.length(xs) <= 3")),
                "and the same rule at a length it does reach cuts the position");
    }

    /**
     * And what each of them raises.
     *
     * <p>Beside the table rather than folded into it. What a comparison is about and what it asks
     * of a measure of coverage are two questions with two answers, and a test that only read the
     * second could not tell an arm that raises nothing from an arm that does not exist.
     */
    @Test
    void everyArmThatRaisesNothingSaysSomethingDifferentAboutWhy() {
        assertEquals(Required.Because.IT_DEPENDS_ON_THE_ANSWER, why(about("value.n <= a")),
                "the answer, and not that the rule names no position — it names one");
        assertEquals(Required.Because.IT_CUTS_NOTHING, why(about("a <= a")),
                "read in full, and what it cuts is nothing");
        assertEquals(Required.Because.IT_NAMES_NO_POSITION, why(about("20 <= 30")),
                "nowhere to be about");
        assertEquals(Required.Because.IT_WAS_NOT_READ, why(about("a * a <= 9")),
                "the only one of these that is about a limit of this compiler");
        assertEquals(Required.Because.IT_SINGLES_ACROSS_POSITIONS, why(about("a == b")),
                "one arm put whole on a place, which the branch measure already asks a row for");
        assertEquals(Required.Because.IT_NAMES_NO_VALUE_THE_QUANTITY_HOLDS,
                why(about("2 * a == 9")),
                "read in full, and the value it names is not one the quantity takes");
        assertEquals(Required.Because.IT_CUTS_WHERE_THE_QUANTITY_DOES_NOT_RUN,
                why(about("(xs: List<Int>)", "List.length(xs) <= -1")),
                "read in full, and the line is outside where a length goes");
    }

    /** What a comparison that raises a question raises, which is a boundary and the classes it
     *  divides the position into. */
    @Test
    void aLineOnAPositionRaisesABorderAndTheClassesEitherSideOfIt() {
        Required required = Required.ofComparison(about("a + 1 <= 10").subject());

        assertEquals(List.of("BOUNDARY", "PARTITION"),
                required.obligations().stream().map(each -> each.obligation().name()).toList(),
                "the border and the classes, from a rule the spelling used to hide");
    }

    /** The one reason a comparison raises nothing, where it raises nothing. */
    private static Required.Because why(ComparisonAssessment of) {
        Required required = Required.ofComparison(of.subject());
        Required.Irrelevant irrelevant = assertInstanceOf(Required.Irrelevant.class, required,
                () -> "raises nothing: " + required);
        assertEquals(1, irrelevant.because().size(), "one comparison, one reason");
        return irrelevant.because().iterator().next();
    }

    /** What the rule does to the quantity it cuts. */
    private static Required.Places places(ComparisonAssessment of) {
        return switch (of.subject()) {
            case Required.ComparisonSubject.AnInput input -> input.places();
            case Required.ComparisonSubject.AcrossPositions over -> over.places();
            default -> throw new AssertionError("not a comparison that cuts: " + of);
        };
    }
}
