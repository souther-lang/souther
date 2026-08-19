package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.ast.Hir;
import souther.compiler.query.Compilation;
import souther.compiler.query.Scopes;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * Whether the range is exact and whether the rules were answered are two questions, and neither
 * follows from the other.
 *
 * <p>What an edge stands on is the first: a row at an edge is a whole value with that edge in it, so
 * a rule the bounds do not express is a way that value can be refused. What the coverage accounting
 * measures is the second: a rule is answered where some reading took it in, whatever it made of it.
 * Written down here as a grid rather than as two tests, because the pairs that disagree are the whole
 * content — a measure that read either off the other would be right on the rows that agree and would
 * promise a row nobody can build on the rows that do not.
 *
 * <p>Each row was measured before it was written down, and two of them are answers this compiler gets
 * wrong today. They are asserted as they stand so that the change that fixes them has to say so.
 */
class WhatMakesARangeExactIsNotWhatAnswersACoverageQuestionTest {

    /** The clause alone, so that nothing beside it decides the answer. */
    private static String only(String clauses) {
        return """
                module example.rooms

                data Length = Int
                    %s
                """.formatted(clauses);
    }

    private static FieldDomains read(String source) {
        return read(source, "Length");
    }

    private static FieldDomains read(String source, String type) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        String module = compilation.modules().get(0);
        Symbols symbols = Scopes.derived(compilation.db(), module).value();
        assertNotNull(symbols);
        TypeSymbol named = TypeSymbols.declared(new TypeKey(module, type));
        Hir.Data data = (Hir.Data) symbols.declarations().declaration(named.key());
        assertNotNull(data, "no `" + type + "` declared");
        return FieldDomains.of(named, data, symbols);
    }

    /**
     * The three answers as one value, so that a row states all of them or none.
     *
     * @param everyQuestionAnswered   whether every coverage question the rules raise was answered
     * @param evidence                what the reading that built the bounds says it managed, named
     *                                by the cause rather than compared whole: the atoms a cause
     *                                carries are this compiler's and a test asserting them would be
     *                                a copy of the reading rather than a statement about it
     */
    private record Answers(boolean everyQuestionAnswered, String evidence) {

        static Answers of(String clauses) {
            FieldDomains domains = read(only(clauses));
            return new Answers(
                    domains.accounting().values().stream().allMatch(a -> a.unaccounted().isEmpty()),
                    named(domains.projection()));
        }
    }

    /** A projection's evidence as the causes it names, in order, and "exact" where it names none. */
    private static String named(ProjectionEvidence evidence) {
        return evidence.causes().isEmpty() ? "exact"
                : evidence.causes().stream()
                        .map(cause -> cause.getClass().getSimpleName())
                        .collect(java.util.stream.Collectors.joining(", "));
    }

    private static final Answers EXACT_AND_ANSWERED = new Answers(true, "exact");
    private static final Answers ANSWERED_AND_LOSSY = new Answers(true, "Lossy");
    private static final Answers ANSWERED_AND_UNREPRESENTED = new Answers(true, "Unrepresented");
    private static final Answers UNANSWERED_AND_UNREPRESENTED = new Answers(false, "Unrepresented");

    /** A bound is both, which is the row every other one is read against. */
    @Test
    void aBoundIsExactAndAnswered() {
        assertEquals(EXACT_AND_ANSWERED, Answers.of("invariant top = value <= 10"));
    }

    /**
     * A hole is answered and leaves the range approximate.
     *
     * <p>The reading that turns clauses into sets of values holds {@code value /= 0} whole, so every
     * question about which values may stand at the position is answered. A range is all the interval
     * algebra holds, so the projection admits the 0 and no row can write it.
     */
    @Test
    void aHoleIsAnsweredAndLeavesTheRangeApproximate() {
        assertEquals(ANSWERED_AND_LOSSY, Answers.of("invariant nonzero = value /= 0"));
    }

    /**
     * The same hole beside a bound that already excludes it, which the projection takes in whole.
     *
     * <p>Nothing is lost: a value at or above 1 is on one side of zero, so the domain sharpens the
     * denial to an end rather than dropping it, and the range is the range. Which is a fact about
     * what the projection made of the clause, and not about the shape the clause is written in — a
     * reader asking what a denial could have become has no end for it either way.
     */
    @Test
    void aHoleAlreadyExcludedIsExact() {
        assertEquals(EXACT_AND_ANSWERED,
                Answers.of("""
                        invariant floor = value >= 1
                            invariant nonzero = value /= 0"""));
    }

    /**
     * A rule the numeric reading takes in whole and the second walk has no word for.
     *
     * <p>{@code value * 2 >= 4} moves the floor to 2, and is beyond the reading of ends and the
     * reading of values both. The projection took it in whole, which is the only thing that decides
     * this.
     */
    @Test
    void aScaledBoundIsExact() {
        assertEquals(EXACT_AND_ANSWERED, Answers.of("invariant said = value * 2 >= 4"));
    }

    /**
     * The row a measure built out of what the projection knows has to be built against.
     *
     * <p>Both values are named, so the reading of values holds the clause and every question is
     * answered. The projection is the interval {@code [3, 5]}, and the 4 in the middle is a row
     * nobody can write. Nothing records a loss for it: the clause never reached the interval algebra
     * as a form it could narrow by, so there was no narrowing to lose anything at. A reading that
     * concluded the range was exact from the absence of a loss would offer that 4.
     */
    @Test
    void valuesNamedApartAreAnsweredAndTheRangeBetweenThemIsNot() {
        assertEquals(ANSWERED_AND_UNREPRESENTED,
                Answers.of("invariant said = value == 3 || value == 5"));
    }

    /** A rule nothing took in is unanswered as well, which is the one row where the two agree that
     *  something is missing — and they are answering different questions to get there. */
    @Test
    void aRuleNothingReadIsUnansweredAndLeavesTheRangeApproximate() {
        assertEquals(UNANSWERED_AND_UNREPRESENTED,
                Answers.of("invariant said = Int.abs(value) >= 2"));
    }

    /**
     * A rule written a record away, named as the rule it is and at the position it is about.
     *
     * <p>The reading that builds the bounds reaches a field's own declaration, so what it says it
     * managed is said there too. A rule of the field's type that the interval algebra has no form
     * for leaves the field's range wider than the rule, and the evidence names both which rule and
     * which position — neither of which is derivable from the value the walk came back with.
     */
    @Test
    void aRuleUnderAFieldIsNamedWhereItIsWritten() {
        FieldDomains domains = read("""
                module example.rooms

                data Side = Int
                    invariant said = value == 3 || value == 5

                data Length = { a: Side }
                """, "Length");
        assertEquals(
                List.of(new ProjectionEvidence.Cause.Unrepresented(
                        new RuleRef.Invariant(only(domains, "said")), "a")),
                domains.projection().causes());
    }

    /**
     * One shape, one answer, wherever it is written.
     *
     * <p>A product of a coordinate with itself states a relation about an atom standing for the
     * product and not one about the coordinate, so the range of the coordinate is wider than the
     * rule on a record and on a newtype alike. It was two answers while a walk of the declarations
     * classified the rules by their shape: the record arm asked whether every reading of the clause
     * discharged it and the newtype arm whether the ordered reading placed an end, and one shape
     * went two ways because two walks were being asked.
     */
    @Test
    void oneShapeIsOneAnswerWhereverItIsWritten() {
        FieldDomains onARecord = read("""
                module example.rooms

                data R = { n: Int }
                    invariant odd = n * n >= 4
                """, "R");
        assertEquals("Unrepresented", named(onARecord.projection()));

        assertEquals(UNANSWERED_AND_UNREPRESENTED,
                Answers.of("invariant odd = value * value >= 4"),
                "and the same on a newtype");
    }

    /** The clause of the read declaration the author called {@code name}. */
    private static Clause.Ref only(FieldDomains domains, String name) {
        return domains.accounting().keySet().stream()
                .filter(rule -> rule instanceof RuleRef.Invariant invariant
                        && invariant.clause().name().map(ClauseName::value)
                                .filter(name::equals).isPresent())
                .map(rule -> ((RuleRef.Invariant) rule).clause())
                .findFirst().orElseThrow(() -> new AssertionError("no clause called `" + name + "`"));
    }
}
