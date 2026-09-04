package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Compilation;
import souther.compiler.query.Scopes;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A question a rule leaves standing is accounted for by a reading or by the answer, and the two are
 * told apart.
 *
 * <p>Three causes reach one outcome and only two of them are about a rule. A rule whose form no
 * reading takes apart is the reading's own account; a rule read in full whose exact answer ran past
 * the allowance is an account of the answer, which no rule is answerable for
 * ({@link ReadingEvidence#stoppedBy} refuses to file one). A question with neither is the accounting
 * disagreeing with itself and is refused where it is made.
 *
 * <p>The third case is what this is for. Reaching an admitted-values question with no reading having
 * recognised the rule's positions was one, and a helper was the way to it: the clause was read at
 * the names the expansion's binding introduced and every reading passed over it. Going inside the
 * binding closed that (ADR-0106), so the helper here is held to answering as the rule written out
 * does — and the answer-level case is held beside it, so that closing one is not read as the other
 * having gone away.
 */
class WhatAStandingQuestionIsAccountedForByTest {

    /**
     * A rule no reading takes apart, written where the clause is.
     *
     * <p>The reading recognised the position and gave up on the rule, which is its own account to
     * give.
     */
    private static final String A_FORM_NO_READING_TAKES_APART = """
            module demo

            data Range = { min: String, max: String }

            data N = { range: Range }
                invariant UNREAD_MAX
            """.replace("UNREAD_MAX", souther.compiler.ARuleNoReadingTakesIn.about("range.max"));

    /** The same rule, reached through a helper, which is the same rule about the same position. */
    private static final String THE_SAME_FORM_THROUGH_A_HELPER = """
            module demo

            data Range = { min: String, max: String }

            data N = { range: Range }
                invariant valid(range)

            let valid (r: Range) : Bool = UNREAD_MAX
            """.replace("UNREAD_MAX", souther.compiler.ARuleNoReadingTakesIn.about("r.max"));

    /**
     * Rules read in full whose answer is more than the allowance will build.
     *
     * <p>Each pattern is small and both are taken in; showing the branch they share empty takes a
     * machine of about ninety thousand states. So nothing is short of a rule here, and what is short
     * is the answer they come to between them — which is why the question stands with no reading
     * naming a rule. The same model is read for what it leaves the position in
     * {@code ABranchNobodyCouldWorkOutIsNotOneAnybodyReadTest}.
     */
    private static final String AN_ANSWER_BEYOND_THE_ALLOWANCE = """
            module demo

            data N = { x: String, y: String }
                invariant r =
                    (String.matches("a{300}", y) && String.matches("b{300}", y))
                    || x == "A"
            """;

    @Test
    void aFormNoReadingTakesApartIsTheReadingsOwnAccount() {
        assertEquals(Map.of("invariant N #1 at range.max", "TheValueReadingSays"),
                whyStanding(A_FORM_NO_READING_TAKES_APART));
    }

    /** And reaching that rule through a helper does not change whose account it is. */
    @Test
    void reachingThatRuleThroughAHelperLeavesTheSameAccount() {
        assertEquals(whyStanding(A_FORM_NO_READING_TAKES_APART),
                whyStanding(THE_SAME_FORM_THROUGH_A_HELPER));
    }

    /**
     * And a rule the reading took in whole leaves a question no reading is answerable for.
     *
     * <p>Which is the arm that names none of them, standing for the one thing it now stands for. A
     * reading's own words here would say that something fell short of the rule, and nothing did.
     */
    @Test
    void anAnswerBeyondTheAllowanceIsAccountedForByNoReading() {
        assertEquals(Map.of("invariant N (r) at y", "NothingTookItIn"),
                whyStanding(AN_ANSWER_BEYOND_THE_ALLOWANCE));
    }

    /** What became of every question of every rule that nothing answered. */
    private static Map<String, String> whyStanding(String source) {
        Map<String, String> out = new LinkedHashMap<>();
        read(source).accounting().values().forEach(accounting ->
                accounting.answers().forEach((owed, outcome) -> {
                    if (outcome instanceof RuleAccounting.Outcome.Unaccounted unaccounted) {
                        out.put(((RuleCitation.Named) accounting.cited()).name() + " at " + owed,
                                unaccounted.why().getClass().getSimpleName());
                    }
                }));
        return out;
    }

    private static FieldDomains read(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        assertEquals(List.of(), compilation.diagnostics().values().stream()
                .flatMap(List::stream)
                .map(each -> each.diagnostic().code())
                .toList(), "the model this reads has to be one somebody could write");
        Symbols symbols = Scopes.derived(compilation.db(), "demo").value();
        TypeSymbol.AtModule name = TypeSymbols.declared(new TypeKey(symbols.module(), "N"));
        return FieldDomains.of(name, RuleReadings.of(compilation, "demo"),
                souther.compiler.query.ReadAs.THE_COMPILATION_DOES);
    }
}
