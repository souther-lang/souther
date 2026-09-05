package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.BlockReason;
import souther.compiler.inputs.RuleReasons;
import souther.compiler.query.Compilation;
import souther.compiler.query.Scopes;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * What a question's rule left is said in the order the places it stands on were written.
 *
 * <p>The order is the author's or it is nobody's. A reading meets the parts of a clause in whatever
 * order it walks them, and a list handed on afterwards says somebody put it in an order without
 * saying who — so a reader taking the first entry as the first thing to lift is reading a fact about
 * a walk unless the places decided it.
 *
 * <p>Measured by writing the same two clauses the other way round. Nothing else about the model
 * changes, so anything that comes out different is what the author's order settles, and anything
 * that comes out the same is settled by something else.
 */
class WhatAQuestionStandsOnIsSaidInTheOrderItWasWrittenTest {

    /**
     * A pattern this compiler will not build, beside a form no reading takes apart.
     *
     * <p>Two limits of one rule at one position, lifted by different work, so the question stands on
     * both and an author has two places to look at.
     */
    private static final String COSTLY_THEN_UNREAD = """
            module demo

            data N = { y: String }
                invariant r = String.matches("a{60000}", y) && UNREAD_Y
            """.replace("UNREAD_Y", souther.compiler.ARuleNoReadingTakesIn.about("y"));

    /** The same two clauses, written the other way round. */
    private static final String UNREAD_THEN_COSTLY = """
            module demo

            data N = { y: String }
                invariant r = UNREAD_Y && String.matches("a{60000}", y)
            """.replace("UNREAD_Y", souther.compiler.ARuleNoReadingTakesIn.about("y"));

    /** Written this way round, the pattern comes first. */
    @Test
    void theReasonsComeOutInTheOrderTheirClausesWereWritten() {
        assertEquals(List.of(new BlockReason.PatternTooCostly(),
                        new BlockReason.UnreadValueRule()),
                saidOf(COSTLY_THEN_UNREAD),
                "the clause an author wrote first is the first thing they are sent to");
    }

    /** And written the other way round, the form does. */
    @Test
    void andTheOtherWayRoundTheyComeOutTheOtherWayRound() {
        assertEquals(List.of(new BlockReason.UnreadValueRule(),
                        new BlockReason.PatternTooCostly()),
                saidOf(UNREAD_THEN_COSTLY),
                "which is what makes the order the author's rather than the walk's");
    }

    /** And each of them is an order somebody wrote, which is what the carrier says. */
    @Test
    void andBothAreAnOrderSomebodyWrote() {
        assertInstanceOf(RuleReasons.AsWritten.class, standingOn(COSTLY_THEN_UNREAD));
        assertInstanceOf(RuleReasons.AsWritten.class, standingOn(UNREAD_THEN_COSTLY));
    }

    /** The words the question's rule left, in the order they are held in. */
    private static List<BlockReason.RuleReadingStopped> saidOf(String source) {
        return standingOn(source).reasons();
    }

    /** What every question of every rule that nothing answered stands on, of the one rule here. */
    private static RuleReasons standingOn(String source) {
        List<RuleReasons> found = new ArrayList<>();
        read(source).accounting().values().forEach(accounting ->
                accounting.unansweredQuestions().forEach(each ->
                        found.add(each.why().stopped().itsRuleLeft())));
        assertEquals(1, found.size(), "one rule, one position, one question that nothing answered");
        return found.getFirst();
    }

    private static FieldDomains read(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        assertEquals(List.of(), compilation.diagnostics().values().stream()
                .flatMap(List::stream).map(each -> each.diagnostic().code()).toList(),
                "the model this reads has to be one somebody could write");
        Symbols symbols = Scopes.derived(compilation.db(), "demo").value();
        TypeSymbol.AtModule name = TypeSymbols.declared(new TypeKey(symbols.module(), "N"));
        return FieldDomains.of(name, RuleReadings.of(compilation, "demo"),
                souther.compiler.query.ReadAs.THE_COMPILATION_DOES);
    }
}
