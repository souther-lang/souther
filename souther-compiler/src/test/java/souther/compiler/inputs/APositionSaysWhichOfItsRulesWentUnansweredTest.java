package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.ast.Hir;
import souther.compiler.check.CoverageObligation;
import souther.compiler.check.Owed;
import souther.compiler.check.Prepared;
import souther.compiler.check.RuleAccounting;
import souther.compiler.check.Sig;
import souther.compiler.check.Symbols;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.Scopes;
import souther.compiler.query.Shapes;
import souther.compiler.values.AdmissibleSet;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A position says which of its rules went unanswered, and that is not what a reading says of
 * itself.
 *
 * <p>The models of issue #842. Both bound a numeric newtype and divide it with a guard, and the
 * reading that turns clauses into sets of values is short of the position's rules in both — it has
 * no word for a range. Asked of that reading, the two are the same model. Asked of the rules, they
 * are not: in the first every clause was taken in by something, and in the second one was taken in
 * by nothing.
 */
class APositionSaysWhichOfItsRulesWentUnansweredTest {

    /** The issue's model: an ordering invariant, and a guard dividing what it bounds. */
    private static final String EVERY_RULE_ANSWERED = """
            module example.rooms

            data Length = Int
                invariant min = value >= 1
                invariant max = value <= 100

            behavior price : (length: Length) -> Int
            let price (length) =
                if length.value >= 50 then 1 else 2
            """;

    /** The same, with a clause neither reading takes in. */
    private static final String ONE_RULE_UNANSWERED = """
            module example.rooms

            data Length = Int
                invariant min = value >= 1
                invariant max = value <= 100
                invariant even = value * value >= 4

            behavior price : (length: Length) -> Int
            let price (length) =
                if length.value >= 50 then 1 else 2
            """;

    private static Position positionOf(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        String module = compilation.modules().get(0);
        Prepared prepared = compilation.db().ask(new Shapes.Prepared(module)).value();
        Map<String, Sig> sigs = compilation.db().ask(new Bodies.Signatures(module)).value();
        assertNotNull(prepared);
        assertNotNull(sigs);
        Hir.SpecBehavior spec = (Hir.SpecBehavior) prepared.behaviors().stream()
                .filter(b -> b.name().equals("price")).findFirst().orElseThrow();
        Symbols symbols = Scopes.derived(compilation.db(), module).value();
        return InputDomain.of(spec, sigs.get("price"), symbols, souther.compiler.check.ReadAs.THE_COMPILATION_DOES).positions().stream()
                .filter(p -> p.path().toString().equals("length"))
                .findFirst().orElseThrow();
    }

    /**
     * Every rule taken in, and the reading of values short of them all the same.
     *
     * <p>The pair of assertions is the point. The completeness beside the position says what it has
     * always said; what changed is that a report may no longer read it as the model having gone
     * unread.
     */
    @Test
    void aBoundIsAnsweredEvenWhereTheReadingOfValuesIsShort() {
        Position length = positionOf(EVERY_RULE_ANSWERED);

        assertEquals(List.of(), length.unansweredQuestions(),
                "both bounds were taken in, by the reading that turns them into ends");
        assertInstanceOf(AdmissibleSet.Completeness.Wider.class, length.completeness(),
                "and the reading of values is short of the rules, as it always was");
    }

    /**
     * A clause nothing took in leaves its question standing, and the question names the clause.
     *
     * <p>Which is what the report never had. An author was told that a rule about the position went
     * unread, with nothing saying which rule — two lines above a boundary drawn from one of the
     * rules the sentence was about.
     */
    @Test
    void aClauseNothingTookInIsNamed() {
        List<RuleAccounting.Unanswered> open = positionOf(ONE_RULE_UNANSWERED)
                .unansweredQuestions();

        assertEquals(1, open.size(), () -> "one clause, one question: " + open);
        assertEquals("invariant Length (even)", open.get(0).rule().named(),
                "the clause the author wrote, as a report names it — and not the position it "
                        + "is about");
        assertEquals(CoverageObligation.ADMITTED_VALUES, open.get(0).owed().obligation());
        assertTrue(open.get(0).owed().subject() instanceof Owed.Subject.OfAPosition at
                        && at.path().isEmpty(),
                () -> "about the value the newtype wraps: " + open.get(0).owed().subject());
    }
}
