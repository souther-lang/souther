package souther.compiler.query;

import org.junit.jupiter.api.Test;
import souther.compiler.diag.SourceRendering;
import souther.compiler.partition.DecisionReading;
import souther.compiler.partition.DecisionRule;
import souther.compiler.partition.ShownBy;
import souther.compiler.report.AdequacyReport;

import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A call of a behavior of the model that answers a {@code Bool} is a place the run records the
 * answer, as an applied operation of the language is.
 *
 * <p>The rules a body delegating its answer to a named question comes to are the callee's, stated
 * at the call; whether the body writes {@code isFifty(p.score)} or
 * {@code if isFifty(p.score) then true else false} does not change which rules a run is placed at.
 */
class ABoolACallOfABehaviorAnswersIsSeenInTheRunTest {

    private static final String IS_FIFTY = """
            behavior isFifty : (n: Int) -> Bool
            let isFifty (n) = n == 50
            example isFifty
                | (50) -> true
                | (51) -> false
                | (49) -> false
                | (48) -> false
                | (52) -> false
            """;

    private static final String WON = """
            module demo
            data Playing = { score: Int }
            data State = Playing | Out
            behavior won : (s: State) -> Bool
            let won (s) =
                match s with
                    | Out -> false
                    | Playing as p -> isFifty(p.score)
            example won
                | (Playing { score = 0 }) -> false
                | (Out) -> false
                | (Playing { score = 50 }) -> true
            """ + IS_FIFTY;

    private static final String A_TAIL_CALL = """
            module demo
            behavior w : (k: Int) -> Bool
            let w (k) = isFifty(k)
            example w
                | (50) -> true
                | (51) -> false
            """ + IS_FIFTY;

    private static final String A_NEGATED_TAIL_CALL = """
            module demo
            behavior w : (k: Int) -> Bool
            let w (k) = Bool.not(isFifty(k))
            example w
                | (50) -> false
                | (51) -> true
            """ + IS_FIFTY;

    private static final String IN_AN_IF = """
            module demo
            behavior w : (k: Int) -> Bool
            let w (k) = if isFifty(k) then true else false
            example w
                | (50) -> true
                | (51) -> false
            """ + IS_FIFTY;

    private static final String A_CHAIN = """
            module demo
            behavior check : (n: Int) -> Bool
            let check (n) = isFifty(n)
            behavior won : (n: Int) -> Bool
            let won (n) = check(n)
            example check
                | (50) -> true
                | (51) -> false
            example won
                | (50) -> true
                | (51) -> false
            """ + IS_FIFTY;

    private static final String TWICE = """
            module demo
            behavior both : (a: Int, b: Int) -> Bool
            let both (a, b) = isFifty(a) && isFifty(b)
            example both
                | (50, 50) -> true
                | (51, 50) -> false
                | (50, 51) -> false
            """ + IS_FIFTY;

    @Test
    void theModelThatDelegatesItsAnswerEndsSatisfiedWithItsThreeRows() {
        Compilation compilation = Compilation.ofSource(WON, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        String report = AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));

        assertTrue(report.lines().anyMatch(line -> line.contains("decision ")
                && line.contains("rules 3   taken 3")), report);
        assertTrue(report.contains("adequacy: satisfied"), report);
    }

    private static final String IN_A_CLOSURE = """
            module demo
            behavior all : (xs: List<Int>) -> Bool
            let all (xs) = List.fold((acc, x) -> acc && isFifty(x), true, xs)
            example all
                | ([50]) -> true
                | ([51]) -> false
            """ + IS_FIFTY;

    private static final String A_DEPENDENCY = """
            module demo
            behavior ok : (n: Int) -> Bool
            behavior w : (n: Int) -> Bool
                depends on ok
            let w (n, ok) = ok(n)
            example w
                | (1) with ok = true -> true
                | (2) with ok = false -> false
            """;

    private static final String A_BOUND_DEPENDENCY = """
            module demo
            behavior ok : (n: Int) -> Bool
            behavior w : (n: Int) -> Bool
                depends on ok
            let w (n, ok) = {
                let r = ok(n)
                r
            }
            example w
                | (1) with ok = true -> true
                | (2) with ok = false -> false
            """;

    /**
     * A call of a behavior stands in the places an operation of the language's does: inside a
     * closure handed to one, and as a dependency's answer in tail position or bound by a
     * {@code let}. A helper cannot call a behavior, so no copy of one holds a call twice.
     */
    @Test
    void aDependencyAnsweringATruthIsSeenInTailPosition() {
        assertMeasuresWithoutError(A_DEPENDENCY);
    }

    @Test
    void aDependencyAnsweringATruthIsSeenWhereALetBindsIt() {
        assertMeasuresWithoutError(A_BOUND_DEPENDENCY);
    }

    @Test
    void aCallInAClosureIsMeasured() {
        assertMeasuresWithoutError(IN_A_CLOSURE);
    }

    private static void assertMeasuresWithoutError(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        String report = AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code() + " " + each.diagnostic().said())
                .toList(), report);
    }

    @Test
    void aChainOfDelegationsIsMeasuredAtEveryLevel() {
        assertEveryRowIsPlacedAtItsOwnRule(A_CHAIN, "check", 2);
        assertEveryRowIsPlacedAtItsOwnRule(A_CHAIN, "won", 2);
    }

    @Test
    void theSameBehaviorCalledTwiceIsTwoPlacesToBeSeenAt() {
        assertEveryRowIsPlacedAtItsOwnRule(TWICE, "both", 3);
    }

    @Test
    void aTailCallOfABehaviorIsMeasured() {
        assertEveryRowIsPlacedAtItsOwnRule(A_TAIL_CALL, "w", 2);
    }

    @Test
    void aNegatedTailCallOfABehaviorIsMeasured() {
        assertEveryRowIsPlacedAtItsOwnRule(A_NEGATED_TAIL_CALL, "w", 2);
    }

    @Test
    void aCallInAnIfIsMeasuredAsAnyOther() {
        assertEveryRowIsPlacedAtItsOwnRule(IN_AN_IF, "w", 2);
    }

    @Test
    void aCallInTheArmOfAMatchIsMeasured() {
        assertEveryRowIsPlacedAtItsOwnRule(WON, "won", 3);
    }

    private static void assertEveryRowIsPlacedAtItsOwnRule(String model, String behavior,
                                                           int ways) {
        DecisionEvidence evidence = evidenceOf(model, behavior);
        List<DecisionRule> rules = evidence.rules();
        assertEquals(ways, rules.size(), () -> "one rule per way through the body: " + rules);
        for (DecisionReading.Ruled ruled : evidence.read().found()) {
            assertTrue(ruled.shownBy().stream()
                            .noneMatch(shown -> shown instanceof ShownBy.NothingIsRecorded
                                    || shown instanceof ShownBy.ShortOf),
                    () -> "every condition of the rule is seen somewhere: " + ruled.shownBy());
        }
        DecisionEvidence.RowsPlaced placed = evidence.took().made()
                .orElseThrow(() -> new AssertionError("the rows were read: " + evidence.took()));
        assertEquals(ways, placed.rowsPlaced(), () -> "every row is placed at a rule: " + placed);
        assertEquals(Set.copyOf(rules), placed.rules(),
                () -> "and the rows are placed at every rule: " + placed);
    }

    private static DecisionEvidence evidenceOf(String model, String behavior) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation.db().ask(new Adequacy.Decides(compilation.modules().get(0))).value()
                .get(behavior);
    }
}
