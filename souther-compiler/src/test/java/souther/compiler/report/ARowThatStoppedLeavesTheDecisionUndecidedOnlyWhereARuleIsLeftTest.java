package souther.compiler.report;

import souther.compiler.query.DecisionEvidence;
import souther.compiler.query.Measurement;
import souther.compiler.query.Weakening;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A row that stopped before anything recorded where it went leaves the decision undecided only
 * where a rule is left for it to take.
 *
 * <p>The decision has two rules. The row that stopped is one nobody watched, and a rule nothing was
 * seen taking may be taken by it. Where the rows beside it take both, there is nothing for it to
 * take and the count is exact without it.
 */
class ARowThatStoppedLeavesTheDecisionUndecidedOnlyWhereARuleIsLeftTest {

    private static String model(String rows) {
        return """
                module m

                data Kept = Int
                data Dropped
                data Outcome = Kept | Dropped

                behavior sort : (n: Int) -> Outcome

                let sort (n) = if n >= 0 then Kept(n) else Dropped

                partial let spin (n: Int) : Int = if n < 0 then 0 else spin(n + 1)

                example sort
                    | "spins" : (spin(1)) -> Kept(0)
                """ + rows;
    }

    private static DecisionEvidence theDecision(AdequacyReport report) {
        return report.modules().getFirst().behaviors().getFirst().evidence().decision();
    }

    /** Both rules are taken by the rows that came back. */
    @Test
    void everyRuleTakenLeavesTheDecisionComplete() {
        AdequacyReport report = WrittenWitness.refusedOnly(List.of("E1910"), model(
                "    | \"kept\" : (5) -> Kept(5)\n    | \"dropped\" : (-1) -> Dropped\n"));
        DecisionEvidence decision = theDecision(report);

        assertEquals(1, decision.took().made().orElseThrow().rowsNotWatched(),
                "the row that stopped is still counted as one nothing watched");
        assertInstanceOf(Measurement.Complete.class, decision.took(),
                () -> "no rule is left for it to take: " + decision.took());
    }

    /** One rule is left, and the row that stopped may be the one that takes it. */
    @Test
    void aRuleLeftLeavesTheDecisionUndecided() {
        AdequacyReport report = WrittenWitness.refusedOnly(List.of("E1910"), model(
                "    | \"kept\" : (5) -> Kept(5)\n"));
        DecisionEvidence decision = theDecision(report);

        Measurement.Partial<?> partial = assertInstanceOf(Measurement.Partial.class,
                decision.took(), () -> "the dropped rule may be where it is: " + decision.took());
        assertTrue(partial.weakening().causes().stream()
                        .anyMatch(Weakening.DecisionRunNotWatched.class::isInstance),
                () -> partial.weakening().toString());
    }
}
