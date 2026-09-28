package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.partition.Generator;
import souther.compiler.query.About;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.RuleRequirement;
import souther.compiler.query.RuleSearch;
import souther.compiler.query.RuleSettlement;
import souther.compiler.report.AdequacyReport;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A value for a dependency's answer is composed against every demand or against none of them.
 *
 * <p>The composer's half of what a region refusing a constraint means. A reading that meets a
 * condition its region cannot carry says so and goes on: the region it leaves still holds every row
 * that arrives, and what is written down is that the condition is unaccounted for. A composer has no
 * such move. Dropping the demand and composing anyway looks for a value in a region wider than what
 * was demanded, and whatever it finds is handed over as a value that answers the demand.
 *
 * <p>Which a reader saw as a fact about the model. The value composed without the demand took the
 * other rule of the same decision, so one rule was settled as a row having gone elsewhere and the
 * other as a rule no row takes — a gap a strict build refuses over, standing for a model that states
 * nothing of the kind. What is settled now is that nothing was composed to try, for a reason that
 * says where the shortfall is.
 */
class ADemandNoRegionCarriesIsNotComposedAgainstTest {

    /**
     * A decision turning on two positions of an answer that hold records.
     *
     * <p>Records, because a difference between two of them is read from end to end and stands on no
     * order — the one shape a region has to refuse. The demand reaches the composer as a form over
     * both positions, which is what makes this a test of the composer rather than of the reading.
     */
    private static final String RECORDS_COMPARED = """
            module example.demand

            data K = { id: Int }
            data R = { k: K, j: K }
            data Yes
            data No
            data Answer = Yes | No

            behavior look : (at: Int) -> R

            behavior decidesOnRecords : (at: Int) -> Answer
                depends on look
            let decidesOnRecords (at, look) = if look(at).k == look(at).j then Yes else No
            """;

    private static final String BEHAVIOR = "decidesOnRecords";

    /** Nothing is composed for the rules of a decision whose demand no region carries. */
    @Test
    void nothingIsComposedForADemandTheRegionCannotCarry() {
        AdequacyReport.BehaviorReport behavior = reportOf(RECORDS_COMPARED);

        assertFalse(behavior.ruleSettlements().isEmpty(),
                "the body decides, so it has rules a row is looked for at");
        behavior.ruleSettlements().forEach((rule, settled) -> {
            assertInstanceOf(RuleRequirement.Unsettled.NothingWasComposedToTry.class,
                    settled.requirement(),
                    () -> "nothing was composed for " + rule + ": " + settled);
            assertTrue(reasons(settled).contains(
                            Generator.UnresolvedCombination.Reason
                                    .NOTHING_STANDS_IN_FOR_A_DEPENDENCY),
                    () -> "and the reason says which shortfall it is: " + settled);
        });
    }

    /**
     * And no rule of the model is reported as one no row takes.
     *
     * <p>What the value composed without the demand came to, and the half that reaches an author as
     * something to fix. A row composed against rules the demand is not in satisfies the other rule
     * as readily as the one it was composed for, and the rule it left is then a rule nothing was
     * seen taking.
     */
    @Test
    void andNoRuleIsReportedAsOneNoRowTakes() {
        assertTrue(reportOf(RECORDS_COMPARED).reported().stream()
                        .noneMatch(f -> f.finding().about() instanceof About.ARuleNoRowTakes),
                "a rule nothing composed a row for is not a rule no row takes");
    }

    /** The reasons a search that came to nothing came back with. */
    private static List<Generator.UnresolvedCombination.Reason> reasons(RuleSettlement settled) {
        return settled.search() instanceof RuleSearch.CameToNothing(var ways)
                ? ways.stream().map(Generator.UnresolvedCombination::reason).toList()
                : List.of();
    }

    /** The behavior's own part of the report, which is where a settlement per rule is. */
    private static AdequacyReport.BehaviorReport reportOf(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return AdequacyReport.of(compilation).modules().stream()
                .flatMap(module -> module.behaviors().stream())
                .filter(each -> BEHAVIOR.equals(each.name()))
                .findFirst().orElseThrow(
                        () -> new AssertionError("the model under test writes " + BEHAVIOR));
    }
}
