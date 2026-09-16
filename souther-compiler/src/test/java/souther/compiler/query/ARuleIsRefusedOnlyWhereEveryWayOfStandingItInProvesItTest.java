package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.partition.CompositionBudget;
import souther.compiler.partition.Generator;

import java.util.EnumSet;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;

/**
 * A rule of a decision is one the model refuses only where every way of standing the dependencies
 * in proved it.
 *
 * <p>A row for a rule is composed once per way of standing them in, and each of those searches is
 * composed in the region its own standing leaves. So what one of them proved is about that region:
 * a rule with a proof under one standing and a row under another is a rule something stands in, and
 * reading the first as the rule's answer would report a way this compiler did reach as one no value
 * takes.
 *
 * <p>Put to the quantifier directly. What varies here is the pair of ways, and a model that puts
 * two standings under one rule varies in what the body reads as well — the comparison would be
 * about the difference rather than about the rule the ways are of.
 */
class ARuleIsRefusedOnlyWhereEveryWayOfStandingItInProvesItTest {

    /** Every way of standing the dependencies in proved it, which is the rule's own answer. */
    @Test
    void everyWayProvingItIsTheRulesAnswer() {
        assertEquals(new RuleRequirement.Excluded.TheRulesLeaveNoValueForIt(proof()),
                Adequacy.DecisionSearch.provedByEveryWay(List.of(proved(), proved())),
                "both standings leave the rule nothing, which is what the model says of it");
    }

    /** One of them proving it is a statement about that standing's region and not about the rule. */
    @Test
    void oneWayProvingItBesideARowIsNotTheRulesAnswer() {
        assertNull(Adequacy.DecisionSearch.provedByEveryWay(List.of(proved(), built())),
                "a row was composed under the other standing, so something does stand in the rule");
    }

    /** And one of them proving it beside a search a budget ended is not the rule's answer either. */
    @Test
    void oneWayProvingItBesideASearchThatWasStoppedIsNotTheRulesAnswer() {
        assertNull(Adequacy.DecisionSearch.provedByEveryWay(List.of(proved(), stopped())),
                "the other standing was not searched to the end, so nothing there was proved");
    }

    /** A word about what this compiler managed is not a proof, under any standing. */
    @Test
    void aWordAboutThisCompilerIsNotAProof() {
        assertNull(Adequacy.DecisionSearch.provedByEveryWay(List.of(
                        cameTo(Generator.UnresolvedCombination.Reason.ALL_CANDIDATES_REJECTED))),
                "every candidate refused says nothing about the ones that were not tried");
    }

    /** And no way at all is not every way, which is the classes not linking. */
    @Test
    void noWayAtAllIsNotEveryWay() {
        assertNull(Adequacy.DecisionSearch.provedByEveryWay(List.of()),
                "nothing was searched, so nothing was proved");
    }

    private static Generator.UnresolvedCombination proof() {
        return new Generator.UnresolvedCombination(List.of("a rule of the decision"),
                Generator.UnresolvedCombination.Reason.THE_RULES_LEAVE_NOTHING_THERE);
    }

    private static Generator.BoundaryAttempt proved() {
        return new Generator.BoundaryAttempt.Unresolved(proof(), List.of());
    }

    private static Generator.BoundaryAttempt cameTo(
            Generator.UnresolvedCombination.Reason reason) {
        return new Generator.BoundaryAttempt.Unresolved(new Generator.UnresolvedCombination(
                List.of("a rule of the decision"), reason), List.of());
    }

    private static Generator.BoundaryAttempt built() {
        return new Generator.BoundaryAttempt.Built(new Generator.GeneratedRow(
                new Generator.Purpose.ForAPoint("a rule of the decision"), List.of()), List.of());
    }

    private static Generator.BoundaryAttempt stopped() {
        CompositionBudget budget = CompositionBudget.ELEMENTS_A_PROPOSAL_HOLDS;
        return new Generator.BoundaryAttempt.Stopped(new Generator.UnresolvedCombination(
                List.of("a rule of the decision"),
                Generator.UnresolvedCombination.Reason.wordFor(Set.of(budget))),
                EnumSet.of(budget), Set.of(), List.of());
    }
}
