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
 * in proved it, and what it is refused by is every word they came back with.
 *
 * <p>A row for a rule is composed once per way of standing them in, and each of those searches is
 * composed in the region its own standing leaves. So what one of them proved is about that region:
 * a rule with a proof under one standing and a row under another is a rule something stands in, and
 * reading the first as the rule's answer would report a way this compiler did reach as one no value
 * takes.
 *
 * <p>And more than one word proves. Two standings may be refused for two reasons, and what a reader
 * is shown may not follow which of them a walk met first — so the words are held in an order of
 * their own, and two runs that walked the ways in two orders hold one value.
 *
 * <p>Put to the quantifier directly. What varies here is the pair of ways, and a model that puts
 * two standings under one rule varies in what the body reads as well — the comparison would be
 * about the difference rather than about the rule the ways are of.
 */
class ARuleIsRefusedOnlyWhereEveryWayOfStandingItInProvesItTest {

    /** Every way of standing the dependencies in proved it, which is the rule's own answer. */
    @Test
    void everyWayProvingItIsTheRulesAnswer() {
        assertEquals(RuleSearch.CameToNothing.by(leavesNothing()),
                Adequacy.DecisionSearch.provedByEveryWay(List.of(proved(), proved())),
                "both standings leave the rule nothing, which is what the model says of it");
    }

    /**
     * Two standings refused for two reasons are refused by both words, in one order.
     *
     * <p>The pair and its mirror, because what makes the order one order is that the walk cannot
     * choose it. Read off the ways as they were met, a model would say one thing and the same model
     * with its arms written the other way round would say the other.
     */
    @Test
    void twoWordsProvingItAreBothHeldAndInOneOrder() {
        RuleSearch.CameToNothing said =
                Adequacy.DecisionSearch.provedByEveryWay(List.of(proved(), cannotBeBoth()));
        RuleSearch.CameToNothing mirrored =
                Adequacy.DecisionSearch.provedByEveryWay(List.of(cannotBeBoth(), proved()));

        assertEquals(said, mirrored,
                "which way a walk met first is not something the rule's account is a function of");
        assertEquals(List.of(leavesNothing(), positionCannotBeBoth()), said.ways(),
                "both words are said, in the order this document says such words in");
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

    private static Generator.UnresolvedCombination leavesNothing() {
        return word(Generator.UnresolvedCombination.Reason.THE_RULES_LEAVE_NOTHING_THERE);
    }

    private static Generator.UnresolvedCombination positionCannotBeBoth() {
        return word(Generator.UnresolvedCombination.Reason.ONE_POSITION_CANNOT_BE_BOTH);
    }

    private static Generator.UnresolvedCombination word(
            Generator.UnresolvedCombination.Reason reason) {
        return new Generator.UnresolvedCombination(List.of("a rule of the decision"), reason);
    }

    private static Generator.BoundaryAttempt proved() {
        return new Generator.BoundaryAttempt.Unresolved(leavesNothing(), NOTHING_LEFT_OUT);
    }

    private static Generator.BoundaryAttempt cannotBeBoth() {
        return new Generator.BoundaryAttempt.Unresolved(positionCannotBeBoth(), NOTHING_LEFT_OUT);
    }

    private static Generator.BoundaryAttempt cameTo(
            Generator.UnresolvedCombination.Reason reason) {
        return new Generator.BoundaryAttempt.Unresolved(word(reason), NOTHING_LEFT_OUT);
    }

    private static Generator.BoundaryAttempt built() {
        return new Generator.BoundaryAttempt.Built(new Generator.GeneratedRow(
                new Generator.Purpose.ForAPoint("a rule of the decision"), List.of()),
                NOTHING_LEFT_OUT);
    }

    private static Generator.BoundaryAttempt stopped() {
        CompositionBudget budget = CompositionBudget.ELEMENTS_A_PROPOSAL_HOLDS;
        return new Generator.BoundaryAttempt.Stopped(new Generator.UnresolvedCombination(
                List.of("a rule of the decision"),
                Generator.UnresolvedCombination.Reason.wordFor(Set.of(budget))),
                EnumSet.of(budget), Set.of(), NOTHING_LEFT_OUT);
    }

    /** These searches are about what a rule's answer is made of and not about what was left out. */
    private static final souther.compiler.partition.CompositionAccount NOTHING_LEFT_OUT =
            souther.compiler.partition.CompositionAccount.NOTHING;
}
