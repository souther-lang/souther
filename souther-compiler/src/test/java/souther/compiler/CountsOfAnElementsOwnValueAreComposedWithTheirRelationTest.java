package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.partition.DecisionRule;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A guard over how many elements of a list meet what their own values say, held to how many meet
 * another statement and to how many there are, is composed for both of its answers.
 *
 * <p>Which elements meet each statement is the elements' own, so the list is chosen among the
 * values an element holds, and shared out among the counts the relation holds them to. A relation
 * that no list meets is a rule the search leaves unsettled and not one it shows to be impossible.
 */
class CountsOfAnElementsOwnValueAreComposedWithTheirRelationTest {

    private static final String DEALS = """
            module probe

            data Deal = { amount: Int }
            data Big = { n: Int }
            data Small = { n: Int }

            behavior sized : (deals: List<Deal>) -> Big | Small
                constructs Big, Small

            let sized (deals) = {
                guard GUARD
                    else Small { n = 0 }
                Big { n = 1 }
            }
            """;

    private static final String OVER_A_HUNDRED =
            "List.length(List.filter(d -> d.amount > 100, deals))";

    private static final String OVER_TWO_HUNDRED =
            "List.length(List.filter(d -> d.amount > 200, deals))";

    private static final String LENGTH = "List.length(deals)";

    @Test
    void theElementsOverAThresholdAgainstHowManyThereAreAreComposed() {
        assertEquals(List.of(), whatNothingCouldShow(OVER_A_HUNDRED + " == " + LENGTH));
        assertEquals(List.of(), whatNothingCouldShow("2 * " + OVER_A_HUNDRED + " > " + LENGTH));
        assertEquals(List.of(), whatNothingCouldShow(OVER_A_HUNDRED + " < " + LENGTH));
    }

    @Test
    void theElementsOverOneThresholdAgainstThoseOverAnotherAreComposed() {
        assertEquals(List.of(),
                whatNothingCouldShow(OVER_A_HUNDRED + " > " + OVER_TWO_HUNDRED));
        assertEquals(List.of(),
                whatNothingCouldShow(OVER_A_HUNDRED + " == " + OVER_TWO_HUNDRED));
    }

    /**
     * What another condition leaves of one count is what the relation is composed within: the
     * counts it holds are placed at the fewest it leaves them together, and not at the fewest
     * each leaves alone, so a relation that holds only where another count is not nought is met
     * where that other condition says it is nought.
     */
    @Test
    void aRelationIsComposedWithinWhatAnotherConditionLeavesOfACount() {
        String under = "List.length(List.filter(d -> d.amount < 50, deals))";
        String either = OVER_A_HUNDRED + " + " + under + " == 1";
        assertEquals(List.of(), whatNothingCouldShow(either, under + " == 0"));
        assertEquals(List.of(), whatNothingCouldShow(either, OVER_A_HUNDRED + " == 0"));
    }

    /**
     * A relation is composed at every way of sharing the elements among the counts, and not at
     * the first that the counts alone allow: where the elements' own rules leave none meeting one
     * statement, the elements go to the other, whichever the relation names first.
     */
    @Test
    void aRelationIsComposedAtTheWaysTheElementsLeaveAndNotTheFirstTheCountsAllow() {
        String under = "List.length(List.filter(d -> d.amount < 50, deals))";
        String either = OVER_A_HUNDRED + " + " + under + " == 1";
        String noneUnder = DEALS.replace("data Deal = { amount: Int }",
                "data Deal = { amount: Int }\n    invariant atLeastFifty = amount >= 50");
        String noneOver = DEALS.replace("data Deal = { amount: Int }",
                "data Deal = { amount: Int }\n    invariant atMostAHundred = amount <= 100");
        assertEquals(List.of(), DecisionRulesTheSearchLeftUnsettled.notShownIn(
                noneUnder.replace("GUARD", either), "probe"));
        assertEquals(List.of(), DecisionRulesTheSearchLeftUnsettled.notShownIn(
                noneOver.replace("GUARD", either), "probe"));
    }

    /**
     * A relation only a large container meets is reached by sharing its elements out among the
     * ways they meet the statements: the ways grow with the size, and those the relation leaves
     * no count to are not walked.
     */
    @Test
    void aRelationOnlyALargeContainerMeetsIsComposedAmongManyWaysOfSharing() {
        String under = "List.length(List.filter(d -> d.amount < 50, deals))";
        assertEquals(List.of(), whatNothingCouldShow(
                LENGTH + " - " + OVER_A_HUNDRED + " - " + under + " >= 14"));
    }

    /** More counts than a pair are held to the same relation, and are composed the same. */
    @Test
    void moreThanTwoCountsAreComposedWithTheirRelation() {
        String under = "List.length(List.filter(d -> d.amount < 50, deals))";
        assertEquals(List.of(), whatNothingCouldShow(
                OVER_A_HUNDRED + " + " + under + " + " + OVER_TWO_HUNDRED + " == 2"));
    }

    /**
     * A relation only a container larger than any a count is composed with meets is no relation
     * the model leaves no row: what stopped the search is not shown as the model's own rules.
     */
    @Test
    void aRelationNoContainerComposedMeetsIsNotShownImpossible() {
        assertEquals(List.of(), DecisionRulesTheSearchLeftUnsettled.excludedIn(
                DEALS.replace("GUARD", LENGTH + " - " + OVER_A_HUNDRED + " >= 40"), "probe"));
    }

    private static List<DecisionRule> whatNothingCouldShow(String first, String second) {
        return DecisionRulesTheSearchLeftUnsettled.notShownIn(
                TWO_GUARDS.replace("FIRST", first).replace("SECOND", second), "probe");
    }

    private static final String TWO_GUARDS = """
            module probe

            data Deal = { amount: Int }
            data Big = { n: Int }
            data Small = { n: Int }

            behavior sized : (deals: List<Deal>) -> Big | Small
                constructs Big, Small

            let sized (deals) = {
                guard FIRST
                    else Small { n = 0 }
                guard SECOND
                    else Small { n = 2 }
                Big { n = 1 }
            }
            """;

    /** The rules of the decision no search could settle. */
    private static List<DecisionRule> whatNothingCouldShow(String guard) {
        return DecisionRulesTheSearchLeftUnsettled.notShownIn(DEALS.replace("GUARD", guard),
                "probe");
    }
}
