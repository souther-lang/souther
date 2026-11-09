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

    /** The rules of the decision no search could settle. */
    private static List<DecisionRule> whatNothingCouldShow(String guard) {
        return DecisionRulesTheSearchLeftUnsettled.in(DEALS.replace("GUARD", guard), "probe");
    }
}
