package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import static souther.compiler.partition.AComparisonInAClosureThatIgnoresTheElementIsOwedARowOnlyWhereTheContainerHoldsOneTest.assertEveryRowStandsAtItsPoint;
import static souther.compiler.partition.AComparisonInAClosureThatIgnoresTheElementIsOwedARowOnlyWhereTheContainerHoldsOneTest.isEmpty;

/**
 * A closure written once and applied more than once is one rule that a run reaches through any of
 * the copies the applications make.
 *
 * <p>{@code over(0) || over(1)} states {@code atLeast > 5} once, and the tree holds a copy of it for
 * each application. A row at its line is one that reaches the comparison through some copy, so what
 * it owes is what every copy asks and no more — and where the copies ask different things, one
 * proving a value exists at the point is the point proved.
 */
class AClosureAppliedMoreThanOnceIsOneRuleReachedByEachOfItsCopiesTest {

    private static final String HEAD = """
            module probe

            data Low
            data High

            let apply (f: (Int) -> Bool): Bool = f(0)

            behavior pick : (atLeast: Int, xs: List<Int>) -> Low | High
            """;

    @Test
    void aClosureAppliedTwiceDirectlyIsOneRule() {
        assertEveryRowStandsAtItsPoint(HEAD + """
                let pick (atLeast, xs) = {
                    let over = x -> atLeast > 5
                    if over(0) || over(1) then High else Low
                }
                """, "pick", row -> true);
    }

    @Test
    void aClosureHandedTwiceToOneHelperIsOneRule() {
        assertEveryRowStandsAtItsPoint(HEAD + """
                let pick (atLeast, xs) = {
                    let over = x -> atLeast > 5
                    if apply(over) || apply(over) then High else Low
                }
                """, "pick", row -> true);
    }

    /**
     * The helper applies the closure with no container, so the comparison is reached whatever
     * {@code xs} holds, and a row is not held to {@code xs} holding something. With the model
     * holding it empty, a row that does is a row the model refuses.
     */
    @Test
    void aClosureAlsoHandedToAHelperIsNotHeldToTheContainerOfItsOperation() {
        assertEveryRowStandsAtItsPoint(HEAD + """
                let pick (atLeast, xs) = {
                    guard List.isEmpty(xs) else Low
                    let over = x -> atLeast > 5
                    if apply(over) || List.any(over, xs) then High else Low
                }
                """, "pick", row -> isEmpty(row.get(1)));
    }
}
