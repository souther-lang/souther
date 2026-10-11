package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.BorderAssessment;
import souther.compiler.query.Compilation;
import souther.compiler.query.ItemAssessment;

import java.util.List;
import java.util.Map;
import java.util.function.Predicate;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A comparison inside a closure that never reads its element is evaluated only where a container
 * the closure is applied over holds something, so a row composed for one of its points is one that
 * stands at the point — read back, and not only built to look like it does.
 *
 * <p>{@code List.any(x -> atLeast > 5, xs)} draws a line on {@code atLeast}. With {@code xs} empty
 * the closure is applied to nothing and the comparison is never evaluated, so a row at the line
 * with {@code xs} empty is a row that never meets it.
 */
class AComparisonInAClosureThatIgnoresTheElementIsOwedARowOnlyWhereTheContainerHoldsOneTest {

    private static final String MODEL = """
            module probe

            data Low
            data High

            behavior pick : (atLeast: Int, xs: List<Int>) -> Low | High
            let pick (atLeast, xs) = if GUARD then High else Low

            example pick
                | "the row" : (9, [1]) -> High
            """;

    /**
     * The entries of a map that files a counter that never moves under the key of each element of
     * {@code xs} are there for some element, so the comparison on the counter is evaluated only
     * where {@code xs} holds something.
     */
    private static final String COUNTS = """
            module probe

            let countsOf (xs: List<String>): Map<String, Int> =
                List.fold((acc, x) -> Map.updateOrInsert(x, 1, n -> n, acc), Map.empty, xs)

            behavior busy : (atLeast: Int, xs: List<String>) -> Map<String, Int>
            let busy (atLeast, xs) =
                Map.filterEntries((_, count) -> count >= atLeast, countsOf(xs))
            """;

    /**
     * One closure handed to two operations over two containers: it is applied by either of them, so
     * the comparison is evaluated where {@code xs} holds something or {@code ys} does.
     */
    private static final String SHARED = """
            module probe

            data Low
            data High

            behavior pick : (atLeast: Int, xs: List<Int>, ys: List<Int>) -> Low | High
            let pick (atLeast, xs, ys) = {
                let over = x -> atLeast > 5
                if List.any(over, xs) || List.any(over, ys) then High else Low
            }

            example pick
                | "the row" : (9, [1], [1]) -> High
            """;

    /**
     * A fold hands its closure an accumulator no container holds and an element of {@code xs}:
     * what enters the closure is {@code xs} holding something, and nothing the accumulator is.
     */
    private static final String FOLDED = """
            module probe

            data Low
            data High

            behavior pick : (atLeast: Int, xs: List<Int>) -> Low | High
            let pick (atLeast, xs) =
                if List.fold((acc, x) -> atLeast > 5, false, xs) then High else Low

            example pick
                | "the row" : (9, [1]) -> High
            """;

    @Test
    void aRowComposedForAFoldHoldsSomethingInTheContainerItWalks() {
        assertEveryRowStandsAtItsPoint(FOLDED, "pick", row -> !isEmpty(row.get(1)));
    }

    @Test
    void aRowComposedForAnAnyOverTheContainerHoldsSomething() {
        assertEveryRowStandsAtItsPoint(MODEL.replace("GUARD", "List.any(x -> atLeast > 5, xs)"),
                "pick", row -> !isEmpty(row.get(1)));
    }

    @Test
    void aRowComposedForAnAllOverTheContainerHoldsSomething() {
        assertEveryRowStandsAtItsPoint(MODEL.replace("GUARD", "List.all(x -> atLeast > 5, xs)"),
                "pick", row -> !isEmpty(row.get(1)));
    }

    @Test
    void aRowComposedForAMapFiledUnderTheKeysOfAListHoldsSomethingInTheList() {
        assertEveryRowStandsAtItsPoint(COUNTS, "busy", row -> !isEmpty(row.get(1)));
    }

    @Test
    void aRowComposedForAClosureSharedByTwoContainersHoldsSomethingInOneOfThem() {
        assertEveryRowStandsAtItsPoint(SHARED, "pick",
                row -> !isEmpty(row.get(1)) || !isEmpty(row.get(2)));
    }

    /**
     * A filter of {@code xs} may be empty where {@code xs} is not, so what holds of {@code xs} says
     * nothing certain of the closure over the filter. A row offered for a point there is one read
     * back standing at it or one that says it was not.
     */
    @Test
    void aRowOfferedOverAContainerThatMayBeEmptyIsOneReadBackOrSaysItWasNot() {
        String source = MODEL.replace("GUARD",
                "List.any(x -> atLeast > 5, List.filter(y -> y > 100, xs))");
        List<ItemAssessment.Owed> searched = searchedPointsOn(source, "pick");
        assertFalse(searched.isEmpty(), "the line on atLeast has points to search");
        for (ItemAssessment.Owed owed : searched) {
            if (owed.searches().only() instanceof ItemAssessment.Attempt.Built built) {
                assertInstanceOf(ItemAssessment.Attempt.Certified.class, built,
                        () -> "a row built at " + owed.criterion() + " reaches the comparison or"
                                + " is not offered as one that does: " + built.row());
            }
        }
    }

    private static boolean isEmpty(String written) {
        return written.replace(" ", "").equals("[]");
    }

    private static void assertEveryRowStandsAtItsPoint(String source, String behavior,
                                                       Predicate<List<String>> holdsSomething) {
        List<ItemAssessment.Owed> searched = searchedPointsOn(source, behavior);
        assertTrue(searched.size() >= 2, () -> "the line on atLeast has points to search: "
                + searched);
        for (ItemAssessment.Owed owed : searched) {
            ItemAssessment.Attempt.Certified certified = assertInstanceOf(
                    ItemAssessment.Attempt.Certified.class, owed.searches().only(),
                    () -> "a row was composed and read back at " + owed.criterion());
            List<String> row = certified.row().inputs().stream()
                    .map(input -> input.text()).toList();
            assertTrue(holdsSomething.test(row),
                    () -> "the row at " + owed.criterion() + " holds nothing the closure is"
                            + " applied over: " + row);
        }
    }

    private static List<ItemAssessment.Owed> searchedPointsOn(String source, String behavior) {
        return BorderAssessment.pointsOf(lines(source, behavior)).stream()
                .filter(point -> point.label() != null && point.label().contains("atLeast"))
                .map(BorderAssessment.Point::item)
                .filter(ItemAssessment.Owed.class::isInstance)
                .map(ItemAssessment.Owed.class::cast)
                .filter(ItemAssessment.Owed::worthSearching)
                .toList();
    }

    private static List<BorderAssessment> lines(String source, String behavior) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        Map<String, List<BorderAssessment>> all =
                Adequacy.readingsOf(compilation.db(), compilation.modules().get(0));
        assertNotNull(all, () -> "the model under test compiles: " + compilation.errors().stream()
                .map(each -> each.diagnostic().code() + " " + each.diagnostic().values()).toList());
        assertTrue(all.containsKey(behavior), () -> "lines of " + behavior + ": " + all.keySet());
        return all.get(behavior);
    }
}
