package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.BorderAssessment;
import souther.compiler.query.Compilation;
import souther.compiler.query.ItemAssessment;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A comparison inside a closure that never reads its element is evaluated only where the
 * container the closure is applied over holds something, so a row composed for one of its points
 * holds something.
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

    @Test
    void aRowComposedForAnAnyOverTheContainerHoldsSomething() {
        assertEveryRowHoldsSomething(MODEL.replace("GUARD", "List.any(x -> atLeast > 5, xs)"),
                "pick");
    }

    @Test
    void aRowComposedForAnAllOverTheContainerHoldsSomething() {
        assertEveryRowHoldsSomething(MODEL.replace("GUARD", "List.all(x -> atLeast > 5, xs)"),
                "pick");
    }

    @Test
    void aRowComposedForAMapFiledUnderTheKeysOfAListHoldsSomethingInTheList() {
        assertEveryRowHoldsSomething(COUNTS, "busy");
    }

    /**
     * A filter of {@code xs} may be empty where {@code xs} is not, so the closure over it asks
     * nothing of {@code xs} having an element.
     */
    @Test
    void aContainerThatMayBeEmptyWhereWhatItIsMadeOfIsNotAsksNothingOfThat() {
        String source = MODEL.replace("GUARD",
                "List.any(x -> atLeast > 5, List.filter(y -> y > 100, xs))");
        List<ItemAssessment.Owed> searched = BorderAssessment.pointsOf(lines(source, "pick"))
                .stream()
                .filter(point -> point.label() != null && point.label().contains("atLeast"))
                .map(BorderAssessment.Point::item)
                .filter(ItemAssessment.Owed.class::isInstance)
                .map(ItemAssessment.Owed.class::cast)
                .filter(ItemAssessment.Owed::worthSearching)
                .toList();
        assertFalse(searched.isEmpty(), "the line on atLeast has points to search");
        for (ItemAssessment.Owed owed : searched) {
            assertFalse(owed.searches().toString().contains("List.length(xs)"),
                    () -> "xs holding something is no condition of the closure's being applied: "
                            + owed.searches());
        }
    }

    private static void assertEveryRowHoldsSomething(String source, String behavior) {
        List<ItemAssessment.Owed> searched = BorderAssessment.pointsOf(lines(source, behavior))
                .stream()
                .filter(point -> point.label() != null && point.label().contains("atLeast"))
                .map(BorderAssessment.Point::item)
                .filter(ItemAssessment.Owed.class::isInstance)
                .map(ItemAssessment.Owed.class::cast)
                .filter(ItemAssessment.Owed::worthSearching)
                .toList();
        assertTrue(searched.size() >= 2, () -> "the line on atLeast has points to search: "
                + searched);
        for (ItemAssessment.Owed owed : searched) {
            ItemAssessment.Attempt.Built built = assertInstanceOf(
                    ItemAssessment.Attempt.Built.class, owed.searches().only(),
                    () -> "a row was composed at " + owed.criterion());
            String xs = built.row().inputs().get(1).text();
            assertFalse(xs.replace(" ", "").equals("[]"),
                    () -> "the row at " + owed.criterion() + " holds nothing in xs: " + xs);
        }
    }

    private static List<BorderAssessment> lines(String source, String behavior) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        Map<String, List<BorderAssessment>> all =
                Adequacy.readingsOf(compilation.db(), compilation.modules().get(0));
        assertNotNull(all, "the model under test compiles");
        assertTrue(all.containsKey(behavior), () -> "lines of " + behavior + ": " + all.keySet());
        return all.get(behavior);
    }
}
