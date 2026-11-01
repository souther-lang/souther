package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.partition.Generator;
import souther.compiler.query.Adequacy;
import souther.compiler.query.BorderAssessment;
import souther.compiler.query.Compilation;
import souther.compiler.query.ItemAssessment;
import souther.compiler.report.AdequacyReport;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A class of one reading of a comparison that the cases of the other readings cover has no row at
 * it, since a row in the case of another reading is a row of that reading. It is proved empty and
 * not searched until a figure of this compiler's stops the search, and what it comes to is the
 * refutation of that point and not a gap an author is asked to close.
 *
 * <p>{@code clamp(n) == 50} is read twice: {@code n == 50} where {@code n <= 50}, and {@code n >
 * 50} where {@code n /= 50}. The class above the first line, {@code 51 < n}, lies in the case of
 * the second; the class of the same values above the second line is a different point and is owed
 * a row.
 */
class AClassTheOtherReadingsOfAComparisonCoverIsNotSearchedForTest {

    private static final String CLAMPED_EQUALITY = """
            module m

            behavior clamp : (n: Int) -> Int

            let clamp (n) = if n > 50 then 50 else n

            behavior full : (n: Int) -> Bool

            let full (n) = clamp(n) == 50

            example full
                | (50) -> true
                | (49) -> false
                | (0) -> false
            """;

    private static boolean leftNoValue(ItemAssessment.Attempt attempt) {
        return attempt instanceof ItemAssessment.Attempt.Unresolved unresolved
                && unresolved.why().reason()
                        == Generator.UnresolvedCombination.Reason.NO_VALUE_CAN_STAND_THERE;
    }

    private static Compilation measured() {
        Compilation compilation = Compilation.ofSource(CLAMPED_EQUALITY, "Main");
        assertTrue(compilation.errors().isEmpty(), () -> "the model compiles: " + compilation.errors());
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation;
    }

    @Test
    void theClassTheOtherReadingCoversIsRefutedAndNotBlamedOnAFigure() {
        Compilation compilation = measured();
        String human = AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));

        assertTrue(human.contains(
                "read as full/n: in 51 < n (line 1 of 2) — no value can stand at 51 < n"), human);
        assertFalse(human.contains("how many values a point is tried with"), human);
        assertFalse(human.contains("no row is at an OUT point"), human);
    }

    @Test
    void theSameValuesAboveTheOtherLineAreStillOwedARow() {
        Compilation compilation = measured();
        String human = AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));

        assertTrue(human.contains("no row is at an IN point"), human);
        assertTrue(human.contains("no row is at the ON point"), human);
    }

    /**
     * Of the two points that read {@code 51 < n}, one is refuted by the search and the other is
     * not. The refuted one carries no proof of its own that a value stands there: a class outside
     * its case is a row for the comparison to come out as the class says, which the position's
     * declarations say nothing of.
     */
    @Test
    void theRefutedPointIsSettledByTheSearchAloneAndTheOtherIsNot() {
        Compilation compilation = measured();
        Map<String, List<BorderAssessment>> all =
                Adequacy.readingsOf(compilation.db(), compilation.modules().get(0));
        assertNotNull(all, () -> "the model compiles: " + compilation.errors());
        List<ItemAssessment.Owed> above = BorderAssessment.pointsOf(all.get("full")).stream()
                .filter(point -> point.label() != null && point.label().contains("51 < n"))
                .map(BorderAssessment.Point::item)
                .filter(ItemAssessment.Owed.class::isInstance)
                .map(ItemAssessment.Owed.class::cast)
                .toList();

        assertEquals(2, above.size(), () -> "the two points above 51: " + above);
        List<ItemAssessment.Owed> refuted = above.stream()
                .filter(owed -> !owed.searches().each().isEmpty()
                        && owed.searches().each().stream().allMatch(
                                AClassTheOtherReadingsOfAComparisonCoverIsNotSearchedForTest::
                                        leftNoValue))
                .toList();
        assertEquals(1, refuted.size(), () -> "one of them is refuted: " + above);
        assertFalse(refuted.getFirst().projection().proves(), () -> "by the search alone: " + refuted);
    }
}
