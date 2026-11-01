package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A class of one reading of a comparison that the cases of the other readings cover has no row at
 * it, since a row in the case of another reading is a row of that reading. It is proved empty and
 * not searched until a figure of this compiler's stops the search.
 *
 * <p>{@code clamp(n) == 50} is read twice: {@code n == 50} where {@code n <= 50}, and {@code n >
 * 50} where {@code n /= 50}. The class above the first line, {@code 51 < n}, lies in the case of
 * the second.
 */
class AClassTheOtherReadingsOfAComparisonCoverIsNotSearchedForTest {

    private static final String A_FIGURE_OF_THIS_COMPILER =
            "how many values a point is tried with";

    private static final String CLAMPED_EQUALITY = """
            module m

            behavior clamp : (n: Int) -> Int

            let clamp (n) = if n > 50 then 50 else n

            behavior full : (n: Int) -> Bool

            let full (n) = clamp(n) == 50
            """;

    private static String report(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        assertTrue(compilation.errors().isEmpty(), () -> "the model compiles: " + compilation.errors());
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }

    @Test
    void theClassAboveAnEqualityLineThatTheOtherReadingCoversIsNotBlamedOnAFigure() {
        String human = report(CLAMPED_EQUALITY);

        assertFalse(human.contains(A_FIGURE_OF_THIS_COMPILER), human);
    }
}
