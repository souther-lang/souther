package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a way states of a difference of two years decides a comparison of that difference only
 * where every difference it leaves comes out the same way. The constants are not nought, so the
 * level the comparison is held at is read the way the statement holds it.
 */
class AWayDecidesARelationOnlyWhereItLeavesOneAnswerTest {

    private static final String POINT_OF_THE_INNER_COMPARISON =
            "whether a row is at the OFF point (comparison@6:";

    private static String report(String comparison) {
        Compilation compilation = Compilation.ofSource("""
                module p

                behavior f : (on: Date, b: Date) -> Bool
                let f (on, b) =
                    if Date.year(on) - Date.year(b) >= 0
                    then Date.year(on) - Date.year(b) >= %s else false
                """.formatted(comparison), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }

    /** Differences of nought and of nine are both left by the way, and ten is between them. */
    @Test
    void aComparisonThatTheDifferencesTheWayLeavesCrossIsNotDecided() {
        assertTrue(report("10").contains(POINT_OF_THE_INNER_COMPARISON), report("10"));
    }

    @Test
    void aComparisonThatEveryDifferenceTheWayLeavesGivesOneAnswerIsDecided() {
        assertFalse(report("-10").contains(POINT_OF_THE_INNER_COMPARISON), report("-10"));
    }
}
