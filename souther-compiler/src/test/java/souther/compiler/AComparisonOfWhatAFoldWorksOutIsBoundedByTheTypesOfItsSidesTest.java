package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A comparison whose sides a run works out is held to what the types of its sides leave them: a
 * point past the end of a newtype's value is one no row can reach, and is said to be that rather
 * than left undecided.
 */
class AComparisonOfWhatAFoldWorksOutIsBoundedByTheTypesOfItsSidesTest {

    private static final String SCORING = """
            module m

            data Points = Int
                invariant value >= 0 && value <= 12

            data Score = Int
                invariant value >= 0 && value <= 50

            behavior add : (before: Score, p: Points) -> Score

            let add (before, p) = {
                let sum = before.value + p.value
                if sum > 50 then Score(25) else Score(sum)
            }

            example add
                | (Score(48), Points(3)) -> Score(25)
                | (Score(25), Points(10)) -> Score(35)
                | (Score(48), Points(2)) -> Score(50)
                | (Score(0), Points(0)) -> Score(0)
                | (Score(40), Points(12)) -> Score(25)
                | (Score(50), Points(0)) -> Score(50)
                | (Score(38), Points(12)) -> Score(50)

            behavior total : (ps: List<Points>) -> Score

            let total (ps) = List.fold((s, p) -> add(s, p), Score(0), ps)

            example total
                | ([]) -> Score(0)
                | ([Points(5), Points(5)]) -> Score(10)

            """;

    private static final String REACHED_ROWS = """
            example reached
                | ([]) -> false
                | ([Points(5), Points(5)]) -> false
                | ([Points(12), Points(12), Points(12), Points(12), Points(1)]) -> false
                | ([Points(12), Points(12), Points(12), Points(12), Points(2)]) -> true
            """;

    private static String reportOf(String body) {
        Compilation compilation = Compilation.ofSource(SCORING + body, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code()).toList(), "the model under test compiles");
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }

    private static String reached(String condition) {
        return reportOf("""
                behavior reached : (ps: List<Points>) -> Bool

                let reached (ps) = %s

                """.formatted(condition) + REACHED_ROWS);
    }

    @Test
    void thePointsPastTheEndOfTheAnswersTypeAreExcluded() {
        String report = reached("total(ps).value == 50");
        assertTrue(report.contains("adequacy: satisfied"), report);
    }

    @Test
    void theSidesWrittenTheOtherWayRoundAreBoundedAlike() {
        String report = reached("50 == total(ps).value");
        assertTrue(report.contains("adequacy: satisfied"), report);
    }

    /** The same rows against a number no type bounds: nothing says the points are out of reach. */
    @Test
    void aSideNoTypeBoundsLeavesThePointsUndecided() {
        String report = reportOf("""
                behavior thrown : (ps: List<Points>) -> Int

                let thrown (ps) = List.fold((s, p) -> s + p.value, 0, ps)

                example thrown
                    | ([]) -> 0
                    | ([Points(5), Points(5)]) -> 10

                behavior reached : (ps: List<Points>) -> Bool

                let reached (ps) = thrown(ps) == 50

                """ + REACHED_ROWS);
        assertFalse(report.contains("adequacy: satisfied"), report);
    }
}
