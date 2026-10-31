package souther.compiler;

import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A branch that rules a value out with {@code /=} beside a bound is judged as the same branch
 * written with the strict comparison is.
 *
 * <p>{@code a + b <= 50 && a + b /= 50} leaves the sum at 49 or below, so a construction from the
 * sum discharges an invariant of {@code <= 49} exactly as {@code a + b < 50} does. Every row has the
 * guard written both ways, and the two must agree: which of them an author wrote is not something
 * the language distinguishes.
 */
class ABranchThatRulesOutAValueByAHoleIsJudgedAsTheStrictBranchIsTest {

    private static String model(String guard, String value) {
        return """
                module m

                data Below = Int
                    invariant value <= 49

                data Out = Int

                behavior f : (a: Int, b: Int) -> Below | Out
                    constructs Below, Out

                let f (a, b) =
                    if %s then Below(%s) else Out(0)
                """.formatted(guard, value);
    }

    /** What the discharge check said: the warnings, or the refusal it stopped at. */
    private static List<String> judged(String guard, String value) {
        return judgedWhole(model(guard, value));
    }

    @Test
    void aHoleOnAPositionMovesThePosition() {
        assertEquals(List.of(), judged("a <= 50 && a /= 50", "a"));
    }

    @Test
    void aHoleOnASumMovesThePositionAndTheSum() {
        String hole = "b >= 0 && a + b <= 50 && a + b /= 50";
        assertEquals(List.of(), judged(hole, "a"));
        assertEquals(List.of(), judged(hole, "a + b"));
        assertEquals(List.of(), judged("b >= 0 && a + b < 50", "a + b"));
    }

    @Test
    void theBoundAloneStillOwesTheConstruction() {
        assertEquals(List.of("E2011"), judged("b >= 0 && a + b <= 50", "a"));
        assertEquals(List.of("E2011"), judged("b >= 0 && a + b <= 50", "a + b"));
    }

    @Test
    void aHoleOnADifferenceMovesTheDifference() {
        assertEquals(List.of(), judged("a - b <= 50 && a - b /= 50", "a - b"));
        assertEquals(List.of(), judged("a - b < 50", "a - b"));
    }

    /**
     * Three cases on a total, as the scoring model of the issue writes them: what the first two rule
     * out is what the last one is left with, so the negation of each reaches the final branch. The
     * order the cases are written in is not what discharges.
     */
    @Test
    void whatTheEarlierCasesRuleOutReachesTheLastBranch() {
        String equalFirst = """
                module m

                data Below = Int
                    invariant value <= 49

                data Out = Int

                behavior f : (a: Int, b: Int) -> Below | Out
                    constructs Below, Out

                let f (a, b) =
                    if a + b == 50 then Out(0)
                    else if a + b > 50 then Out(0)
                    else Below(a + b)
                """;
        String greaterFirst = equalFirst.replace("a + b == 50", "a + b > 50").replace(
                "else if a + b > 50", "else if a + b == 50");
        assertEquals(List.of(), judgedWhole(equalFirst));
        assertEquals(List.of(), judgedWhole(greaterFirst));
        assertEquals(List.of("E2011"), judgedWhole(equalFirst.replace("a + b == 50", "a + b == 40")));
    }

    private static List<String> judgedWhole(String model) {
        try {
            return Compiler.compileWithWarnings(model).warnings().stream()
                    .map(Diagnostic::code)
                    .filter(code -> code.startsWith("E20"))
                    .toList();
        } catch (CompileException refused) {
            return List.of(refused.getMessage().substring(0, 5));
        }
    }

    /** The scoring model of the issue: three cases on a total, the first of them a hole. */
    @Test
    void theOrderTheComparisonsAreWrittenInIsNotWhatDischarges() {
        assertEquals(List.of(), judged("a + b <= 50 && b >= 0 && a >= 0 && a + b /= 50", "a + b"));
        assertEquals(List.of(), judged("a + b < 50 && b >= 0 && a >= 0", "a + b"));
    }
}
