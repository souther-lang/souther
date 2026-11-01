package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A comparison read back through a callee that branches on the quantity is drawn once per arm, and
 * the lines are told apart by the case each decides in, also when that case is about the quantity
 * the point is at.
 */
class TwoLinesInCasesOnOneQuantityAreToldApartTest {

    private static final String CLAMPED = """
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

    private static String human(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }

    @Test
    void theOnPointAndTheOffPointOfTheSameValueAreSaidInTheirOwnCases() {
        String human = human(CLAMPED);
        assertTrue(human.contains("read as full/n: = 51 where n /= 50"), human);
        assertTrue(human.contains("read as full/n: = 51 where n <= 50"), human);
    }

    /** A comparison that is one line in one case has nothing for a case to tell apart. */
    @Test
    void aSingleComparisonSaysNoCase() {
        String human = human("""
                module m

                behavior big : (n: Int) -> Bool

                let big (n) = n > 50

                example big
                    | (51) -> true
                    | (50) -> false
                """);
        assertTrue(human.contains("read as big/n"), human);
        assertFalse(human.contains(" where "), human);
    }
}
