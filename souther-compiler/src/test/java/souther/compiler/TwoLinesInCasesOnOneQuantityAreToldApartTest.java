package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.List;

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

    /**
     * What tells the readings apart comes from the readings and not from the rows: a row added to
     * the model moves none of the words, whichever points it answers.
     */
    @Test
    void theWordsDoNotDependOnTheRowsTheModelHolds() {
        List<String> without = readingsOf(human(CLAMPED));
        List<String> withMore = readingsOf(human(CLAMPED.replace("    | (0) -> false\n",
                "    | (0) -> false\n    | (60) -> false\n    | (51) -> false\n")));
        assertFalse(withMore.isEmpty());
        // A point a row answers is no longer listed; what is listed is said as it was.
        assertTrue(without.containsAll(withMore), () -> without + " and " + withMore);
    }

    private static List<String> readingsOf(String human) {
        return human.lines().map(String::strip).filter(line -> line.startsWith("· read as full/n"))
                .map(line -> line.replaceFirst(" — .*", "")).sorted().toList();
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
