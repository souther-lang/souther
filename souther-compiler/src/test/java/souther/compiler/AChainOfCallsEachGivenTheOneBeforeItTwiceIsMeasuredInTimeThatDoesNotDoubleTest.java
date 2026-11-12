package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.time.Duration;

import static org.junit.jupiter.api.Assertions.assertTimeoutPreemptively;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * An equality over the answer of the last of a chain of calls, each handed the one before it
 * twice, is measured in what grows with the calls and not with the paths through them.
 */
class AChainOfCallsEachGivenTheOneBeforeItTwiceIsMeasuredInTimeThatDoesNotDoubleTest {

    private static String reportOfChain(int depth, String comparison) {
        return reportOfChainEndingIn(depth, "LAST " + comparison + " j");
    }

    private static String reportOfChainEndingIn(int depth, String ending) {
        StringBuilder body = new StringBuilder("{\n    let a0 = x\n");
        for (int i = 1; i <= depth; i++) {
            body.append("    let a%d = Int.floorMod(a%d, a%d)\n".formatted(i, i - 1, i - 1));
        }
        body.append("    " + ending.replace("LAST", "a" + depth) + "\n}");
        Compilation compilation = Compilation.ofSource("""
                module m

                behavior f : (x: Int, j: Int) -> Bool
                let f (x, j) = %s
                """.formatted(body), "Main");
        compilation.measure(Adequacy.Asked.reportOnly(Adequacy.Level.ALL));
        compilation.answerEverything();
        return AdequacyReport.of(compilation)
                .humanInEnglish(SourceRendering.namedByIdentity(compilation.texts()));
    }

    private static String reportOfNamesThatReachEachOther(int depth) {
        StringBuilder body = new StringBuilder("{\n    let a0 = x\n    let b0 = j\n");
        for (int i = 1; i <= depth; i++) {
            body.append("    let a%d = Int.floorMod(a%d, b%d)\n".formatted(i, i - 1, i - 1));
            body.append("    let b%d = Int.floorMod(b%d, a%d)\n".formatted(i, i - 1, i - 1));
        }
        body.append("    a%d == b%d\n}".formatted(depth, depth));
        Compilation compilation = Compilation.ofSource("""
                module m

                behavior f : (x: Int, j: Int) -> Bool
                let f (x, j) = %s
                """.formatted(body), "Main");
        compilation.measure(Adequacy.Asked.reportOnly(Adequacy.Level.ALL));
        compilation.answerEverything();
        return AdequacyReport.of(compilation)
                .humanInEnglish(SourceRendering.namedByIdentity(compilation.texts()));
    }

    private static String reportOfTruthsEachMadeOfTheOneBefore(int depth, String step) {
        StringBuilder body = new StringBuilder("{\n    let a0 = x >= 0\n");
        for (int i = 1; i <= depth; i++) {
            body.append("    let a%d = %s\n".formatted(i, step.replace("PREV", "a" + (i - 1))));
        }
        body.append("    a%d\n}".formatted(depth));
        Compilation compilation = Compilation.ofSource("""
                module m

                behavior f : (x: Int, j: Int) -> Bool
                let f (x, j) = %s
                """.formatted(body), "Main");
        compilation.measure(Adequacy.Asked.reportOnly(Adequacy.Level.ALL));
        compilation.answerEverything();
        return AdequacyReport.of(compilation)
                .humanInEnglish(SourceRendering.namedByIdentity(compilation.texts()));
    }

    /** What is said of a truth does not depend on how many names it is made through. */
    @Test
    void aTruthMadeOfTheOneBeforeItTwiceIsReadOnceForEachNameAndSaysWhatItSaysAtAnyDepth() {
        for (String step : new String[] {"PREV && PREV", "PREV || PREV",
                "if PREV then PREV else PREV"}) {
            String shallow = reportOfTruthsEachMadeOfTheOneBefore(2, step);
            String deep = assertTimeoutPreemptively(Duration.ofSeconds(60),
                    () -> reportOfTruthsEachMadeOfTheOneBefore(100, step));
            org.junit.jupiter.api.Assertions.assertEquals(shallow, deep, step);
        }
    }

    @Test
    void aChainNamedInTheConditionOfAnIfAndInItsArmsIsMeasured() {
        String report = assertTimeoutPreemptively(Duration.ofSeconds(60),
                () -> reportOfChainEndingIn(60, "if LAST == j then LAST > 1 else LAST < j"));
        assertTrue(!report.isEmpty());
    }

    @Test
    void namesThatReachEachOtherAtADepthDoublingWouldNotFinishAreMeasured() {
        String report = assertTimeoutPreemptively(Duration.ofSeconds(60),
                () -> reportOfNamesThatReachEachOther(40));
        assertTrue(!report.isEmpty());
    }

    @Test
    void anEqualityAtADepthThatDoublingWouldNotFinishIsMeasured() {
        for (int depth : new int[] {24, 40, 100}) {
            String report = assertTimeoutPreemptively(Duration.ofSeconds(60),
                    () -> reportOfChain(depth, "=="));
            assertTrue(!report.isEmpty(), "depth " + depth);
        }
    }

    @Test
    void anEqualityIsNotMeasuredInMoreTimeThanTheOrderOverTheSameChain() {
        String ordered = assertTimeoutPreemptively(Duration.ofSeconds(60),
                () -> reportOfChain(24, ">="));
        assertTrue(!ordered.isEmpty());
    }
}
