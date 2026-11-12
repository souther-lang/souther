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
        StringBuilder body = new StringBuilder("{\n    let a0 = x\n");
        for (int i = 1; i <= depth; i++) {
            body.append("    let a%d = Int.floorMod(a%d, a%d)\n".formatted(i, i - 1, i - 1));
        }
        body.append("    a%d %s j\n}".formatted(depth, comparison));
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
