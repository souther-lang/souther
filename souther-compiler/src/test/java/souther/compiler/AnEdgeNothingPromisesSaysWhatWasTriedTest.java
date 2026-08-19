package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceNameResolver;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * An edge nothing has shown to be writable says what was tried, not only that nothing was.
 *
 * <p>A line the rules draw is not counted until a concrete value is accepted at it, and a search
 * that composed nothing settles nothing either way. That is the semantics, and read off the report
 * alone it looks like an accident: the same four lines are counted in one model and not in another
 * that differs by a constraint on a field they have nothing to do with.
 *
 * <p>What separates the two is which facts the compiler managed to establish, and it is the one
 * thing the line does not say. An author who cannot see that reads it as the tool being unreliable
 * rather than as the tool being honest about what it could not prove.
 */
class AnEdgeNothingPromisesSaysWhatWasTriedTest {

    /** A disequality nothing can project, and a sibling whose pattern nothing can write. */
    private static final String MODEL = """
            module example.d4

            data Ok

            data Amount = Int
                invariant range = value >= 0 && value <= 100

            data Tag = String
                invariant shape = String.matches("(a+)\\\\1", value)

            data Pair = { low: Amount, high: Amount, tag: Tag }
                invariant together = low.value /= high.value

            behavior check : (p: Pair) -> Ok
                constructs Ok

            let check (p) = Ok

            example check
                | "a pair" : (Pair { low = Amount(5), high = Amount(7), tag = Tag("aa") }) -> Ok
            """;

    private static String report() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.measure(Adequacy.Asked.reportOnly());
        compilation.answerEverything();
        return AdequacyReport.of(compilation).human(SourceNameResolver.identity());
    }

    /** The line is still said, which is what keeps a discovered edge from disappearing. */
    @Test
    void theEdgeIsStillNamed() {
        String human = report();

        assertTrue(human.contains("not known to be writable: the ON point check/p.low = 0"), human);
    }

    /** And it says what the search came to, so the verdict is legible rather than surprising. */
    @Test
    void theLineSaysWhatTheSearchCameTo() {
        String human = report();

        String line = human.lines()
                .filter(each -> each.contains("not known to be writable: the ON point check/p.low = 0"))
                .findFirst().orElseThrow(() -> new AssertionError(human));

        assertTrue(line.contains("nothing composed one"), line);
    }
}
