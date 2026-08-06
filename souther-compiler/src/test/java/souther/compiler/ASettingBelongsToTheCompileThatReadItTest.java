package souther.compiler;

import souther.compiler.observe.FailurePhase;
import souther.compiler.observe.RowOutcome;
import souther.compiler.query.Compilation;
import souther.compiler.query.Output;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What a compile is held to is what the settings said when it started.
 *
 * <p>Read once into a static, a setting is fixed for the life of the JVM — which is the wrong answer
 * in every long-lived one. A build daemon and an editor's language server both outlive the compile a
 * setting was written for, so the compile that reads it is not the compile it was meant for, and
 * changing it has no effect at all until the process is restarted.
 */
class ASettingBelongsToTheCompileThatReadItTest {

    private static final String COUNTS_DOWN = """
            module example.setting
            data N = Int
            data Out = Int
            partial let spin (n: Int): Int = if n == 0 then 0 else spin(n - 1)
            behavior run : (n: N) -> Out constructs Out
            let run (n) = Out(spin(n.value))
            example run
              | "counts down": (N(2000)) -> Out(0)
            """;

    private static RowOutcome onlyRow() {
        Compilation compilation = Compilation.ofSource(COUNTS_DOWN, "Main");
        compilation.answerEverything();
        String sourceId = compilation.exampleSourcesOf("example.setting").get(0);
        List<RowOutcome> rows = compilation.db()
                .ask(new Output.Examples("example.setting", sourceId, Output.CoverageMode.NONE))
                .value().rows();
        assertEquals(1, rows.size(), rows.toString());
        return rows.get(0);
    }

    /**
     * Two compiles in one JVM, with the setting changed between them, are held to what each read.
     *
     * <p>Both are run here rather than one, because a setting that is never read again gives the
     * right answer for the first compile and the wrong one for every compile after it — and a test
     * that only ran the second would pass on an implementation that read it once and one that reads
     * it each time.
     */
    @Test
    void aSettingChangedBetweenTwoCompilesReachesTheSecond() {
        String before = System.getProperty("souther.example.step.limit");
        try {
            System.setProperty("souther.example.step.limit", "100000000");
            assertEquals(FailurePhase.NONE, onlyRow().failurePhase(),
                    "with steps to spare the row comes back");

            System.setProperty("souther.example.step.limit", "100");
            assertEquals(FailurePhase.STEP_LIMIT, onlyRow().failurePhase(),
                    "the compile after the change is held to what it says");
        } finally {
            if (before == null) {
                System.clearProperty("souther.example.step.limit");
            } else {
                System.setProperty("souther.example.step.limit", before);
            }
        }
    }

    /** A setting written as something that is not a positive number leaves the default in place: a
     *  typo in a build script is not a reason to refuse to compile a model. */
    @Test
    void aSettingThatIsNotANumberLeavesTheDefaultInPlace() {
        String before = System.getProperty("souther.example.step.limit");
        try {
            System.setProperty("souther.example.step.limit", "soon");

            assertEquals(EvaluationPolicy.DEFAULT_STEP_LIMIT,
                    EvaluationPolicy.fromSettings().stepLimit());
        } finally {
            if (before == null) {
                System.clearProperty("souther.example.step.limit");
            } else {
                System.setProperty("souther.example.step.limit", before);
            }
        }
    }
}
