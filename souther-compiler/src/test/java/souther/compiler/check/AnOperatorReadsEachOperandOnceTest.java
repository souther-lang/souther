package souther.compiler.check;

import souther.compiler.Compiler;

import org.junit.jupiter.api.Test;

import java.util.concurrent.atomic.AtomicReference;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Elaborating a binary expression reads each operand once, so what it costs is the size of the
 * expression and not two to the power of its nesting depth (issue #507).
 *
 * <p>An operand read twice costs twice its own subtree, and an operand of an operand costs twice
 * again: a chain of {@code N} operators nested one inside the last cost {@code 2^N}. Twenty-six
 * links took ten seconds and a hundred did not finish. Nothing said so — the operand check that
 * read them is the same check that reports, and it reports nothing until it comes back.
 *
 * <p>The reading is one place for every operator, so a chain of any one of them measures it. The
 * depth below is where the two costs are far enough apart that neither the machine nor the run
 * decides the answer: at 26 links a second reading takes tens of seconds, and one reading takes
 * milliseconds.
 */
class AnOperatorReadsEachOperandOnceTest {

    /** Deep enough that a second reading is tens of seconds, shallow enough that one is not
     *  measurable. */
    private static final int LINKS = 26;

    /** Far above what one reading costs at {@link #LINKS} and far below what two cost. */
    private static final long BUDGET_MS = 10_000;

    /** A chain of values, each written from the one before it — the shape the nesting ceiling
     *  (E2104) tells an author to break a deep expression into. A value is substituted where it is
     *  named (ADR-0072), so the last one's body is as deep as the chain is long. */
    @Test
    void aChainOfNamedValuesCostsWhatItsLengthSays() {
        StringBuilder source = new StringBuilder("module m\n\nlet v0 = 1\n");
        for (int i = 1; i <= 100; i++) {
            source.append("let v").append(i).append(" = v").append(i - 1).append(" + 1\n");
        }
        source.append("\nbehavior f : (x: Int) -> Int\nlet f (x) = x + v100\n");

        compilesWithinTheBudget(source.toString());
    }

    @Test
    void aChainOfArithmeticCostsWhatItsLengthSays() {
        compilesWithinTheBudget("""
                module m

                behavior f : (x: Int) -> Int
                let f (x) = x%s
                """.formatted(" + 1".repeat(LINKS)));
    }

    @Test
    void aChainOfAppendsCostsWhatItsLengthSays() {
        compilesWithinTheBudget("""
                module m

                behavior f : (s: String) -> String
                let f (s) = s%s
                """.formatted(" ++ \"a\"".repeat(LINKS)));
    }

    @Test
    void aChainOfLogicalOperatorsCostsWhatItsLengthSays() {
        compilesWithinTheBudget("""
                module m

                behavior f : (b: Bool) -> Bool
                let f (b) = b%s
                """.formatted(" && true".repeat(LINKS)));
    }

    /** `==` does not associate, so the nesting is written out. */
    @Test
    void aChainOfEqualitiesCostsWhatItsLengthSays() {
        compilesWithinTheBudget("""
                module m

                behavior f : (b: Bool) -> Bool
                let f (b) = %sb%s
                """.formatted("(".repeat(LINKS), " == true)".repeat(LINKS)));
    }

    /**
     * Compiles {@code source} on a thread of its own and fails where it took longer than
     * {@link #BUDGET_MS}. The wait is bounded well above the budget: a compile that never comes back
     * is the failure this is about, and it fails with a name on it rather than sitting there.
     */
    private static void compilesWithinTheBudget(String source) {
        AtomicReference<Throwable> thrown = new AtomicReference<>();
        Thread work = new Thread(() -> {
            try {
                Compiler.compile(source);
            } catch (Throwable x) {
                thrown.set(x);
            }
        }, "operand-cost");
        long started = System.nanoTime();
        work.start();
        try {
            work.join(6 * BUDGET_MS);
        } catch (InterruptedException interrupted) {
            Thread.currentThread().interrupt();
            throw new AssertionError("interrupted while waiting for the compile", interrupted);
        }
        long took = (System.nanoTime() - started) / 1_000_000;

        assertFalse(work.isAlive(), "the compile did not come back within " + (6 * BUDGET_MS) + "ms");
        assertNull(thrown.get(), "this source is correct and should compile");
        assertTrue(took < BUDGET_MS, "compiling took " + took + "ms, which is what reading an operand"
                + " more than once costs at this depth");
    }
}
