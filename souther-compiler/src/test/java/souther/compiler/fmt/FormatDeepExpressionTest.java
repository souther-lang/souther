package souther.compiler.fmt;

import org.junit.jupiter.api.Test;
import souther.compiler.cst.CstError;
import souther.compiler.cst.CstParser;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.concurrent.atomic.AtomicReference;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A source that nests deeper than the tree walks can descend must be answered, not thrown at, and
 * answered the same way every time.
 *
 * <p>The compiler already refused such a source, by catching the {@code StackOverflowError} its own
 * walks raised. The formatter did not, so the same source that {@code compile} turned into a
 * diagnostic took {@code souther fmt} down with a stack trace. Catching the error in one more place
 * would have closed that hole and left the deeper one open: what counts as "too deep" is then the
 * stack divided by whatever frame the JIT happened to compile, so the answer is not a property of
 * the source. Measured before the limit existed, {@code souther fmt --check} on one unchanged file
 * came back clean seven times out of fourteen and crashed the other seven.
 *
 * <p>So the limit is written down, and the parse is what applies it. The cases here are the two
 * shapes that reach it from opposite sides: a nest the parser descends, and a chain the parser
 * builds by wrapping what it already read.
 */
class FormatDeepExpressionTest {

    /** Small enough that the depths below are past it on any platform. A limit that only holds on a
     *  roomy stack is not a limit; these run where the old behaviour failed worst. */
    private static final int STACK_BYTES = 256 * 1024;

    private static final int RUNS = 8;

    private static String moduleWith(String expr) {
        return """
                module m

                data N = Int

                behavior f : (n: N) -> N constructs N
                let f (n) = N { value = %s }
                """.formatted(expr);
    }

    private static String deepNest() {
        return moduleWith("(".repeat(5000) + "1" + ")".repeat(5000));
    }

    private static String deepChain() {
        return moduleWith("1 + ".repeat(20000) + "1");
    }

    @Test
    void aNestTheParserDescendsIsReported() throws InterruptedException {
        assertReportsDepth(deepNest());
    }

    @Test
    void aChainTheParserWrapsIsReported() throws InterruptedException {
        assertReportsDepth(deepChain());
    }

    @Test
    void formattingSuchASourceDoesNotOverflow() throws InterruptedException {
        for (String source : List.of(deepNest(), deepChain())) {
            Throwable thrown = onSmallStack(() -> Formatter.format(source));
            assertFalse(thrown instanceof StackOverflowError,
                    "formatting a source the parser already refused reached the end of the stack");
        }
    }

    /**
     * The property the catch alone could not give. Before the limit, the same source on the same
     * stack was accepted on some runs and refused on others, because the stack each frame costs is
     * decided by which tier the recursion happens to be compiled at when it runs.
     */
    @Test
    void theAnswerIsTheSameOnEveryRun() throws InterruptedException {
        String source = deepChain();
        List<String> answers = new ArrayList<>();
        for (int i = 0; i < RUNS; i++) {
            AtomicReference<String> answer = new AtomicReference<>();
            onSmallStack(() -> answer.set(firstErrorOf(source)));
            answers.add(answer.get());
        }
        assertEquals(1, Set.copyOf(answers).size(),
                "the same source gave different answers across runs: " + answers);
        assertNotNull(answers.get(0), "the source was accepted, so the limit never applied");
    }

    /** A refused source is still described in full: the tree the parser hands back covers every
     *  character it read, which is what lets an editor keep showing the file it could not walk. */
    @Test
    void theTreeStillCoversTheWholeSource() throws InterruptedException {
        for (String source : List.of(deepNest(), deepChain())) {
            AtomicReference<String> text = new AtomicReference<>();
            onSmallStack(() -> text.set(CstParser.parse(source).root().text()));
            assertEquals(source, text.get(), "the parse dropped part of the source it refused");
        }
    }

    /** One cause is one complaint: the levels above the one that tripped are the same fact seen
     *  from further out, and an editor that listed them all would bury the one worth reading. */
    @Test
    void theDepthIsReportedOnce() throws InterruptedException {
        AtomicReference<List<CstError>> errors = new AtomicReference<>();
        onSmallStack(() -> errors.set(CstParser.parse(deepNest()).errors()));
        assertEquals(1, errors.get().size(), "expected one error, got " + errors.get());
    }

    private static void assertReportsDepth(String source) throws InterruptedException {
        AtomicReference<String> message = new AtomicReference<>();
        onSmallStack(() -> message.set(firstErrorOf(source)));
        assertNotNull(message.get(),
                "a source this deep should not parse cleanly; the test no longer reaches the limit");
        assertTrue(message.get().contains("deep"),
                "expected a depth diagnostic, got: " + message.get());
    }

    /** The parse's first complaint, or null where it had none. */
    private static String firstErrorOf(String source) {
        List<CstError> errors = CstParser.parse(source).errors();
        return errors.isEmpty() ? null : errors.get(0).legacyMessage();
    }

    /** Runs {@code work} on a thread with {@link #STACK_BYTES} of stack and returns what it threw,
     *  or null where it returned. */
    private static Throwable onSmallStack(Runnable work) throws InterruptedException {
        AtomicReference<Throwable> caught = new AtomicReference<>();
        Thread t = new Thread(null, () -> {
            try {
                work.run();
            } catch (Throwable x) {
                caught.set(x);
            }
        }, "deep-expression", STACK_BYTES);
        t.start();
        t.join(120_000);
        assertFalse(t.isAlive(), "the parse did not come back within 120s");
        return caught.get();
    }
}
