package souther.compiler.fmt;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.MethodSource;
import souther.compiler.cst.CstError;
import souther.compiler.diag.msg.DeclarationMessage;
import souther.compiler.diag.msg.Message;
import souther.compiler.cst.CstParser;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.function.IntFunction;
import java.util.concurrent.atomic.AtomicReference;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A source that nests deeper than a tree walk can descend must be answered, not thrown at, answered
 * the same way every time, and answered whatever the source nests.
 *
 * <p>The compiler already refused such a source, by catching the {@code StackOverflowError} its own
 * walks raised. The formatter did not, so the same source that {@code compile} turned into a
 * diagnostic took {@code souther fmt} down with a stack trace. Catching the error in one more place
 * would have closed that hole and left the deeper one open: what counts as "too deep" is then the
 * stack divided by whatever frame the JIT happened to compile, so the answer is not a property of
 * the source. Measured before the limit existed, {@code souther fmt --check} on one unchanged file
 * came back clean seven times out of fourteen and crashed the other seven.
 *
 * <p>The cases below are the shapes that reach the limit by different routes, and they are here
 * because the first attempt at this bounded two of them. A limit written into the productions that
 * read expressions is not a limit on the tree: the grammar closes its cycles in more places than one
 * reading finds — a unary minus recurses straight back into itself without passing through
 * {@code expr} at all, and types and patterns have cycles of their own. Every shape is put through
 * the same questions — including at each depth either side of the bound, where a source comes back
 * accepted and the bound is what a walker is relying on — so a route that grows a tree past it fails
 * here rather than in whichever walk descends it first.
 */
class DeepSyntaxTest {

    /** Small enough that the depths below are past it on any platform. A limit that only holds on a
     *  roomy stack is not a limit; these run where the old behaviour failed worst. */
    private static final int STACK_BYTES = 256 * 1024;

    private static final int RUNS = 8;

    /** One way of writing something inside something else, nested {@code n} levels deep. */
    record Shape(String name, IntFunction<String> at) {
        /** The shape written far past the bound, where the refusal is certain. */
        String source() {
            return at.apply(3000);
        }

        @Override
        public String toString() {
            return name;
        }
    }

    private static String moduleWith(String expr) {
        return """
                module m

                data N = Int

                behavior f : (n: N) -> N constructs N
                let f (n) = N { value = %s }
                """.formatted(expr);
    }

    static List<Shape> shapes() {
        return List.of(
                // Read by descending: the enclosing production calls the inner one.
                new Shape("parenthesis nest",
                        n -> moduleWith("(".repeat(n) + "1" + ")".repeat(n))),
                // Read by a loop that wraps what it has already read, so the frames never nest
                // while the tree does — invisible to any guard placed on the descent.
                new Shape("operator chain", n -> moduleWith("1 + ".repeat(n) + "1")),
                // A cycle that never passes through the expression entry point at all.
                new Shape("unary chain", n -> moduleWith("-".repeat(n) + "1")),
                // The type grammar's own cycle, through a type argument.
                new Shape("generic type nest",
                        n -> "module m\n\ndata X = " + "List<".repeat(n) + "Int" + ">".repeat(n) + "\n"),
                // And through a tuple type.
                new Shape("tuple type nest",
                        n -> "module m\n\ndata X = " + "(".repeat(n) + "Int, Int" + ")".repeat(n) + "\n"),
                // The pattern grammar's cycle, through a tuple pattern.
                new Shape("tuple pattern nest",
                        n -> "module m\n\nbehavior f : (n: Int) -> Int\nlet f "
                                + "(".repeat(n) + "x" + ")".repeat(n) + " = x\n"));
    }

    /** The bound a walker inherits. Every walk over this tree descends it by recursion, so this is
     *  what says a walk is affordable before it is made. */
    @ParameterizedTest
    @MethodSource("shapes")
    void theTreeComesBackWithinTheBound(Shape shape) throws InterruptedException {
        AtomicReference<Integer> depth = new AtomicReference<>();
        Throwable thrown = onSmallStack(() -> depth.set(CstParser.parse(shape.source()).green().depth()));

        assertNull(thrown, "parsing threw " + thrown);
        assertTrue(depth.get() <= CstParser.MAX_DEPTH,
                "the parse handed back a tree " + depth.get() + " deep, past the "
                        + CstParser.MAX_DEPTH + " a walker is told to expect");
    }

    @ParameterizedTest
    @MethodSource("shapes")
    void theDepthIsWhatIsReported(Shape shape) throws InterruptedException {
        AtomicReference<List<CstError>> errors = new AtomicReference<>();
        onSmallStack(() -> errors.set(CstParser.parse(shape.source()).errors()));

        assertNotNull(errors.get(), "the parse did not come back with an answer");
        // The bound is the tree's, so the diagnostic is too. `List<List<…<Int>…>>` reaches it
        // without an expression in sight, and `let` is not what splits it up; a message about
        // either is telling the author to do something that does not apply to what they wrote.
        assertTrue(errors.get().stream().map(CstError::said)
                        .anyMatch(m -> m instanceof DeclarationMessage.ItNestsDeeperThanIsRead),
                "expected the nesting diagnostic, got: " + errors.get().stream()
                        .map(CstError::said).toList());
    }

    /**
     * The bound holds at the boundary, not only far past it. The shapes above are refused, and a
     * refusal flattens what it had read — so they say nothing about a source that stops one level
     * short and comes back accepted. That is where the bound is actually load-bearing, and where
     * counting the frames rather than the tree they leave behind was wrong by one: 59 unary minuses
     * were accepted with a tree 65 deep, against a bound of 64.
     */
    @ParameterizedTest
    @MethodSource("shapes")
    void theBoundHoldsEitherSideOfIt(Shape shape) {
        for (int n = 0; n <= CstParser.MAX_DEPTH * 2; n++) {
            int depth = CstParser.parse(shape.at().apply(n)).green().depth();
            assertTrue(depth <= CstParser.MAX_DEPTH,
                    shape.name() + " at n=" + n + " gave a tree " + depth
                            + " deep, past the " + CstParser.MAX_DEPTH + " a walker is told to expect");
        }
    }

    /** A refused source is still described in full: the tree covers every character it read, which
     *  is what lets an editor keep showing the file it could not walk. */
    @ParameterizedTest
    @MethodSource("shapes")
    void theTreeStillCoversTheWholeSource(Shape shape) throws InterruptedException {
        AtomicReference<String> text = new AtomicReference<>();
        onSmallStack(() -> text.set(CstParser.parse(shape.source()).root().text()));

        assertEquals(shape.source(), text.get(), "the parse dropped part of the source it refused");
    }

    @ParameterizedTest
    @MethodSource("shapes")
    void formattingSuchASourceDoesNotOverflow(Shape shape) throws InterruptedException {
        Throwable thrown = onSmallStack(() -> Formatter.format(shape.source()));

        assertFalse(thrown instanceof StackOverflowError,
                "formatting a source the parser already refused reached the end of the stack");
    }

    /**
     * The property the catch alone could not give. Before the limit, the same source on the same
     * stack was accepted on some runs and refused on others, because the stack each frame costs is
     * decided by which tier the recursion happens to be compiled at when it runs.
     */
    @Test
    void theAnswerIsTheSameOnEveryRun() throws InterruptedException {
        String source = moduleWith("1 + ".repeat(20000) + "1");
        List<Message> answers = new ArrayList<>();
        for (int i = 0; i < RUNS; i++) {
            AtomicReference<Message> answer = new AtomicReference<>();
            onSmallStack(() -> answer.set(firstErrorOf(source)));
            answers.add(answer.get());
        }
        assertEquals(1, Set.copyOf(answers).size(),
                "the same source gave different answers across runs: " + answers);
        assertNotNull(answers.get(0), "the source was accepted, so the limit never applied");
    }

    /** One cause is one complaint: the levels above the one that tripped are the same fact seen
     *  from further out, and an editor that listed them all would bury the one worth reading. */
    @Test
    void theDepthIsReportedOnce() throws InterruptedException {
        AtomicReference<List<CstError>> errors = new AtomicReference<>();
        onSmallStack(() -> errors.set(
                CstParser.parse(moduleWith("(".repeat(5000) + "1" + ")".repeat(5000))).errors()));

        assertEquals(1, errors.get().size(), "expected one error, got " + errors.get());
    }

    /** A source that stays within the bound is untouched by any of this. */
    @Test
    void anOrdinarySourceIsUnaffected() throws InterruptedException {
        String source = moduleWith("((1 + 2) * (3 + n.value)) - 4");
        AtomicReference<List<CstError>> errors = new AtomicReference<>();
        onSmallStack(() -> errors.set(CstParser.parse(source).errors()));

        assertEquals(List.of(), errors.get(), "an ordinary expression was refused");
    }

    /** The parse's first complaint, or null where it had none. */
    private static Message firstErrorOf(String source) {
        List<CstError> errors = CstParser.parse(source).errors();
        return errors.isEmpty() ? null : errors.get(0).said();
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
