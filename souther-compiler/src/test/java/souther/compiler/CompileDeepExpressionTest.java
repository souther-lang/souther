package souther.compiler;

import org.junit.jupiter.api.Test;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.Located;
import souther.compiler.meta.ModulePath;
import souther.compiler.query.Compilation;
import souther.compiler.query.Adequacy;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.concurrent.atomic.AtomicReference;
import java.util.function.Supplier;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A compilation that runs out of stack must be reported, not thrown. Every phase here descends by
 * recursion, so a deep enough one exhausts the stack — and a {@code StackOverflowError} is not a
 * {@code CompileException}, so left alone it passes straight through the recovery boundary and the
 * command line prints a stack trace.
 *
 * <p>Asked at every entry point, because the answer is the compiler's rather than the signature's.
 * The recovery was written on the two that answer with classes, and the ones that answer with a
 * {@code Compilation} — which is what the command line and the editor ask for — did not have it, so
 * the same source came back a diagnostic through one door and an {@code Error} through another.
 *
 * <p>Each case runs on a thread with a small, fixed stack. What counts as "too deep" otherwise
 * depends on the stack the test happens to run with, which makes the same source compile on one run
 * and overflow on the next; pinning the stack makes the boundary the same everywhere.
 */
class CompileDeepExpressionTest {

    /** Small enough that the depths below are past it on any platform, large enough for the
     *  phases that are not recursing over the expression. */
    private static final int STACK_BYTES = 256 * 1024;

    private static String moduleWith(String expr) {
        return """
                module m

                data N = Int

                behavior f : (n: N) -> N constructs N
                let f (n) = N { value = %s }
                """.formatted(expr);
    }

    /**
     * A source that once ran the walks out of stack: a chain of values, each naming the one before,
     * which substitution splices into one tree as long as the chain.
     *
     * <p>It no longer reaches the stack. What a definition may say is bounded now, and this chain
     * says more than the bound, so the expansion is refused before it runs. It is kept as what it
     * shows: every door answers it the same way. Which answer that is has moved once already and
     * may move again — what is asked of it here is that it is an answer.
     */
    private static String aCompilationThatOnceRanOutOfStack() {
        StringBuilder sb = new StringBuilder("module m exposing (f)\n\nlet v0 = 1\n");
        for (int i = 1; i <= 1000; i++) {
            sb.append("let v").append(i).append(" = v").append(i - 1).append(" + 1\n");
        }
        return sb.append("\nbehavior f : (x: Int) -> Int\nlet f (x) = x + v1000\n").toString();
    }

    /** Every entry point that drives a compilation, by the name a reader would call it. What a
     *  door hands back is kept: the analysing ones answer with a compilation carrying the reports
     *  rather than by raising, which is what they promise, so what counts as an answer differs by
     *  door even though whether there is one does not. */
    private static Map<String, Supplier<Object>> everyEntryPoint(String source) {
        List<String> sources = List.of(source);
        Map<String, Supplier<Object>> doors = new LinkedHashMap<>();
        doors.put("compile(source)", () -> Compiler.compile(source));
        doors.put("compile(source, name)", () -> Compiler.compile(source, "m"));
        doors.put("compileWithWarnings(source)", () -> Compiler.compileWithWarnings(source));
        doors.put("compileWithWarnings(source, name)",
                () -> Compiler.compileWithWarnings(source, "m"));
        doors.put("compiled(source, name)", () -> Compiler.compiled(source, "m"));
        doors.put("analyzed(source, name, ...)",
                () -> Compiler.analyzed(source, "m", new ArrayList<Located>(), Adequacy.Asked.NOTHING));
        doors.put("compileModules(sources)", () -> Compiler.compileModules(sources));
        doors.put("compileModules(sources, path)",
                () -> Compiler.compileModules(sources, ModulePath.EMPTY));
        doors.put("compileModulesWithWarnings(sources)",
                () -> Compiler.compileModulesWithWarnings(sources));
        doors.put("compileModulesWithWarnings(sources, path)",
                () -> Compiler.compileModulesWithWarnings(sources, ModulePath.EMPTY));
        doors.put("compiledModules(sources, path, ...)",
                () -> Compiler.compiledModules(sources, ModulePath.EMPTY, new ArrayList<Located>()));
        doors.put("analyzedModules(sources, path, ...)",
                () -> Compiler.analyzedModules(sources, ModulePath.EMPTY, new ArrayList<Located>(),
                        Adequacy.Asked.NOTHING));
        return doors;
    }

    /**
     * The boundary itself, asked with the one thing it is for.
     *
     * <p>Nothing reaches it by compiling any more. What a definition may say is bounded at the
     * producers of the depth now, so a source deep enough to exhaust a walk is refused before it
     * runs — which is what issue #524 asked for, and what makes this the only case that holds the
     * recovery. Without it, removing the recovery outright would leave every other case green.
     */
    @Test
    void theBoundaryTurnsAnExhaustedStackIntoADiagnostic() {
        CompileException thrown = assertThrows(CompileException.class,
                () -> Compiler.driven(() -> {
                    throw new StackOverflowError();
                }));

        assertTrue(thrown.getMessage().contains("deep"),
                "expected a depth diagnostic, got: " + thrown.getMessage());
    }

    /**
     * Every door, and every door's answer said together. Stopping at the first one that is wrong
     * says one name where the question is which of them agree, and the door that had the recovery
     * already is among the first — so a run that stopped there would report the one door that was
     * never in doubt.
     *
     * <p>What is asked is that each door answers, not what it answers with. Where the answer comes
     * from has moved — it was the recovery, and it is the bound on what a definition may say — and
     * a door that agreed before agrees still.
     */
    @Test
    void everyEntryPointAnswersTheSameWay() throws InterruptedException {
        String source = aCompilationThatOnceRanOutOfStack();
        List<String> wrong = new ArrayList<>();

        for (Map.Entry<String, Supplier<Object>> door : everyEntryPoint(source).entrySet()) {
            AtomicReference<Object> answered = new AtomicReference<>();
            Throwable thrown = run(() -> answered.set(door.getValue().get()), STACK_BYTES);
            String said = whatIsWrong(thrown, answered.get());
            if (said != null) {
                wrong.add(door.getKey() + " -> " + said);
            }
        }

        assertTrue(wrong.isEmpty(), "these entry points did not answer with a diagnostic:\n  "
                + String.join("\n  ", wrong));
    }

    @Test
    void deeplyNestedParenthesesAreReported() throws InterruptedException {
        String expr = "(".repeat(5000) + "1" + ")".repeat(5000);

        assertReportsDepth("compile(source)", () -> Compiler.compile(moduleWith(expr)));
    }

    @Test
    void aVeryLongOperatorChainIsReported() throws InterruptedException {
        String expr = "1 + ".repeat(20000) + "1";

        assertReportsDepth("compile(source)", () -> Compiler.compile(moduleWith(expr)));
    }

    /** A module set goes through the same walks, so it needs the same answer. */
    @Test
    void theSameHoldsForAModuleSet() throws InterruptedException {
        String expr = "(".repeat(5000) + "1" + ")".repeat(5000);

        assertReportsDepth("compileModules(sources)",
                () -> Compiler.compileModules(List.of(moduleWith(expr))));
    }

    /**
     * A nest is walked, not rescanned. The lambda lookahead reads the parenthesised run at every
     * level of one, and deriving each token position from the cursor again made that cost the cube of
     * the depth — this source took over two minutes, and where the stack ran out first it still took
     * nine seconds to say so, which from the outside is a compiler that has hung. The stack here is
     * large enough that the walk, not the depth limit, is what the time measures.
     */
    @Test
    void aNestIsWalkedRatherThanRescannedAtEveryLevel() throws InterruptedException {
        String expr = "(".repeat(5000) + "1" + ")".repeat(5000);

        long started = System.nanoTime();
        run(() -> Compiler.compile(moduleWith(expr)), 32 * 1024 * 1024);
        long took = (System.nanoTime() - started) / 1_000_000;

        assertTrue(took < 30_000, "compiling a 5000-deep nest took " + took + "ms");
    }

    /** What is wrong with a door's answer, or null where it answered: a raising door throws a
     *  diagnostic, an analysing one hands back a compilation with the diagnostic in its reports. */
    private static String whatIsWrong(Throwable thrown, Object handedBack) {
        if (thrown instanceof CompileException) {
            return null;
        }
        if (thrown != null) {
            return thrown.getClass().getName();
        }
        if (handedBack instanceof Compilation compilation
                && !compilation.errors(compilation.db().allReports()).isEmpty()) {
            return null;
        }
        return "compiled";
    }

    /** Runs {@code work} on a thread with {@link #STACK_BYTES} of stack and asserts it came back
     *  with a depth diagnostic rather than an {@code Error}. */
    private static void assertReportsDepth(String door, Runnable work) throws InterruptedException {
        Throwable thrown = run(work, STACK_BYTES);
        assertNotNull(thrown, door + ": a source this deep should not compile on a " + STACK_BYTES
                + "-byte stack; the test no longer exercises the depth boundary");
        assertInstanceOf(CompileException.class, thrown,
                door + ": expected a diagnostic, got " + thrown.getClass().getName());
        assertTrue(thrown.getMessage().contains("deep"),
                door + ": expected a depth diagnostic, got: " + thrown.getMessage());
    }

    /**
     * Runs {@code work} on a thread with {@code stackBytes} of stack and returns what it threw, or
     * null where it returned. The wait is bounded: work that never comes back is a failure with a
     * name on it, not a run that sits there.
     */
    private static Throwable run(Runnable work, int stackBytes) throws InterruptedException {
        AtomicReference<Throwable> caught = new AtomicReference<>();
        Thread t = new Thread(null, () -> {
            try {
                work.run();
            } catch (Throwable x) {
                caught.set(x);
            }
        }, "deep-expression", stackBytes);
        t.start();
        t.join(120_000);
        assertFalse(t.isAlive(), "the compile did not come back within 120s");
        return caught.get();
    }
}
