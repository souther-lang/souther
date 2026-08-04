package souther.compiler;

import java.time.Duration;

/**
 * The budget a compile is given when the point of the model is a row that never finishes.
 *
 * <p>A test about what is reported when a row does not come back has to wait for the compiler to
 * stop waiting, and the default budget is set for the opposite case — long enough that no
 * terminating row is ever cut short on the slowest host a build runs on. Paying that here buys
 * nothing: the row is a `partial` recursion with no base case, so the answer at 2000ms and the answer
 * here are the same answer, reached sooner.
 *
 * <p>Said on the compilation rather than for the JVM, because the two kinds of model are mixed
 * together in one suite. {@code CompilePartialAdequacyTest} compiles a model whose rows loop and,
 * beside it, one that walks four thousand nodes and finishes — and a budget short enough for the
 * first would report the second as a row that does not terminate, which is a failure that depends on
 * how loaded the machine was rather than on anything the model says.
 *
 * <p>A model that mixes a row which comes back with one that does not may still be compiled with
 * this, and several are: what matters is not that every row loops but that the ones which finish do
 * so in microseconds — writing {@code Ok { n = 1 }} against a two-field record. The margin is then
 * four orders of magnitude, and no amount of load closes it.
 *
 * <p>What must keep the default is a model whose rows do real work. {@code budgetSpent} in
 * {@code CompilePartialAdequacyTest} walks four thousand nodes to spend the observation budget, and
 * it holds no looping helper at all; a budget chosen for the loops would report it as a behavior that
 * does not terminate, which is the one failure this whole arrangement exists to make impossible.
 */
final class DoesNotComeBack {

    /**
     * Long enough that starting a worker, loading the generated classes and reflecting into them is
     * never what runs out of it, and short enough that a suite full of these is not mostly waiting.
     *
     * <p>The rows this is used for do not terminate, so no value of it can make the test say the
     * wrong thing — a bigger one only makes it slower. What it is for is the work <em>around</em> the
     * loop, which is measured in single-digit milliseconds even on a cold JVM under a fully loaded
     * host.
     */
    static final Duration BUDGET = Duration.ofMillis(100);

    /** As {@link Compiler#compile(String)}, on this budget: the same first error, raised the same
     *  way, without waiting out a default set for models that come back. */
    static void compile(String model) {
        Compiler.compiled(model, "Main", new java.util.ArrayList<>(),
                souther.compiler.query.Adequacy.Asked.NOTHING, BUDGET);
    }

    /** As {@link Compiler#compiledModules(java.util.List, souther.compiler.meta.ModulePath,
     *  java.util.List)}, on this budget. */
    static void compileModules(java.util.List<String> sources,
                               java.util.List<souther.compiler.diag.Located> warningsOut) {
        Compiler.compiledModules(sources, souther.compiler.meta.ModulePath.EMPTY, warningsOut,
                souther.compiler.query.Adequacy.Asked.NOTHING, BUDGET);
    }

    private DoesNotComeBack() {
    }
}
