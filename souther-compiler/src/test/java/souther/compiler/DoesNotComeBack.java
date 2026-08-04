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

    /** As {@link #compile(String)}, with the work this model does not get back from said rather
     *  than timed. {@code what} is named as {@link #overrunningOn} names it. */
    static void compileOverrunning(String model, String... what) {
        Compiler.compiled(model, "Main", new java.util.ArrayList<>(),
                souther.compiler.query.Adequacy.Asked.NOTHING, null, overrunningOn(what));
    }

    /** As {@link #compileModules(java.util.List, java.util.List)}, said rather than timed. */
    static void compileModulesOverrunning(java.util.List<String> sources,
                                          java.util.List<souther.compiler.diag.Located> warningsOut,
                                          String... what) {
        Compiler.compiledModules(sources, souther.compiler.meta.ModulePath.EMPTY, warningsOut,
                souther.compiler.query.Adequacy.Asked.NOTHING, null, overrunningOn(what));
    }

    /**
     * A deadline under which the work a test names does not come back, and everything else runs to
     * completion.
     *
     * <p>What a test about an overrun is asking is what the compiler <em>says</em> about work that
     * did not finish, and a clock is a poor way to ask it: the model has to be written so that
     * something genuinely loops, and then the answer depends on whether the host was loaded enough
     * to cut short the rows that were supposed to finish. Named work overruns here because the test
     * said so, and the rest is run on the calling thread — no worker, no waiting, and no row that
     * finishes reported as one that did not.
     *
     * <p>The names are the ones the two sites give their work, and each names the thing rather than
     * the visit: {@code row 2 of `take`} for a row evaluated, {@code the fixtures of row 2 of
     * `take`} for the statements it is read from, {@code the `fake find` table}, {@code a `with
     * dep`}. Naming the thing is what makes this deterministic — one row is evaluated more than once
     * over a compile, once to check it and again to measure what it covered, and anything counting
     * visits would answer differently on the second pass.
     *
     * <p>Only the work named overruns, so whatever else the model does still has to finish: it is
     * run inline, and a loop nobody named would not be cut short but would hang.
     */
    static Deadline overrunningOn(String... what) {
        java.util.Set<String> named = java.util.Set.of(what);
        return new Deadline() {

            @Override
            public long budgetMs() {
                return BUDGET.toMillis();   // what a report about an overrun quotes
            }

            @Override
            public <T> Outcome<T> given(String subject, java.util.concurrent.Callable<T> work) {
                if (named.contains(subject)) {
                    return new Outcome.Overran<>(() -> { });   // nothing was started to give up on
                }
                try {
                    return new Outcome.Finished<>(work.call());
                } catch (Exception e) {
                    return new Outcome.Threw<>(e);
                }
            }
        };
    }

    private DoesNotComeBack() {
    }
}
