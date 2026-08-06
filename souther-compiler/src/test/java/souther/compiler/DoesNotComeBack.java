package souther.compiler;

import java.time.Duration;
import java.util.function.Predicate;

/**
 * The budget a compile is given when the point of the model is a row that never finishes.
 *
 * <p>Counted rather than timed. A test about what is reported when a row does not come back used to
 * wait for the compiler to stop waiting, which made the answer depend on how loaded the host was: a
 * row that finishes is reported as one that did not, if the machine is busy enough. Held to a number
 * of steps, the looping row is reported for spending them and the rows beside it are not, on every
 * host and every time.
 *
 * <p>Said on the compilation rather than for the JVM, because the two kinds of model are mixed
 * together in one suite. A model that mixes a row which comes back with one that does not may be
 * compiled with this, and several are: what matters is that the ones which finish cost a handful of
 * steps — writing {@code Ok { n = 1 }} against a two-field record — against the fifty thousand this
 * allows.
 *
 * <p>What must keep the default is a model whose rows do real work. {@code budgetSpent} in
 * {@code CompilePartialAdequacyTest} walks four thousand nodes to spend the observation budget, and
 * it holds no looping helper at all.
 */
final class DoesNotComeBack {

    /**
     * The wait a test quotes when it says work did not come back.
     *
     * <p>Only {@link #overrunningOn} uses it, and there it is never waited out: the work is said to
     * overrun rather than timed. What it is for is the number the report about it quotes.
     */
    static final Duration BUDGET = Duration.ofMillis(100);

    /**
     * Steps enough for a row that finishes, and far fewer than a row that does not will spend.
     *
     * <p>This is what a model written so that something loops is held to. A loop reaches this in
     * microseconds and is reported for it, and the answer is the same on every host — so a suite full
     * of these neither waits nor races. The rows beside the looping one in these models write a
     * literal or a two-field record, which costs a handful of steps against this.
     */
    static final EvaluationPolicy POLICY = EvaluationPolicy.of(50_000L);

    /** As {@link Compiler#compile(String)}, on this budget: the same first error, raised the same
     *  way, without waiting out a default set for models that come back. */
    static void compile(String model) {
        Compiler.compiled(model, "Main", new java.util.ArrayList<>(),
                souther.compiler.query.Adequacy.Asked.NOTHING, POLICY);
    }

    /** As {@link Compiler#compiledModules(java.util.List, souther.compiler.meta.ModulePath,
     *  java.util.List)}, on this budget. */
    static void compileModules(java.util.List<String> sources,
                               java.util.List<souther.compiler.diag.Located> warningsOut) {
        Compiler.compiledModules(sources, souther.compiler.meta.ModulePath.EMPTY, warningsOut,
                souther.compiler.query.Adequacy.Asked.NOTHING, POLICY);
    }

    /** As {@link #compile(String)}, with the work this model does not get back from said rather
     *  than timed. {@code what} is named as {@link #overrunningOn} names it. */
    static void compileOverrunning(String model, Predicate<Deadline.Work> which) {
        Compiler.compiled(model, "Main", new java.util.ArrayList<>(),
                souther.compiler.query.Adequacy.Asked.NOTHING, null, overrunningOn(which));
    }

    /** As {@link #compileModules(java.util.List, java.util.List)}, said rather than timed. */
    static void compileModulesOverrunning(java.util.List<String> sources,
                                          java.util.List<souther.compiler.diag.Located> warningsOut,
                                          Predicate<Deadline.Work> which) {
        Compiler.compiledModules(sources, souther.compiler.meta.ModulePath.EMPTY, warningsOut,
                souther.compiler.query.Adequacy.Asked.NOTHING, null, overrunningOn(which));
    }

    /**
     * A deadline under which the work a test picks out does not come back, and everything else runs
     * to completion.
     *
     * <p>What a test about an overrun is asking is what the compiler <em>says</em> about work that
     * did not finish, and a clock is a poor way to ask it: the model has to be written so that
     * something genuinely loops, and then the answer depends on whether the host was loaded enough
     * to cut short the rows that were supposed to finish. Work overruns here because the test picked
     * it out, and the rest is run on the calling thread — no worker, no waiting, and no row that
     * finishes reported as one that did not.
     *
     * <p>Picked out by what the work is, never by how many times something has been asked. One row
     * is worked on more than once over a compile — once to check it, again to measure what it
     * covered — so anything counting visits answers differently on the second pass.
     *
     * <p>Only the work picked out overruns, so whatever else the model does still has to finish: it
     * is run inline, and a loop nothing picked out would not be cut short but would hang.
     */
    static Deadline overrunningOn(Predicate<Deadline.Work> which) {
        return new Deadline() {

            @Override
            public long budgetMs() {
                return BUDGET.toMillis();   // what a report about an overrun quotes
            }

            @Override
            public <T> Outcome<T> given(Work work, java.util.concurrent.Callable<T> body) {
                if (which.test(work)) {
                    return new Outcome.Overran<>(() -> { });   // nothing was started to give up on
                }
                try {
                    return new Outcome.Finished<>(body.call());
                } catch (Throwable cause) {
                    // Everything the worker could have thrown, as the build's deadline hands it over:
                    // `ExampleStatements` reads a `NoClassDefFoundError` as this host having no
                    // runtime, and would never see one that came past this instead of through it.
                    return new Outcome.Threw<>(cause);
                }
            }
        };
    }

    /** Every row of {@code target}, evaluated — its fixtures built, the behavior applied. */
    static Predicate<Deadline.Work> everyRowOf(String target) {
        return w -> w instanceof Deadline.Work.Row row && row.target().equals(target);
    }

    /** The statements every row of {@code target} is read from, with nothing applied. */
    static Predicate<Deadline.Work> theFixturesOfEveryRowOf(String target) {
        return w -> w instanceof Deadline.Work.Fixtures f && f.target().equals(target);
    }

    /** Everything a row of {@code target} is worked on for: read, and evaluated. */
    static Predicate<Deadline.Work> everythingAboutRowsOf(String target) {
        return everyRowOf(target).or(theFixturesOfEveryRowOf(target));
    }

    /**
     * The one row written with {@code description}, and the statements it is read from.
     *
     * <p>For a model with more than one row of a behavior, where only one of them is the one that
     * does not come back. The description is written on the row, so it moves with it — a position
     * would have to be counted out of a text block and re-counted whenever the model above it
     * changed.
     */
    static Predicate<Deadline.Work> everythingAboutTheRowDescribed(String description) {
        return w -> switch (w) {
            case Deadline.Work.Row row -> description.equals(row.description());
            case Deadline.Work.Fixtures f -> description.equals(f.description());
            default -> false;
        };
    }

    /** Every {@code fake} table of {@code target}, built. */
    static Predicate<Deadline.Work> everyTableOf(String target) {
        return w -> w instanceof Deadline.Work.Table t && t.target().equals(target);
    }

    private DoesNotComeBack() {
    }
}
