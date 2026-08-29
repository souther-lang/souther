package souther.compiler;

import souther.compiler.examples.Deadline;
import souther.compiler.observe.RowIdentity;
import souther.compiler.execute.EvaluationPolicy;
import souther.compiler.execute.jvm.JvmExampleDeadlines;
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
public final class DoesNotComeBack {

    /**
     * The wait a compile in one of these tests is given, and so the wait a report about work that
     * did not come back quotes.
     *
     * <p>Said to the compilation rather than held by the arrangement. What a report quotes has to be
     * what the compilation was told it would give a row, and an arrangement with a wait of its own
     * would be a second answer to that — a number in a rendered line that nothing asked for. Nothing
     * waits it out here: the work is said to overrun rather than timed.
     */
    public static final Duration WAIT = Duration.ofMillis(100);

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
     * An arrangement under which the work a test picks out does not come back, and everything else
     * runs to completion.
     *
     * <p>What a test about an overrun is asking is what the compiler <em>says</em> about work that
     * did not finish, and a clock is a poor way to ask it: the model has to be written so that
     * something genuinely loops, and then the answer depends on whether the host was loaded enough
     * to cut short the rows that were supposed to finish. Work overruns here because the test picked
     * it out, and the rest is run on the calling thread — no worker, no waiting, and no row that
     * finishes reported as one that did not.
     *
     * <p>The wait it quotes is the one this compilation was given, which is the whole of what it
     * takes from the compile. A wait of its own would be a second answer to how long a row got, and
     * a report quoting it would be quoting a number nothing said — which is what
     * {@code AnOverrunIsReportedAgainstTheWaitTheCompilationWasGivenTest} holds it to.
     *
     * <p>Picked out by what the work is, never by how many times something has been asked. One row
     * is worked on more than once over a compile — once to check it, again to measure what it
     * covered — so anything counting visits answers differently on the second pass.
     *
     * <p>Only the work picked out overruns, so whatever else the model does still has to finish: it
     * is run inline, and a loop nothing picked out would not be cut short but would hang.
     */
    public static JvmExampleDeadlines overrunningOn(Predicate<Deadline.Work> which) {
        return outerTimeout -> new Deadline() {

            @Override
            public long budgetMs() {
                return outerTimeout.toMillis();   // what a report about an overrun quotes
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

    /**
     * An arrangement under which the work a test picks out ends by throwing {@code thrown}, and
     * everything else runs to completion.
     *
     * <p>For a test about how the compiler classifies what comes back out of an evaluation. Some of
     * those are reachable by writing a model — a loop spends its budget — and some are not: a stack
     * that runs out in a generated decoder needs a fixture the parser will not accept before the
     * decoder ever sees it. What is being tested is the classification and not the route to it, so
     * the route is stated.
     */
    static JvmExampleDeadlines throwingOn(Predicate<Deadline.Work> which, Throwable thrown) {
        return outerTimeout -> new Deadline() {

            @Override
            public long budgetMs() {
                return outerTimeout.toMillis();
            }

            @Override
            public <T> Outcome<T> given(Work work, java.util.concurrent.Callable<T> body) {
                if (which.test(work)) {
                    return new Outcome.Threw<>(thrown);
                }
                try {
                    return new Outcome.Finished<>(body.call());
                } catch (Throwable cause) {
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
    public static Predicate<Deadline.Work> everythingAboutRowsOf(String target) {
        return everyRowOf(target).or(theFixturesOfEveryRowOf(target));
    }

    /**
     * The one row named {@code name}, and the statements it is read from.
     *
     * <p>For a model with more than one row of a behavior, where only one of them is the one that
     * does not come back. The name is written on the row, so it moves with it — a position would have
     * to be counted out of a text block and re-counted whenever the model above it changed — and one
     * behavior's rows do not share a name, so it picks out one row.
     */
    static Predicate<Deadline.Work> everythingAboutTheRowNamed(String name) {
        RowIdentity named = new RowIdentity.Named(name);
        return w -> switch (w) {
            case Deadline.Work.Row row -> named.equals(row.identity());
            case Deadline.Work.Fixtures f -> named.equals(f.identity());
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
