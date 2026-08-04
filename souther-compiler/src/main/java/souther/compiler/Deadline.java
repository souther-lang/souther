package souther.compiler;

import souther.compiler.diag.SourcePos;

import java.util.concurrent.Callable;

/**
 * How long a piece of work gets, and what the caller is handed when it does not finish.
 *
 * <p>Two places give work a limit: a written statement being read ({@link ExampleStatements}) and a
 * row being evaluated ({@link ExampleVerifier}). Both do it the same way — a worker of its own and a
 * wall clock — and both did it inline, which left every test about what the compiler <em>says</em>
 * about work that overran racing a clock to say it. On a loaded host the race is lost in the
 * direction that matters: work that does finish is reported as work that did not.
 *
 * <p>So the limit is a seam. What a build uses is {@link #ofMillis}, which is what both sites did
 * before. What a test uses is a deadline that decides by which work it is, so "this row does not
 * come back" is stated rather than raced for.
 */
public interface Deadline {

    /**
     * One piece of work, said as what it is rather than as a sentence about it.
     *
     * <p>A deadline a test writes decides by reading this, so it is an identity and not a label:
     * a description that read well would still have to be unique, and would break every test that
     * matched on it the day the wording improved. What makes it unique is where the writing is —
     * two rows of one behavior differ in nothing else, and a behavior can be exampled by more than
     * one {@code example} block and by more than one file.
     */
    sealed interface Work {

        /** The behavior this work is about. */
        String target();

        /** The source the writing this is about was written in. */
        String sourceId();

        /** Where in that source it starts. */
        SourcePos pos();

        /** A row of an {@code example}, evaluated: its fixtures built, the behavior applied, the
         * result compared. {@code description} is what the row was written with, or null. */
        record Row(String target, String sourceId, SourcePos pos, String description)
                implements Work {}

        /** The statements a row is read from, with no behavior applied. */
        record Fixtures(String target, String sourceId, SourcePos pos, String description)
                implements Work {}

        /** A {@code fake} table, built. */
        record Table(String target, String sourceId, SourcePos pos) implements Work {}

        /** A {@code with} written on a row. */
        record With(String target, String sourceId, SourcePos pos) implements Work {}
    }

    /** How many milliseconds this allows. What a report about an overrun quotes. */
    long budgetMs();

    /** {@code work}, run within what this allows. */
    <T> Outcome<T> given(Work work, Callable<T> work0);

    /** What became of work that was given a deadline. */
    sealed interface Outcome<T> {

        /** It finished, and this is what it answered. */
        record Finished<T>(T value) implements Outcome<T> {}

        /**
         * It did not finish.
         *
         * <p>{@code abandon} gives up on it, and is separate from this arriving because the two are
         * ordered: work that overran may have published how far it got, and giving up interrupts it,
         * so a caller that wants to know reads first and abandons after. A caller with nothing to
         * read still has to call it — nothing else will.
         */
        record Overran<T>(Runnable abandon) implements Outcome<T> {}

        /** It ended by throwing, and this is what came out. */
        record Threw<T>(Throwable cause) implements Outcome<T> {}
    }

    /** The deadline a build runs on: a worker of its own, and {@code budgetMs} on the clock. */
    static Deadline ofMillis(long budgetMs) {
        return new Deadline() {

            @Override
            public long budgetMs() {
                return budgetMs;
            }

            @Override
            public <T> Outcome<T> given(Work work, Callable<T> body) {
                java.util.concurrent.FutureTask<T> task = new java.util.concurrent.FutureTask<>(body);
                // A daemon, because work that overran is asked to stop and cannot be made to: a
                // fixture's helper reaches no interrupt point, so the thread may outlive the answer
                // about it and must not outlive the JVM.
                Thread worker = new Thread(task, "souther-reading");
                worker.setDaemon(true);
                worker.start();
                try {
                    return new Outcome.Finished<>(
                            task.get(budgetMs, java.util.concurrent.TimeUnit.MILLISECONDS));
                } catch (java.util.concurrent.TimeoutException _) {
                    return new Outcome.Overran<>(() -> task.cancel(true));
                } catch (java.util.concurrent.ExecutionException ee) {
                    task.cancel(true);
                    return new Outcome.Threw<>(ee.getCause());
                } catch (InterruptedException _) {
                    task.cancel(true);
                    Thread.currentThread().interrupt();
                    return new Outcome.Threw<>(
                            new java.util.concurrent.CancellationException(
                                    "interrupted while reading " + work.target()));
                }
            }
        };
    }
}
