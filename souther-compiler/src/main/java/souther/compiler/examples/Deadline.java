package souther.compiler.examples;

import souther.compiler.diag.SourcePos;
import souther.compiler.observe.RowIdentity;

import java.util.concurrent.Callable;

/**
 * How long a piece of work gets, and what the caller is handed when it does not finish.
 *
 * <p>Two places give work a limit: a written statement being read ({@link ExampleStatements}) and a
 * row being evaluated ({@link ExampleVerifier}). Both do it the same way and both did it inline,
 * which left every test about what the compiler <em>says</em> about work that overran racing a clock
 * to say it. On a loaded host the race is lost in the direction that matters: work that does finish
 * is reported as work that did not.
 *
 * <p>So the limit is a seam. What is here is only what a reader of a row needs to ask — which piece
 * of work this is, and what became of it. A thread, a stack, a wall clock, work handed back to the
 * caller: those are how one machine keeps a limit, they are said in
 * {@code souther.compiler.execute.jvm}, and a reader that asked for them here would be holding one
 * arrangement's vocabulary to run a row under any of them.
 */
public interface Deadline {

    /**
     * One piece of work, said as what it is rather than as a sentence about it.
     *
     * <p>A deadline a test writes decides by reading this, so what it carries has to say which piece
     * of work it is. Where the writing is says that for any of them, and a row written with a name
     * says it as well: a name is unique among the rows one behavior has, over the module's own source
     * and every file attached to it, so a test may match on either. Editing a name is renaming the
     * row, and a deadline matched on the old one no longer meets it — which is what a rename is.
     */
    sealed interface Work {

        /** The behavior this work is about. */
        String target();

        /** Where the writing this is about starts, which says which source it is in. */
        SourcePos pos();

        /** A row of an {@code example}, evaluated whole: its fixtures built, the behavior applied,
         * the result compared. What {@link Fixtures} is the first third of, and named for the
         * difference. {@code identity} is what the row names itself. */
        record WholeRow(String target, SourcePos pos, RowIdentity identity) implements Work {}

        /** The statements a row is read from, with no behavior applied. */
        record Fixtures(String target, SourcePos pos, RowIdentity identity) implements Work {}

        /** A {@code fake} table, built. */
        record Table(String target, SourcePos pos) implements Work {}

        /** A {@code with} written on a row. */
        record With(String target, SourcePos pos) implements Work {}
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
}
