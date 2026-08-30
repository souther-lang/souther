package souther.compiler.observe;

import souther.compiler.types.ValueName;

import java.util.List;

/**
 * What one {@code example} row states, as something that did not read the source can hold it.
 *
 * <p>A row states what a behavior owes for an input, and running it is not what settles that: the
 * inputs and the expectation are written down, bound and checked whether or not anything applies
 * the behavior. So what a row states is a fact about the model, and this is that fact taken once —
 * where the row was read — rather than a source text something else would have to read again.
 *
 * <p>Three arms, and the second is three. A row hands over values or it does not, which is the one
 * thing a reader has to know before it can do anything with the row; why it does not is the second
 * question, and each answer to it has a different owner — what the behavior requires, what a limit
 * keeps, and what read the row. A row that cannot be handed over must not arrive as no row all the
 * same: a reader given nothing for it would count a row it never saw among the ones it walked and
 * found nothing wrong with.
 *
 * <p>The third is not one of those. {@link StoppedBeforeItsValues} is how far an evaluation got and
 * not something about the row, and it is beside {@link NotStated} rather than among its arms
 * because what an output is handed is a {@link Stated} or a {@link NotStated} — so a state that
 * belongs to a compile in progress is one a reader of a checked program cannot be given, by the
 * static type and not by a rule about which of them arise.
 *
 * <p>What it is not: running the row. Nothing here applies anything, and what a reader does with a
 * row it was given is the reader's.
 */
public sealed interface RowStatement {

    /**
     * The inputs the row hands over and what it states of the answer.
     *
     * <p>Every value here is whole and is one these limits keep. Made by {@link #of}, which is what
     * decides that: a value read whole is not always one a snapshot may carry, and the two
     * questions answered in two places would be a {@code Stated} that means one thing where it was
     * built and another where it was read.
     *
     * <p>A class and not a record, so that the one rule about what these hold cannot be gone round.
     * A record's canonical constructor is as public as the record, and a value larger than what is
     * kept would be written straight past the reading that decides what a row states; made only by
     * {@link #of}, it is that reading whichever side makes one.
     *
     * <p>A value all the same, and it says so itself. What a query stops work on is whether an
     * answer equals the one before it, and this rides inside one — so a statement that answered
     * only for itself would make every compile that read a row look like a compile that changed it.
     * The parts it is are the parts it is equal by.
     */
    final class Stated implements RowStatement {

        private final List<ObservedValue> inputs;
        private final Expectation expects;

        private Stated(List<ObservedValue> inputs, Expectation expects) {
            this.inputs = List.copyOf(inputs);
            this.expects = expects;
        }

        /** What the row hands the behavior, in the order it takes them. */
        public List<ObservedValue> inputs() {
            return inputs;
        }

        /** What the row states of the answer. */
        public Expectation expects() {
            return expects;
        }

        @Override
        public boolean equals(Object other) {
            return other instanceof Stated it && inputs.equals(it.inputs)
                    && expects.equals(it.expects);
        }

        @Override
        public int hashCode() {
            return inputs.hashCode() * 31 + expects.hashCode();
        }

        @Override
        public String toString() {
            return inputs + " -> " + expects;
        }
    }

    /**
     * A row that hands over no values, and why.
     *
     * <p>Three ways, and a reader that has to tell them apart says so as a {@code switch} over this
     * rather than as a test for one of them.
     */
    sealed interface NotStated extends RowStatement {}

    /**
     * The behavior takes something injected, so the row states more than values.
     *
     * <p>A row runs against a bound implementation, and where the behavior depends on something
     * injected, what stands in for that dependency is the rest of what makes the row runnable.
     * Handing over the inputs and the expectation alone would not be handing over the row: a reader
     * whose dependency is an import has nothing to answer that import with, and one that applied the
     * behavior anyway would be reporting what a run that cannot happen answered.
     *
     * <p>So the row crosses as itself and says what is missing. Which dependencies those are is what
     * the behavior requires, in the order it takes them.
     */
    record RequiresStandIns(List<ValueName.Behavior> dependencies) implements NotStated {

        public RequiresStandIns {
            dependencies = List.copyOf(dependencies);
            if (dependencies.isEmpty()) {
                throw new IllegalArgumentException("a row that needs nothing stood in for states"
                        + " its values");
            }
        }
    }

    /**
     * A value the row states is not one that could be carried, and which one.
     *
     * <p>The first such value in the order the row is read: its inputs as they were written, then
     * the expectation. So this says what stopped the statement being made and not everything that
     * is wrong with the row.
     */
    record Incomplete(Side side, Incompleteness.Code why) implements NotStated {

        public Incomplete {
            if (side == null) {
                throw new IllegalArgumentException("a value that could not be carried is one of"
                        + " the values the row states");
            }
            if (why != Incompleteness.Code.VALUE_TRUNCATED
                    && why != Incompleteness.Code.VALUE_UNREADABLE) {
                // What is said here is about a value: it was larger than what is kept, or it could
                // not be read. A reading that did not finish is not about any of the row's values
                // and is `NotRead`, which says so without a word for a value beside it.
                throw new IllegalArgumentException(why + " is not something that happens to a value");
            }
        }
    }

    /**
     * The row was read and the evaluation stopped before its values were.
     *
     * <p>Carries no reason. There is an evaluation of this row and it says how far it got — the
     * stage it reached, how it ended, and where it stopped — so a word for it here would be that
     * fact restated in a vocabulary that says less.
     *
     * <p>Not a {@link NotStated}. That is what a row states where it states no values, and this is
     * not about the row at all: it is a compile that has not finished with it. A program the
     * language accepted holds none of these — every way of stopping before a row's values is a way
     * a compile refuses the program — and what makes that a fact rather than a rule to keep is that
     * what an output is handed cannot be one.
     *
     * <p>Told apart from {@link NotRead}, which is a row there is no evaluation of at all. The two
     * are one sentence in English and two facts: one is a reading that stopped, the other a reading
     * that never reached the row, and only the second has to say why.
     */
    record StoppedBeforeItsValues() implements RowStatement {}

    /**
     * Nothing read the row at all, and why nothing did.
     *
     * <p>There is no evaluation of it: the classes it would have run would not link, or nothing was
     * observed of the source it is written in. So the reason is about the reading rather than about
     * any of the row's values, and it is said here because there is no evaluation beside this to
     * say it.
     *
     * <p>Said rather than left out. A row nothing came back for is a row someone wrote, and one
     * arriving as no row would have a reader count a set it never walked as one it walked and found
     * empty.
     */
    record NotRead(Incompleteness.Code why) implements NotStated {

        public NotRead {
            if (why == null || !why.leftNoRowRead()) {
                throw new IllegalArgumentException("a row that was not read says why nothing was"
                        + " read of it, and " + why + " is a reason a row that was read fell short");
            }
        }
    }

    /** Which of the values a row states. */
    sealed interface Side {

        /** The input at {@code at}, counted from zero, in the order the behavior takes them. */
        record AnInput(int at) implements Side {

            public AnInput {
                if (at < 0) {
                    throw new IllegalArgumentException("an input stands at zero or later: " + at);
                }
            }
        }

        /** What the row states of the answer. */
        record TheExpectation() implements Side {}
    }

    /**
     * What a row with these values states.
     *
     * <p>The one place a statement is made of values, so that what {@link Stated} means is decided
     * once. A value that is not there in full, and one larger than what is kept, are both values a
     * reader cannot be given — the first because nothing here has it, the second because carrying
     * it would carry a value nobody wrote — and both come back as {@link Incomplete} saying which
     * and why.
     *
     * <p>Held to {@link Limits#DEFAULT} and not to limits a caller chooses. What a row's inputs are
     * observed under is that one, so a row's two halves are held to one size; and a type whose
     * meaning came from an argument would mean one thing where it was made and another where it was
     * read, which is what a reader of a {@link Stated} would then have to ask about before it could
     * do anything with the values. How much is kept is a thing to change, in the one place it is
     * written; whose choice it is, is not.
     */
    static RowStatement of(List<ObservedValue> inputs, Expectation expects) {
        return under(inputs, expects, Limits.DEFAULT);
    }

    private static RowStatement under(List<ObservedValue> inputs, Expectation expects,
                                      Limits kept) {
        if (expects == null) {
            throw new IllegalArgumentException("a row states something of the answer");
        }
        for (int i = 0; i < inputs.size(); i++) {
            Incompleteness.Code stopped = kept.stoppedBy(inputs.get(i));
            if (stopped != null) {
                return new Incomplete(new Side.AnInput(i), stopped);
            }
        }
        // What the row states of the answer is read whole, so that a comparison is made against what
        // was written; whether it may be carried is asked of the same limits an input is held to, so
        // that one row's two halves are held to one size.
        Incompleteness.Code stopped = switch (expects) {
            case Expectation.TheValue(Asserted value) -> kept.stoppedBy(value);
            // A case is a name. Nothing about it can be too large or fail to be read.
            case Expectation.TheCase _ -> null;
        };
        return stopped != null ? new Incomplete(new Side.TheExpectation(), stopped)
                : new Stated(inputs, expects);
    }
}
