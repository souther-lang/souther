package souther.compiler.observe;

import souther.compiler.diag.SourcePos;
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
 * question, and each answer to it names which of the row's values could not be handed over — one a
 * stand-in states, one the row states itself — or says that nothing read the row at all. A row that
 * cannot be handed over must not arrive as no row all the same: a reader given nothing for it would
 * count a row it never saw among the ones it walked and found nothing wrong with.
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
     * What the row hands over: what stands in for each dependency, the inputs, and what it states of
     * the answer.
     *
     * <p>Every value here is whole and is one these limits keep. Made by {@link RowStatements#read},
     * which is what decides that: a value read whole is not always one a snapshot may carry, and the
     * two questions answered in two places would be a {@code Stated} that means one thing where it
     * was built and another where it was read.
     *
     * <p>A class and not a record, so that the one rule about what these hold cannot be gone round.
     * A record's canonical constructor is as public as the record, and a value larger than what is
     * kept would be written straight past the reading that decides what a row states; made only by
     * {@link RowStatements#read}, it is that reading whichever side makes one.
     *
     * <p>A value all the same, and it says so itself. What a query stops work on is whether an
     * answer equals the one before it, and this rides inside one — so a statement that answered
     * only for itself would make every compile that read a row look like a compile that changed it.
     * The parts it is are the parts it is equal by.
     */
    final class Stated implements RowStatement {

        private final List<StoodIn> standIns;
        private final List<ObservedValue> inputs;
        private final Expectation expects;

        private Stated(List<StoodIn> standIns, List<ObservedValue> inputs, Expectation expects) {
            this.standIns = List.copyOf(standIns);
            this.inputs = List.copyOf(inputs);
            this.expects = expects;
        }

        /** For the reading that decides what a row states, having decided it. */
        static Stated of(List<StoodIn> standIns, List<ObservedValue> inputs, Expectation expects) {
            return new Stated(standIns, inputs, expects);
        }

        /**
         * What stands in for each of the behavior's dependencies, in the order it requires them.
         *
         * <p>Empty for a behavior that depends on nothing, which is a behavior with nothing to stand
         * in for rather than a row that left something out.
         *
         * <p>Beside the inputs and not among them. A dependency is not an argument: the inputs are
         * what the row hands the behavior, and these are what answers the behavior while it runs
         * with them.
         */
        public List<StoodIn> standIns() {
            return standIns;
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
            return other instanceof Stated it && standIns.equals(it.standIns)
                    && inputs.equals(it.inputs) && expects.equals(it.expects);
        }

        @Override
        public int hashCode() {
            return (standIns.hashCode() * 31 + inputs.hashCode()) * 31 + expects.hashCode();
        }

        @Override
        public String toString() {
            return (standIns.isEmpty() ? "" : standIns + " | ") + inputs + " -> " + expects;
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
     * What stands in for a dependency the behavior takes could not be handed over, and why.
     *
     * <p>A row runs against a bound implementation, and where the behavior depends on something
     * injected, what stands in for that dependency is the rest of what makes the row runnable. What
     * a stand-in states is written down — a value on the row, or a table beside it — so it crosses
     * the way the row's own values cross, and a stand-in holding a value that could not be is a row
     * that hands over nothing: a reader given the inputs alone would apply the behavior with nothing
     * to answer its dependency with.
     *
     * <p>The first such stand-in in the order the row is read: what stands in, in the order the
     * behavior requires it, then the inputs, then the expectation. So this says what stopped the
     * statement being made and not everything that is wrong with the row.
     *
     * <p>{@code at} is where a reader is sent, and which place that is follows from {@link #why}.
     * A value that could not be carried is quoted where that value is written — a table states one
     * on each of its rows and one more where it answers what it does not list, and naming the table
     * would leave a reader to find which of them nothing could be made of. A place rather than a
     * {@link Side}, because what a stand-in states is not a list a place in it can be counted along.
     */
    record StandInUnavailable(ValueName.Behavior dependency, SourcePos at,
                              Why why) implements NotStated {

        public StandInUnavailable {
            if (dependency == null || at == null || why == null) {
                throw new IllegalArgumentException("a stand-in that could not be handed over is one"
                        + " dependency's, is quoted somewhere, and says why");
            }
        }

        /**
         * Why what stands in for the dependency could not be handed over.
         *
         * <p>Two, and they are not one fact said twice. A value that was read and cannot be carried
         * is a fact about that value; nothing having been read is a fact about the compile, and
         * there is no value in it for anything to be said about. One reason covering both would
         * have a reader that wants to quote the value ask first whether there is one.
         */
        public sealed interface Why {

            /**
             * It states a value that could not be carried: larger than what is kept, or not one
             * that could be read.
             *
             * <p>The same two a row's own values are refused for, said with the same codes. What a
             * reader may be given is one question, and a stand-in's values are values.
             */
            record AValueOfIt(Incompleteness.Code code) implements Why {

                public AValueOfIt {
                    if (code != Incompleteness.Code.VALUE_TRUNCATED
                            && code != Incompleteness.Code.VALUE_UNREADABLE) {
                        throw new IllegalArgumentException(
                                code + " is not something that happens to a value");
                    }
                }
            }

            /**
             * Nothing this compile read states what the dependency answers.
             *
             * <p>Nothing stands in for it, or what does would not build. Either is said where the
             * row is written the moment anything runs the row, so a program the language accepted
             * holds this only for a row nothing was going to run — and a reader of one is told that
             * the row states no stand-in, rather than being handed an empty one to run against.
             */
            record NothingWasRead() implements Why {}
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

}
