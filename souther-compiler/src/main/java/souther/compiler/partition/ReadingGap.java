package souther.compiler.partition;

import souther.compiler.observe.Incompleteness;
import souther.compiler.observe.RunSensitivity;

/**
 * Why a reading of a number came to none.
 *
 * <p>What is there and was not kept, and what this compiler never got to. A value the observation
 * did not keep whole is a value that is there, named by the code an observation writes; the rest
 * arrived at no value and have no such code. What a reader does about them differs, so all of them
 * travel, and a quantity stopped in more than one way says each.
 *
 * <p>Whether a wider run would come to another answer is not what tells them apart. An observation
 * answers it out of the code it carries and the codes do not agree with each other — one a wider
 * run keeps, another it meets again — while the three that reached no value answer alike. So it is
 * a question put to a reason rather than a way of sorting them, and {@link
 * souther.compiler.publish.WeakeningWord}, which sorts them more coarsely still for a document,
 * settles it for none of them.
 *
 * <p><b>{@link NoValue} is a place that was reached.</b> A walk that could not be taken and a row
 * that could not be read are this compiler unable to look, which is not the model putting a value
 * somewhere else; said with the same word, a report tells a reader that nothing was written at a
 * position nothing ever looked at. Each of the three is its own arm so that the sentence written
 * for it is chosen from what happened rather than from an emptiness they share.
 *
 * <p><b>Collected and never chosen between.</b> A rule over several terms is read once per term and
 * a point is tried against several readings of several rows, so the reasons arrive a few at a time
 * and are put together. Ranked instead, every place that folds them writes a precedence, every
 * precedence throws one away, and which one a report says comes out of the order a map or a list
 * happened to be walked in.
 */
public sealed interface ReadingGap {

    /**
     * Whether a run of this compiler that allows more could come to a different answer here.
     *
     * <p>Each arm asks whatever holds the fact rather than answering for it: an observation that
     * stopped carries the code, and the code is what every producer of it agrees about. Which is
     * why the answer does not follow from which arm this is — two observations carry two codes and
     * the codes answer differently — and why nothing coarser than an arm may be asked it.
     */
    RunSensitivity runSensitivity();

    /** The observation of a value did not come back whole, and this is what it met. */
    record Observation(Incompleteness.Code code) implements ReadingGap {

        public Observation {
            if (code == null) {
                throw new IllegalArgumentException("an observation that stopped says what it met");
            }
        }

        @Override
        public RunSensitivity runSensitivity() {
            return code.runSensitivity();
        }
    }

    /** The walk arrived at the position and no value of the row stands there under the reading
     *  being tried, so there was none to observe. */
    record NoValue() implements ReadingGap {

        /** Nothing was compared against a figure: the walk met no value, and it meets none however
         *  much a run is allowed. */
        @Override
        public RunSensitivity runSensitivity() {
            return RunSensitivity.UNAFFECTED;
        }
    }

    /**
     * The walk into the row could not be taken, so there was no position to read at.
     *
     * <p>What refuses a step is the reading and the value disagreeing about what is at a position,
     * which is a fact about this compiler's walk and says nothing about the row. A row that stands
     * nowhere below a step took it ({@link NoValue}); this one never got that far.
     */
    record CouldNotWalk() implements ReadingGap {

        /** The reading either exposes a name at a position or it does not, and how much a run is
         *  allowed does not enter into it. */
        @Override
        public RunSensitivity runSensitivity() {
            return RunSensitivity.UNAFFECTED;
        }
    }

    /**
     * A row was asked for and did not come back, so there was nothing to walk.
     *
     * <p>Which of the ways it did not come back — nothing built its values, or the model refused
     * them — is not said here. Both are this compiler unable to put a row in front of the walk, and
     * nothing downstream of the reading acts on the difference; what does tell them apart is
     * {@code RowAsRead.whyNotRead}, and a reader that comes to need it carries it from there rather
     * than from an arm invented here.
     */
    record CouldNotReadRow() implements ReadingGap {

        /** Values that would not build and values the model would not take come back the same way
         *  however much a run is allowed. */
        @Override
        public RunSensitivity runSensitivity() {
            return RunSensitivity.UNAFFECTED;
        }
    }

    ReadingGap NO_VALUE = new NoValue();

    ReadingGap COULD_NOT_WALK = new CouldNotWalk();

    ReadingGap COULD_NOT_READ_ROW = new CouldNotReadRow();

    /** The gap an observation's code is, for a reader holding one. */
    static ReadingGap of(Incompleteness.Code code) {
        return new Observation(code);
    }
}
