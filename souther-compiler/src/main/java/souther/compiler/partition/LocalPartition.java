package souther.compiler.partition;

import souther.compiler.inputs.BlockReason;

import java.util.List;

/**
 * What a position's own type and rules divide it into, as one of three answers about the model.
 *
 * <p>Three answers and not a tally of the readers there happened to be. {@link Open} is not "the
 * lists came back empty" — it is <b>the position's local rules were read to the end and the model
 * states no division here</b>, which is a sentence about the model and the only one an absence may
 * be built on. Written as a count of empty producers, the sentence was one line of a caller away
 * from every position that happened to have nothing beside it, and a producer with the answer
 * stayed outside what "everything was asked" meant (issue #772).
 *
 * <p>None of these carries the reading it came from. Which is what holds the sentence: a reading is
 * completed and the answer derived from it ({@link LocalInspection}), and an {@code Open} has
 * nothing of its own with which to say the reading ran to the end when it did not. A fourth thing
 * to read arrives as another way to be {@link Divided} or {@link Blocked}, not as another empty
 * list to remember to check.
 */
public sealed interface LocalPartition {

    /**
     * The model divides the position: into classes, by lines, or both.
     *
     * <p>Never neither. A value of this carrying no classes and no cuts would be an open position
     * dressed as a divided one, and the phase after this one would never be reached for it.
     *
     */
    record Divided(List<PartitionClass> classes, CutEvidence cuts) implements LocalPartition {

        public Divided {
            classes = List.copyOf(classes);
            if (classes.isEmpty() && cuts instanceof CutEvidence.None) {
                throw new IllegalArgumentException(
                        "nothing divides this position, which is a different answer");
            }
        }
    }

    /**
     * The position's local rules were read to the end, and the model divides it no way.
     *
     * <p>A conclusion rather than a tally. It says nothing about the rules a behavior's body
     * writes — those have not been read — so it is what licenses the questions after it rather than
     * a verdict of its own.
     */
    record Open() implements LocalPartition {}

    /**
     * A rule about this position was written and the reading did not take it in.
     *
     * <p>Not a division and not the absence of one. Nothing follows about what the model does here,
     * which is the point: the values are as wide as the rules could be read as, and a rule this
     * could not read can divide the position as easily as the ones it could.
     */
    record Blocked(BlockReason why) implements LocalPartition {

        public Blocked {
            if (why == null) {
                throw new IllegalArgumentException(
                        "a position blocked by nothing is an open one, which is a different answer");
            }
        }
    }
}
