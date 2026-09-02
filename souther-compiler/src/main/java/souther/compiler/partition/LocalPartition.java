package souther.compiler.partition;

import java.util.List;

/**
 * What a position's own type and rules divide it into.
 *
 * <p>Two answers about the reading of this position's own declarations, and neither is a verdict
 * about the model. {@link Open} says this reading found no division, which is what licenses asking
 * what a body's rules and the position's own questions come to; whether anything about the model
 * follows from there being no class is answered where those are ({@link PendingPosition}).
 *
 * <p>Neither carries the reading it came from. A reading is completed and the answer derived from
 * it ({@link LocalInspection}), so an {@code Open} has nothing of its own with which to claim the
 * reading ran to the end. A third thing to read arrives as another way to be {@link Divided}, not
 * as another empty list to remember to check.
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
     * Nothing this reading found divides the position.
     *
     * <p>About this reading and not about the model. It says nothing about the rules a behavior's
     * body writes, and nothing about whether the rules of the position leave a question standing —
     * so it is what licenses the questions after it rather than a verdict of its own.
     */
    record Open() implements LocalPartition {}
}
