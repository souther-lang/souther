package souther.compiler.partition;

import souther.compiler.types.ApplicationsReadOn;
import souther.compiler.types.ModelOccurrence;

import java.util.List;
import java.util.Objects;

/**
 * One construct of a body that may state something a line is drawn from, where the walk of the
 * body met it, and the applications of the closures it stands in
 * ({@link GuardThresholds#comparisonsRead}).
 *
 * <p>Where it stands and nothing read of it. What it states, which lines it draws and where they
 * decide are read after this and cost more than the walk; a reader that asks which comparisons a
 * body has on which applications, before any of that is paid for, reads this. A construct here
 * may state nothing the measurement draws a line from: what it states is not read.
 *
 * @param copy the copy of the model the construct stands in
 * @param on   the applications of the closures it stands in, as the walk said them
 */
public record AComparisonRead(ModelOccurrence copy, AppliedOn on) {

    public AComparisonRead {
        Objects.requireNonNull(copy, "a construct stands in some copy of the model");
        Objects.requireNonNull(on, "inside some closures or none, said or not");
    }

    /**
     * The applications of the closures a construct stands in, as the walk said them: four states
     * and not a count, since none of them is another's number.
     */
    public sealed interface AppliedOn {

        /** Inside no closure: met once wherever the body is run. */
        record Outside() implements AppliedOn {}

        /**
         * Inside closures whose applications are said one by one.
         *
         * @param each every application, as what a line drawn on it is read on, in the order a
         *             run makes them
         */
        record OnEach(List<ApplicationsReadOn> each) implements AppliedOn {

            public OnEach {
                each = List.copyOf(each);
                if (each.isEmpty()) {
                    throw new IllegalArgumentException("a closure applied is applied some times");
                }
            }
        }

        /** Inside a closure whose applications are not said: how many there are is not known,
         *  and no number of them is said. */
        record NotSaid() implements AppliedOn {}

        /** Inside a closure no run applies: nothing here is met on any run. */
        record OnNone() implements AppliedOn {}
    }
}
