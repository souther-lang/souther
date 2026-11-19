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
 * body reads on which applications, before any of that is paid for, reads this.
 *
 * @param copy         the copy of the model the construct stands in
 * @param applications every application of the closures it stands in, as what a line drawn on it
 *                     is read on; none for one inside no closure, or inside one whose applications
 *                     are not said one by one
 */
public record AComparisonRead(ModelOccurrence copy, List<ApplicationsReadOn> applications) {

    public AComparisonRead {
        Objects.requireNonNull(copy, "a construct stands in some copy of the model");
        applications = List.copyOf(applications);
    }

    /** How many times it is read: once on each application, or once where it stands in none. */
    public int readings() {
        return Math.max(1, applications.size());
    }
}
