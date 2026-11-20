package souther.compiler.inputs;

import java.util.Objects;
import java.util.Optional;

/**
 * One operation of a rule of which neither that a run stops in it nor that none does is shown,
 * and why.
 *
 * <p>Of one operation and never of the rule: another operation of the same rule may be shown to
 * stop a run ({@link AStopShown}) or to stop none, and this says nothing of those.
 *
 * @param operation the operation, as written; none where a run may stop in something worked out
 *                  that no operation names
 * @param why       why neither is shown
 */
public record AStopNotShown(Optional<String> operation, WhyAStopIsNotShown why) {

    public AStopNotShown {
        Objects.requireNonNull(operation, "an operation, or that none names the stop");
        Objects.requireNonNull(why, "a stop is not shown for some reason");
    }
}
