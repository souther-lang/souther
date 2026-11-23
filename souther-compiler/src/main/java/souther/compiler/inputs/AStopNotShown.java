package souther.compiler.inputs;

import souther.compiler.check.CallPassage;

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
 * @param call      the call of a behavior a run may stop in, with what the behavior is told of,
 *                  where {@code why} is {@link WhyAStopIsNotShown#IN_A_CALL}; none otherwise
 */
public record AStopNotShown(Optional<String> operation, WhyAStopIsNotShown why,
                            Optional<CallPassage.WhyOpen.ACall> call) {

    public AStopNotShown {
        Objects.requireNonNull(operation, "an operation, or that none names the stop");
        Objects.requireNonNull(why, "a stop is not shown for some reason");
        Objects.requireNonNull(call, "a call, or that the stop is in none");
        if (call.isPresent() != (why == WhyAStopIsNotShown.IN_A_CALL)) {
            throw new IllegalArgumentException("a call is named exactly where the stop is in one");
        }
    }

    public AStopNotShown(Optional<String> operation, WhyAStopIsNotShown why) {
        this(operation, why, Optional.empty());
    }
}
