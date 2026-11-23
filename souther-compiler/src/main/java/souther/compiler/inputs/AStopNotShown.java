package souther.compiler.inputs;

import souther.compiler.check.StopOrigin;

import java.util.List;
import java.util.Objects;
import java.util.Optional;

/**
 * One operation of a rule of which neither that a run stops in it nor that none does is shown,
 * and why.
 *
 * <p>Of one operation and never of the rule: another operation of the same rule may be shown to
 * stop a run ({@link AStopShown}) or to stop none, and this says nothing of those.
 *
 * @param operation the operation, as written, exactly where {@code why} is of one
 *                  ({@link WhyAStopIsNotShown#isOfAnOperation}); none where a run may stop in
 *                  something worked out that no operation names
 * @param why       why neither is shown
 * @param restsOn   where the stops left untold that it rests on are, as far as the readings
 *                  found them; none where {@code why} rests on no such stop
 *                  ({@link WhyAStopIsNotShown#restsOnStopsLeftUntold})
 */
public record AStopNotShown(Optional<String> operation, WhyAStopIsNotShown why,
                            List<StopOrigin> restsOn) {

    public AStopNotShown {
        Objects.requireNonNull(operation, "an operation, or that none names the stop");
        Objects.requireNonNull(why, "a stop is not shown for some reason");
        restsOn = List.copyOf(restsOn);
        if (operation.isPresent() != why.isOfAnOperation()) {
            throw new IllegalArgumentException("an operation is named exactly where " + why
                    + " is said of one");
        }
        if (!restsOn.isEmpty() && !why.restsOnStopsLeftUntold()) {
            throw new IllegalArgumentException(why + " rests on no stop left untold");
        }
    }

    public AStopNotShown(Optional<String> operation, WhyAStopIsNotShown why) {
        this(operation, why, List.of());
    }
}
