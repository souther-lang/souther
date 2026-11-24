package souther.compiler.partition;

import java.util.function.Function;
import java.util.function.IntFunction;
import java.util.function.Supplier;

/**
 * What is shown of one step put together from what each of several readings of it shows: each
 * way a run gets to it, each application of the closure it stands in, each way of the values it
 * is over, each kind of site it is.
 *
 * <p>The one rule every reader of a stop puts readings together by, so that none puts them
 * together another way: a stop shown by one is a run that stops, whatever the others show; not
 * resolved where some reading is not, or where the readings are not every one there is; and
 * safe only where every reading there is shows it safe. What it comes to does not turn on the
 * order the readings are asked in: which stop or which reason is said may, and whether a run
 * stops does not.
 */
final class WhatEveryWayShows {

    private WhatEveryWayShows() {
    }

    /** What one reading shows. */
    enum Shown { SAFE, STOPS, NOT_RESOLVED }

    /**
     * What the {@code ways} readings {@code judgedBy} answers show together, each told apart by
     * {@code shown}: the first that shows a stop, asked no further; otherwise the first not
     * resolved; otherwise, where they are not {@code every} reading there is,
     * {@code notEveryWay}; otherwise the first, which is safe, or {@code noWay} where there is
     * none.
     */
    static <J> J together(int ways, IntFunction<J> judgedBy, Function<J, Shown> shown,
                          boolean every, Supplier<J> notEveryWay, Supplier<J> noWay) {
        J safe = null;
        J open = null;
        for (int at = 0; at < ways; at++) {
            J judged = judgedBy.apply(at);
            switch (shown.apply(judged)) {
                case STOPS -> {
                    return judged;
                }
                case NOT_RESOLVED -> open = open == null ? judged : open;
                case SAFE -> safe = safe == null ? judged : safe;
            }
        }
        if (open != null) {
            return open;
        }
        if (!every) {
            return notEveryWay.get();
        }
        return safe != null ? safe : noWay.get();
    }

    /** What a stop at an operation shows. */
    static Shown of(StopAssessment.Judgement judged) {
        return switch (judged) {
            case StopAssessment.Judgement.Safe _ -> Shown.SAFE;
            case StopAssessment.Judgement.Stops _ -> Shown.STOPS;
            case StopAssessment.Judgement.Unresolved _ -> Shown.NOT_RESOLVED;
        };
    }

    /** What a stop at a construction shows. */
    static Shown of(ConstructionStopAssessment.Judgement judged) {
        return switch (judged) {
            case ConstructionStopAssessment.Judgement.Safe _ -> Shown.SAFE;
            case ConstructionStopAssessment.Judgement.Stops _ -> Shown.STOPS;
            case ConstructionStopAssessment.Judgement.Unresolved _ -> Shown.NOT_RESOLVED;
        };
    }
}
