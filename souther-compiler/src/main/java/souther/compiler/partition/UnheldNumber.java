package souther.compiler.partition;

import souther.compiler.observe.RunSensitivity;
import souther.exact.ExactFailure;
import souther.exact.ExactRangeExceeded;
import souther.exact.ExactRoomExceeded;

/**
 * Why a number this compiler worked out exactly could not be held, in the two ways that differ for
 * whoever reads the answer.
 *
 * <p>The exact arithmetic says which and leaves the meaning to the caller ({@link ExactFailure}), and
 * this is that meaning in the analysis: whether a run with more room would have come to the number.
 * One of them it would, and the other no run would, so the two answer {@link #runSensitivity}
 * oppositely. Held as one, a reader is either sent to widen a run that will come back the same or
 * told nothing could be done about a number a wider run holds.
 */
public enum UnheldNumber {

    /** The run had no room for what working the number out needed, and a run with more has. */
    MORE_ROOM_COULD_ANSWER,

    /** The number has no representation here, and no run with more room gives it one. */
    NO_REPRESENTATION_EXISTS;

    /** What a failure of the exact arithmetic says about the number, in this vocabulary. */
    public static UnheldNumber of(ExactFailure failure) {
        return switch (failure) {
            case ExactRoomExceeded _ -> MORE_ROOM_COULD_ANSWER;
            case ExactRangeExceeded _ -> NO_REPRESENTATION_EXISTS;
        };
    }

    /** Whether measuring again, allowing more, could hold the number. */
    public RunSensitivity runSensitivity() {
        return switch (this) {
            case MORE_ROOM_COULD_ANSWER -> RunSensitivity.MAY_CHANGE;
            case NO_REPRESENTATION_EXISTS -> RunSensitivity.UNAFFECTED;
        };
    }
}
