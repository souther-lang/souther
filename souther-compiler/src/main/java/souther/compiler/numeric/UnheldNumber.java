package souther.compiler.numeric;

import souther.exact.ExactFailure;
import souther.exact.ExactRangeExceeded;
import souther.exact.ExactRoomExceeded;

import java.util.EnumSet;
import java.util.Set;

/**
 * Why a number this compiler worked out exactly could not be held, in the two ways the arithmetic
 * tells apart.
 *
 * <p>The exact arithmetic says which and leaves the meaning to the caller ({@link ExactFailure}): the
 * host had no room for what the answer needed, or the answer has no representation. A reader is told
 * which, because the first is a question for a machine with more room and the second for nobody.
 *
 * <p><b>Not whether a wider run answers.</b> A wider run is this compiler on the same host with its
 * allowances widened ({@link souther.compiler.observe.RunSensitivity}), and neither of these is an
 * allowance: the room that ran out is the host's, and no figure of this compiler's was compared
 * against. So both are met again by every wider run, and this says nothing on that axis. What does is
 * the vocabulary carrying it, which answers for both alike.
 *
 * <p>Held in this package because {@link ExactRatio} answers with it directly: an operation that
 * fails is one of this arithmetic's own outcomes and not a partition question, so the word for it
 * lives beside the arithmetic and not above it.
 */
public enum UnheldNumber {

    /** The host had no room for what working the number out needed. */
    MORE_ROOM_COULD_ANSWER,

    /** The number has no representation here, whatever room there is. */
    NO_REPRESENTATION_EXISTS;

    /** What a failure of the exact arithmetic says about the number, in this vocabulary. */
    public static UnheldNumber of(ExactFailure failure) {
        return switch (failure) {
            case ExactRoomExceeded _ -> MORE_ROOM_COULD_ANSWER;
            case ExactRangeExceeded _ -> NO_REPRESENTATION_EXISTS;
        };
    }

    /**
     * What several numbers not held say of one answer made of them all: more room answers it only
     * where more room answers every one of them, and otherwise nothing does. The same whichever of
     * them was met first.
     *
     * @param each the ways each part of the answer was not held; one or more
     */
    public static UnheldNumber ofAll(Set<UnheldNumber> each) {
        if (each.isEmpty()) {
            throw new IllegalArgumentException("an answer not held has some part not held");
        }
        return each.equals(EnumSet.of(MORE_ROOM_COULD_ANSWER)) ? MORE_ROOM_COULD_ANSWER
                : NO_REPRESENTATION_EXISTS;
    }
}
