package souther.compiler.fmt;

/**
 * Why a group was laid out the way it was.
 *
 * <p>Broken and broken are not one answer. A group is written down the page because the line it
 * would take is over the width, or because it holds something that cannot be laid out flat at all —
 * a forced break, a trailing comment, a construct that refuses to. Told only that it broke, a reader
 * cannot say whether another width would have kept it whole, and working that out means measuring
 * the group again.
 *
 * <p>This says that the flat layout was refused rather than not fitted. Which obligation the thing
 * that refused was written for is the thing's own, and is read from it.
 */
sealed interface Outcome {

    /** Written on one line: the line it takes is within the width and nothing in it refuses to. */
    record Flat() implements Outcome {}

    /** Written down the page because the line it would take is over the width. */
    record BrokenByWidth() implements Outcome {}

    /**
     * Written down the page because something in it cannot share a line with what follows, and
     * that thing — which carries the obligation it was written for, so the group can be asked why
     * it broke without being measured again to find out which of them it was.
     */
    record BrokenByForcedLayout(Doc.Refuses refusing) implements Outcome {

        /** The obligation the group was written down the page for. */
        Obligation obligation() {
            return refusing.obligation();
        }
    }
}
