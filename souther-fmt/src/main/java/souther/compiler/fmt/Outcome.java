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
 * <p>Which rule the thing that refused answers to is not here. This says that the flat layout was
 * refused rather than not fitted; naming the obligation behind a forced break is the forced-layout
 * rule's, and it can be given without changing this.
 */
sealed interface Outcome {

    /** Written on one line: the line it takes is within the width and nothing in it refuses to. */
    record Flat() implements Outcome {}

    /** Written down the page because the line it would take is over the width. */
    record BrokenByWidth() implements Outcome {}

    /**
     * Written down the page because something in it cannot share a line with what follows, and
     * that thing. Naming it is what lets the obligation behind it be given later without the group
     * being measured again to find out which of them it was.
     */
    record BrokenByForcedLayout(Doc refusing) implements Outcome {}
}
