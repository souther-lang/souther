package souther.compiler.fmt;

/**
 * What a {@link Place} can be handed.
 *
 * <p>Three, because a comment is written in three positions relative to what it is about and the
 * three are not the same question: above the line a place opens, at the end of the line it ends, and
 * inside it under its last member.
 */
enum Carrier {

    /** On lines of its own, in front of the place. */
    ABOVE,

    /** At the end of the line the place ends — after whatever the construct holding it writes
     *  between this place and the next, since that punctuation is on the same line. */
    TRAILING,

    /** Inside the place, under its last member and before what closes it. */
    AT_END
}
