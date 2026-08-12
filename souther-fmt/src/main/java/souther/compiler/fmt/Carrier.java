package souther.compiler.fmt;

/**
 * What a {@link Place} can be handed.
 *
 * <p>Three of these are where a comment stands relative to what it is about, and they divide that
 * question completely: on lines of its own in front of the place, on the place's own line, and on
 * lines of its own after it. A set holding only the first two says that a comment below what it
 * describes is one of the other two, and there is no reading of it that makes it either — written
 * above the next construct it is about that construct, and written at the end of the previous line
 * it is a different kind of comment than the author wrote.
 *
 * <p>{@link #AT_END} answers a different question, which is why it does not upset that division:
 * not where a comment stands beside a member, but that no member follows it at all. It is the
 * comment a container holds after its last member, and what is below it is the container closing.
 */
enum Carrier {

    /** On lines of its own, in front of the place. */
    ABOVE,

    /** At the end of the line the place ends — after whatever the construct holding it writes
     *  between this place and the next, since that punctuation is on the same line. */
    TRAILING,

    /**
     * On lines of its own, after the place, with a member still to come.
     *
     * <p>Only reached where a blank line separates the comment from that member: without one the
     * comment runs straight into what follows and is that member's, which is {@link #ABOVE}. The
     * blank line itself is written by whatever separates the two members and not from here — the
     * comment is below one member and above the separator, and a carrier that wrote the separator
     * too would be saying where the next member begins.
     */
    BELOW,

    /** Inside the place, under its last member and before what closes it. */
    AT_END
}
