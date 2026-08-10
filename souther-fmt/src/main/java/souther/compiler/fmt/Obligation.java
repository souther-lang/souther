package souther.compiler.fmt;

/**
 * Why the canonical form writes a line break whatever the width.
 *
 * <p>{@link TokenDoc.Break#ALWAYS} says that a boundary always breaks, which is a policy: it is
 * what the layout does there and not what is being said by doing it. Five constructions write one,
 * they mean five different things, and told only that a break was forced a reader cannot say which
 * — so the obligation is named where the boundary is built and carried to the break it writes.
 *
 * <p>Not a record of the mechanism. Two constructs writing a member on a line of its own discharge
 * one obligation between them, and the same construct writing a closing bracket discharges another;
 * what makes them one or two is what the rule says, not which method wrote it.
 */
enum Obligation {

    /** A construct written down the page writes each of its members on a line of its own. */
    MEMBERS_TAKE_LINES_OF_THEIR_OWN,

    /** A bracket of a construct written down the page takes a line of its own. */
    A_BRACKET_TAKES_A_LINE_OF_ITS_OWN,

    /** A file ends with one newline. */
    A_FILE_ENDS_WITH_ONE_NEWLINE,

    /** One blank line separates two top-level items, unless an import follows the header or an
     *  import. */
    A_BLANK_LINE_SEPARATES_TOP_LEVEL_ITEMS,

    /** Nothing is written after a comment on the line it is on. The one obligation here that is
     *  not about a construct's shape: it holds wherever a comment stands, and it is why a group
     *  holding one is never laid out flat. */
    NOTHING_SHARES_A_COMMENTS_LINE;

    /** What the rule says, for a reader who is being told their source does not. */
    String said() {
        return switch (this) {
            case MEMBERS_TAKE_LINES_OF_THEIR_OWN ->
                    "a construct written down the page writes its members one to a line";
            case A_BRACKET_TAKES_A_LINE_OF_ITS_OWN ->
                    "a bracket of a construct written down the page takes a line of its own";
            case A_FILE_ENDS_WITH_ONE_NEWLINE -> "a file ends with one newline";
            case A_BLANK_LINE_SEPARATES_TOP_LEVEL_ITEMS ->
                    "one blank line separates two top-level items";
            case NOTHING_SHARES_A_COMMENTS_LINE -> "nothing shares a comment's line";
        };
    }
}
