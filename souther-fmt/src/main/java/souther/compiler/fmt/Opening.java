package souther.compiler.fmt;

/**
 * How the line a {@link Place} is written on begins.
 *
 * <p>Written once, where the place is written, and read twice. The layout takes the boundary from
 * it; comment ownership takes from it whether a comment written above the place is one the place
 * can carry. Two readers of one value — which a table of lines kept beside the document was not,
 * and a construct could be entered in one and left out of the other without anything noticing.
 *
 * <p>What opens the line is written from here and from nowhere else. A construct that wrote the
 * opener itself and named it here as well would be saying where the line begins twice.
 */
sealed interface Opening {

    Opening NONE = new None();

    /** The one line nothing opens: the first of the file. */
    Opening FILE_BEGINS = new FileBegins();

    /** The boundary that opens this place's line, and what the construct writes after it before
     *  the place itself — a leading comma, or nothing. The boundary is held whole rather than as
     *  its policy, so a forced one carries from here the obligation it is written for. */
    record Breaks(TokenDoc.Gap gap, TokenDoc opener) implements Opening {}

    /**
     * The line is open and no boundary opened it, which is true in one place: the start of a file.
     *
     * <p>Anywhere else a place with a line of its own says what opens that line, so that whether
     * the place has one and what wrote it are one value. A place that claimed a line while
     * something else wrote the boundary would be the two-table arrangement again, one table deep.
     */
    record FileBegins() implements Opening {}

    /** The place does not open a line: what holds it goes on writing the line it is on. */
    record None() implements Opening {}

    /** A line opened by a boundary the layout may break, which the group holding it settles. */
    static Opening breaks(TokenDoc.Break policy) {
        return breaks(policy, TokenDoc.NIL);
    }

    /** The same, where the construct writes something at the head of the line before the place —
     *  the connector a chained construct joins its stages with. */
    static Opening breaks(TokenDoc.Break policy, TokenDoc opener) {
        return new Breaks(new TokenDoc.Gap(policy, null), opener);
    }

    /** A line opened by a boundary written whatever the width, for the obligation named. */
    static Opening forced(Obligation obligation) {
        return forced(obligation, TokenDoc.NIL);
    }

    /** The same, where the construct writes something at the head of the line before the place. */
    static Opening forced(Obligation obligation, TokenDoc opener) {
        return new Breaks(new TokenDoc.Gap(TokenDoc.Break.ALWAYS, obligation), opener);
    }

    /** The boundary that opens the line, or nothing where the line is already open. */
    default TokenDoc boundary() {
        return switch (this) {
            case Breaks b -> b.gap();
            case FileBegins _, None _ -> TokenDoc.NIL;
        };
    }

    /**
     * What the construct writes at the head of the line, after the boundary and before the place.
     *
     * <p>It is on the place's line, so what is written above the place is written above it too — a
     * comment put after a leading comma would leave the member starting a line the comma never
     * opened. That is why this is here and not in front of the whole thing.
     */
    default TokenDoc opener() {
        return switch (this) {
            case Breaks b -> b.opener();
            case FileBegins _, None _ -> TokenDoc.NIL;
        };
    }

    /**
     * Whether the place has a line of its own to be written above.
     *
     * <p>A place whose line is opened by a boundary the layout can break has one. A place the
     * construct runs into has not: a comment written there would have the rest of that line
     * written inside it, so the comment belongs to whatever opened the line instead.
     */
    default boolean opensALine() {
        return switch (this) {
            case Breaks b -> b.gap().policy() != TokenDoc.Break.NEVER;
            case FileBegins _ -> true;
            case None _ -> false;
        };
    }
}
