package souther.compiler.meaning;

import souther.compiler.inputs.TermPath;
import souther.compiler.semantics.CaseMapping;

import java.util.Objects;
import java.util.OptionalLong;

/**
 * The string a piece is a piece of, as the pieces of it were taken: what a statement about the
 * piece is about, which a row reads off the string it puts at the position.
 *
 * <p>Part of what a statement about a piece states, and so of what tells it from a statement about
 * a piece of another string: two pieces under one witness ({@link PieceWitness}) are one piece only
 * where they are pieces of the same string, parted the same way.
 *
 * @param string     the position of the string, or of the one it is made of
 * @param conversion what the string is made of that one by, none where it is that one
 * @param separator  the code point it is parted at
 * @param from       the index of the first piece held
 * @param until      the index the pieces held stop before, or none where they run to the last
 */
public record PartedString(TermPath string, CaseMapping conversion, int separator, long from,
                           OptionalLong until) {

    public PartedString {
        Objects.requireNonNull(string, "the string stands at some position");
        Objects.requireNonNull(conversion, "the string is converted or it is not");
        Objects.requireNonNull(until, "the pieces stop somewhere or run to the last");
    }

    /**
     * Whether the pieces held are the one piece at {@code from}: the one piece a row's string has
     * there, or none where it has fewer. Of a window of more pieces, which one a statement about
     * a piece is about is the quantifier's and no row's.
     */
    public boolean isOnePiece() {
        return from < Long.MAX_VALUE && until.isPresent() && until.getAsLong() == from + 1;
    }

    /** What tells these pieces from the pieces of another string, written out. */
    public String spelled() {
        return conversion.writtenAround(string.toString()) + " parted at " + separator + " from "
                + from + until.stream().mapToObj(to -> " to " + to).findFirst().orElse("");
    }
}
