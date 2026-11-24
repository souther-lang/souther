package souther.compiler.partition;

import java.util.Objects;
import java.util.Optional;
import java.util.OptionalInt;
import java.util.OptionalLong;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.meaning.PartedString;
import souther.compiler.meaning.PieceWitness;
import souther.compiler.meaning.Quantity;

/**
 * The pieces at some indexes of a string of the input parted at one code point, which a statement
 * compares with a value: the piece at an index a lookup picked, or whichever piece of a window the
 * statement is about.
 *
 * <p>The string is a string of the input as it stands, or one a case conversion made of it
 * ({@code String.lowercase(email)}): the position it is made of, and what was done to it between.
 *
 * @param separator the code point it is parted at
 * @param string    the string, a string of the input or what a case conversion answers of one
 * @param window    the indexes of the pieces
 * @param within    the statement about some piece it is a piece of, or none where it is the one
 *                  a lookup picked. Which statement it is read in is not which pieces they are,
 *                  so it is no part of what makes two of these the same
 */
record PiecesOfAString(int separator, Quantity string, PieceWindow window,
                       Optional<PieceWitness> within, ConvertedText converted) {

    PiecesOfAString {
        if (separator < 0 || (string == null) == (converted == null) || window == null
                || window.isEmpty()) {
            throw new IllegalArgumentException("pieces are some indexes of a string parted at a"
                    + " code point");
        }
    }

    /** The pieces of a string written as an expression, whatever statement they are read in. */
    PiecesOfAString(int separator, Quantity string, PieceWindow window,
                    Optional<PieceWitness> within) {
        this(separator, string, window, within, null);
    }

    /**
     * The piece a statement of the way holds to a language, as the statement says which it is:
     * the string is the one at a position, made by the case conversions it names.
     */
    static PiecesOfAString heldBy(PartedString parted, PieceWitness within) {
        return new PiecesOfAString(parted.separator(), null,
                new PieceWindow(parted.from(), parted.until()), Optional.of(within),
                new ConvertedText(new NumericTerm.ValueOf(parted.string()), parted.conversion()));
    }

    @Override
    public boolean equals(Object other) {
        if (!(other instanceof PiecesOfAString that) || separator != that.separator
                || !window.equals(that.window)) {
            return false;
        }
        ConvertedText whole = whole();
        return whole != null ? whole.equals(that.whole())
                : that.whole() == null && Objects.equals(string, that.string);
    }

    @Override
    public int hashCode() {
        ConvertedText whole = whole();
        return Objects.hash(separator, window, whole, whole == null ? string : null);
    }

    /** The piece at the index a lookup picked. */
    static PiecesOfAString of(Quantity.ThePieceAt piece) {
        return new PiecesOfAString(piece.separator(), piece.string(),
                new PieceWindow(piece.index(), OptionalLong.of(piece.index() + 1L)),
                Optional.empty());
    }

    /**
     * The pieces a statement about some piece of a window is about, or null where the string is
     * parted into its characters or the window holds none.
     */
    static PiecesOfAString of(Quantity.APieceOf piece) {
        OptionalInt separator = piece.separator();
        PieceWindow window = new PieceWindow(piece.from(),
                piece.among() > 0 ? OptionalLong.of(piece.among()) : OptionalLong.empty());
        return separator.isEmpty() || window.isEmpty() ? null
                : new PiecesOfAString(separator.getAsInt(), piece.string(), window,
                        Optional.of(piece.within()));
    }

    /** The index of the first piece. */
    int first() {
        return Math.toIntExact(window.from());
    }

    /** The index the pieces stop before, or below nought where they run to the last. */
    long until() {
        return window.until().orElse(-1);
    }

    /** The string and what was done to it, or null where it is made of the input by anything but
     *  case conversions of one string of it. */
    ConvertedText whole() {
        return converted != null ? converted : ConvertedText.of(string);
    }

    /**
     * What a model calls these pieces of the string at {@code path}: the piece at an index, or a
     * piece from one.
     */
    String calledOver(String path) {
        ConvertedText whole = whole();
        String text = whole == null ? path : whole.through().writtenAround(path);
        if (window.until().isPresent() && window.until().getAsLong() == window.from() + 1) {
            return "piece " + window.from() + " of " + text;
        }
        return "a piece from " + window.from()
                + (window.until().isPresent() ? " up to " + window.until().getAsLong() : "")
                + " of " + text;
    }

    /** The position of the string, where it is made of one by case conversions or none; null
     *  otherwise. */
    NumericTerm.ValueOf place() {
        ConvertedText whole = whole();
        return whole == null ? null : whole.place();
    }
}
