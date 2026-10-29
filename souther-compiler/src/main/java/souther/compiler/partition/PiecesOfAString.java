package souther.compiler.partition;

import java.util.OptionalInt;
import java.util.OptionalLong;

import souther.compiler.inputs.NumericTerm;
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
 */
record PiecesOfAString(int separator, Quantity string, PieceWindow window) {

    PiecesOfAString {
        if (separator < 0 || string == null || window == null || window.isEmpty()) {
            throw new IllegalArgumentException("pieces are some indexes of a string parted at a"
                    + " code point");
        }
    }

    /** The piece at the index a lookup picked. */
    static PiecesOfAString of(Quantity.ThePieceAt piece) {
        return new PiecesOfAString(piece.separator(), piece.string(),
                new PieceWindow(piece.index(), OptionalLong.of(piece.index() + 1L)));
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
                : new PiecesOfAString(separator.getAsInt(), piece.string(), window);
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
        return ConvertedText.of(string);
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
