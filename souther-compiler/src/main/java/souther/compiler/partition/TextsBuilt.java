package souther.compiler.partition;

import souther.compiler.abort.GetsPast;
import souther.compiler.values.TextExtents;
import souther.exact.BuiltTextBounds;

import java.math.BigInteger;

/**
 * How long a text an operation builds of texts comes to, and each text it builds on the way, from
 * ceilings on what it is handed ({@link GetsPast.TextBuilt}): so whether a run gets past building
 * it is a question of those ceilings and the length a {@code String} holds.
 *
 * <p>What each operation builds and measures is the run time's account of its operations
 * ({@link TextExtents#BUILT_TEXTS}), kept beside the arithmetic a run and this compiler share.
 * This hands it the ceilings of the operands a site's account of itself names, and holds nothing
 * of its own.
 */
final class TextsBuilt {

    private TextsBuilt() { }

    /** What each operand of the site is at most, each asked only of an operand the operation
     *  reads as that. */
    interface Ceilings {

        /** The most code points the text at {@code operand} holds. */
        BigInteger codePoints(int operand);

        /** The most texts the list at {@code operand} holds. */
        BigInteger elements(int operand);

        /** The most code points each text the list at {@code operand} holds. */
        BigInteger codePointsOfEach(int operand);

        /** The greatest the {@code Int} at {@code operand} comes to, or null where nothing ends
         *  it. */
        BigInteger number(int operand);
    }

    /** The bound on what {@code built} builds of operands no more than {@code of} says. */
    static BuiltTextBounds.Bound of(GetsPast.TextBuilt built, Ceilings of) {
        BuiltTextBounds account = TextExtents.BUILT_TEXTS;
        return switch (built) {
            case GetsPast.TextBuilt.Joined(int first, int second) ->
                    account.appended(of.codePoints(first), of.codePoints(second));
            case GetsPast.TextBuilt.JoinedWith(int list, int separator) ->
                    account.joinedWith(of.elements(list), of.codePointsOfEach(list),
                            separator < 0 ? BigInteger.ZERO : of.codePoints(separator));
            case GetsPast.TextBuilt.Copies(int text, int count) ->
                    account.repeated(of.codePoints(text), of.number(count));
            case GetsPast.TextBuilt.Padded(int text, int width, int pad) ->
                    account.padded(of.codePoints(text), of.number(width), of.codePoints(pad));
            case GetsPast.TextBuilt.Reversed(int text) -> account.reversed(of.codePoints(text));
            case GetsPast.TextBuilt.Replaced(int text, int target, int replacement) ->
                    account.replaced(of.codePoints(text), of.codePoints(replacement));
        };
    }

    /** Whether every text {@code bound} says is built on the way fits in a {@code String}. */
    static boolean fits(BuiltTextBounds.Bound bound) {
        return bound.fitsIn(TextExtents.LONGEST_STRING);
    }
}
