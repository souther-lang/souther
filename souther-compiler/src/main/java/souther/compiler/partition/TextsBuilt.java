package souther.compiler.partition;

import souther.compiler.abort.GetsPast;
import souther.compiler.values.TextExtents;

import net.unit8.notation199x.Normalization;

import java.math.BigInteger;

/**
 * How long a text an operation builds of texts comes to, and each text it builds on the way, from
 * ceilings on what it is handed ({@link GetsPast.TextBuilt}): so whether a run gets past building
 * it is a question of those ceilings and the length a {@code String} holds.
 *
 * <p>Every {@code String} is in canonical form (NFC), and each operation builds its text and puts it
 * in that form, measuring what it is defined as building before it builds it ({@code Strings}).
 * Two facts the run time's tables state bound what putting a text in that form does to its
 * length. Two texts each in the form, joined, come to no more than the two and
 * {@link Normalization#seamGrowthBound} once put in it; and no text comes to more than
 * {@link Normalization#longestDecomposition} times as many code points as it holds. The second
 * bounds the other way too: a text holds no more code points than its canonical decomposition,
 * which is the decomposition of the text in canonical form, so no text is more than that many
 * times as long as it is in canonical form.
 *
 * <p>Each answer is a bound and claims no text reaches it.
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

    /**
     * A bound on the code points of the text {@code built} answers, and of every text it is defined
     * as building on the way, which the answer is one of.
     *
     * @param answer the most code points the answer holds
     * @param onTheWay the most code points any text built on the way holds, the answer among
     *                 them; null where nothing ends them
     */
    record Bound(BigInteger answer, BigInteger onTheWay) {

        /** Whether every text built on the way is no longer than a {@code String} holds. */
        boolean fits() {
            return onTheWay != null
                    && onTheWay.compareTo(BigInteger.valueOf(TextExtents.LONGEST_STRING)) <= 0;
        }
    }

    /** What {@link Normalization#seamGrowthBound} says joining two texts in canonical form adds. */
    private static final BigInteger SEAM = BigInteger.valueOf(
            Normalization.seamGrowthBound(Normalization.Form.NFC));

    /** How many times as long as a text it is at most once put in canonical form. */
    private static final BigInteger GROWS = BigInteger.valueOf(
            Normalization.longestDecomposition(Normalization.Form.NFC));

    /** How many times as long as its canonical form a text is at most: its canonical
     *  decomposition holds no fewer code points, and no more than this many times as many as the
     *  canonical form does. */
    private static final BigInteger SHRINKS = BigInteger.valueOf(
            Normalization.longestDecomposition(Normalization.Form.NFD));

    /** The bound on what {@code built} builds of operands no more than {@code of} says. */
    static Bound of(GetsPast.TextBuilt built, Ceilings of) {
        return switch (built) {
            case GetsPast.TextBuilt.Joined(int first, int second) ->
                    joined(of.codePoints(first).add(of.codePoints(second)), BigInteger.ONE);
            case GetsPast.TextBuilt.JoinedWith(int list, int separator) ->
                    joinedWith(of.elements(list), of.codePointsOfEach(list),
                            separator < 0 ? BigInteger.ZERO : of.codePoints(separator));
            case GetsPast.TextBuilt.Copies(int text, int count) ->
                    copies(of.codePoints(text), of.number(count));
            case GetsPast.TextBuilt.Padded(int text, int width, int pad) ->
                    padded(of.codePoints(text), of.number(width), of.codePoints(pad));
            case GetsPast.TextBuilt.Reversed(int text) -> grown(of.codePoints(text));
            case GetsPast.TextBuilt.Replaced(int text, int target, int replacement) ->
                    grown(of.codePoints(text).multiply(of.codePoints(replacement).max(BigInteger.ONE)));
        };
    }

    /**
     * Texts {@code codePoints} long together, each in canonical form, joined at {@code seams}
     * places: no longer than they are together before it is put in the form, and each place adds
     * no more than a seam does.
     */
    private static Bound joined(BigInteger codePoints, BigInteger seams) {
        BigInteger answer = codePoints.add(seams.max(BigInteger.ZERO).multiply(SEAM));
        return new Bound(answer, answer);
    }

    /**
     * At most {@code elements} texts of at most {@code each} code points, with a separator of at
     * most {@code separator} between each two: the texts and the separators together, joined at a
     * place on each side of each separator, or at one between each two where the separator is
     * empty. None is the empty text.
     */
    private static Bound joinedWith(BigInteger elements, BigInteger each, BigInteger separator) {
        if (elements.signum() <= 0) {
            return new Bound(BigInteger.ZERO, BigInteger.ZERO);
        }
        BigInteger between = elements.subtract(BigInteger.ONE);
        BigInteger codePoints = elements.multiply(each).add(between.multiply(separator));
        BigInteger seams = separator.signum() == 0 ? between : between.shiftLeft(1);
        return joined(codePoints, seams);
    }

    /**
     * At most {@code count} copies of a text of at most {@code codePoints}: as long as the copies
     * together, joined between each two. None, or no copy, is the empty text, and a count nothing
     * ends is no bound.
     */
    private static Bound copies(BigInteger codePoints, BigInteger count) {
        if (count == null) {
            return new Bound(null, null);
        }
        if (count.signum() <= 0 || codePoints.signum() == 0) {
            return new Bound(BigInteger.ZERO, BigInteger.ZERO);
        }
        return joined(count.multiply(codePoints), count.subtract(BigInteger.ONE));
    }

    /** A text built of at most {@code codePoints} code points, put in canonical form: no more than
     *  {@link #GROWS} times as long, and no longer than that before it is put in it. */
    private static Bound grown(BigInteger codePoints) {
        BigInteger answer = codePoints.multiply(GROWS);
        return new Bound(answer, answer.max(codePoints));
    }

    /**
     * A text of at most {@code codePoints} padded to a width of at most {@code width} with copies
     * of a text of at most {@code pad}.
     *
     * <p>A text already that wide, or an empty pad, is answered as it is. Otherwise the width is
     * measured first, and then a fill of copies of the pad covering what is still needed, put in
     * canonical form and cut to it, is joined to the text and put in that form; where that comes
     * short of the width, one more code point is needed and the fill is built again. Neither the
     * fill nor the join is shorter than {@link #SHRINKS} times less than what it was built of, so
     * once what is needed is {@code SHRINKS * SHRINKS} times the width the join is that wide: no
     * more is ever needed than that. The copies covering it are fewer than one pad more, the fill
     * no more than {@link #GROWS} times them, the fill cut and the text no more than what is needed
     * and the width, and the join no more than {@link #GROWS} times those.
     */
    private static Bound padded(BigInteger codePoints, BigInteger width, BigInteger pad) {
        if (width == null) {
            return new Bound(null, null);
        }
        if (width.signum() <= 0 || pad.signum() == 0) {
            return new Bound(codePoints, codePoints);
        }
        BigInteger needed = SHRINKS.multiply(SHRINKS).multiply(width);
        BigInteger copied = needed.add(pad);
        BigInteger fill = GROWS.multiply(copied);
        BigInteger cutAndText = needed.add(width);
        BigInteger join = GROWS.multiply(cutAndText);
        BigInteger onTheWay = width.max(copied).max(fill).max(cutAndText).max(join);
        return new Bound(join.max(codePoints), onTheWay.max(codePoints));
    }
}
