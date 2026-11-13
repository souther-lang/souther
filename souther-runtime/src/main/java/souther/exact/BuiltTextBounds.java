package souther.exact;

import org.jspecify.annotations.Nullable;

import java.math.BigInteger;

/**
 * How long a text an operation building texts of texts comes to, and each text it builds on the
 * way, from ceilings on what it is handed: the account of what the run time's string operations
 * measure, said as numbers, so that a reader holding no more than ceilings knows whether a run of
 * one can stop for a text longer than a string holds.
 *
 * <p>Every string is in canonical form, and each operation builds its text and puts it in that
 * form, measuring what it is defined as building before it builds it. Three numbers bound what
 * putting a text in that form does to its length, and are handed in by whoever reads them off the
 * tables of the form ({@link #BuiltTextBounds}). Two texts each in the form, joined, come to no
 * more than the two and {@code seam} once put in it; no text comes to more than {@code grows}
 * times as many code points as it holds; and no text holds more than {@code shrinks} times as many
 * as it comes to, since it holds no more code points than its canonical decomposition, which is
 * the decomposition of the text in canonical form.
 *
 * <p>Each answer is a bound and claims no text reaches it. Held here, beside the arithmetic both a
 * run and the compiler reason with, so that the operations and what the compiler says of them are
 * one account.
 */
public final class BuiltTextBounds {

    private final BigInteger seam;
    private final BigInteger grows;
    private final BigInteger shrinks;

    /**
     * The account under what the canonical form does to a length.
     *
     * @param seam    the most code points joining two texts in the form adds once put in it
     * @param grows   how many times as many code points as a text holds it comes to at most
     * @param shrinks how many times as many code points as a text comes to it holds at most
     */
    public BuiltTextBounds(long seam, long grows, long shrinks) {
        if (seam < 0 || grows < 1 || shrinks < 1) {
            throw new IllegalArgumentException("a seam adds nothing below nought, and a text comes"
                    + " to and from its form at a factor of one or more");
        }
        this.seam = BigInteger.valueOf(seam);
        this.grows = BigInteger.valueOf(grows);
        this.shrinks = BigInteger.valueOf(shrinks);
    }

    /**
     * A bound on the code points of the text an operation answers, and of every text it is
     * defined as building on the way, which the answer is one of.
     *
     * @param answer   the most code points the answer holds
     * @param onTheWay the most code points any text built on the way holds, the answer among
     *                 them; null where nothing ends them
     */
    public record Bound(@Nullable BigInteger answer, @Nullable BigInteger onTheWay) {

        /** Whether every text built on the way holds no more than {@code longest} code points. */
        public boolean fitsIn(long longest) {
            return onTheWay != null && onTheWay.compareTo(BigInteger.valueOf(longest)) <= 0;
        }
    }

    /** A text of at most {@code first} followed by one of at most {@code second}, joined at one
     *  place ({@code append}). */
    public Bound appended(BigInteger first, BigInteger second) {
        return joined(first.add(second), BigInteger.ONE);
    }

    /**
     * At most {@code elements} texts of at most {@code each} code points, with a separator of at
     * most {@code separator} between each two, joined at a place on each side of each separator,
     * or at one between each two where the separator is empty ({@code join}, and {@code concat},
     * a join with the empty separator). None is the empty text.
     */
    public Bound joinedWith(BigInteger elements, BigInteger each, BigInteger separator) {
        if (elements.signum() <= 0) {
            return new Bound(BigInteger.ZERO, BigInteger.ZERO);
        }
        BigInteger between = elements.subtract(BigInteger.ONE);
        BigInteger codePoints = elements.multiply(each).add(between.multiply(separator));
        BigInteger seams = separator.signum() == 0 ? between : between.shiftLeft(1);
        return joined(codePoints, seams);
    }

    /**
     * At most {@code count} copies of a text of at most {@code codePoints}, as long as the copies
     * together and joined between each two ({@code repeat}). None, or no copy, is the empty text,
     * and a count nothing ends is no bound.
     */
    public Bound repeated(BigInteger codePoints, @Nullable BigInteger count) {
        if (count == null) {
            return new Bound(null, null);
        }
        if (count.signum() <= 0 || codePoints.signum() == 0) {
            return new Bound(BigInteger.ZERO, BigInteger.ZERO);
        }
        return joined(count.multiply(codePoints), count.subtract(BigInteger.ONE));
    }

    /** The code points of a text of at most {@code codePoints} in another order, put in
     *  canonical form whole ({@code reverse}). */
    public Bound reversed(BigInteger codePoints) {
        return grown(codePoints);
    }

    /**
     * A text of at most {@code codePoints} with each occurrence of a target of one code point or
     * more put in place of by a text of at most {@code replacement}, put in canonical form whole
     * ({@code replace}). Each occurrence takes a code point or more out and puts that many of the
     * replacement's in, so the text before it is put in the form is no longer than the text times
     * the longer of one and the replacement. An empty target answers the text.
     */
    public Bound replaced(BigInteger codePoints, BigInteger replacement) {
        return grown(codePoints.multiply(replacement.max(BigInteger.ONE)));
    }

    /**
     * A text of at most {@code codePoints} padded to a width of at most {@code width} with copies
     * of a text of at most {@code pad} ({@code padLeft}, {@code padRight}).
     *
     * <p>A text already that wide, or an empty pad, is answered as it is. Otherwise the width is
     * measured first, and then a fill of copies of the pad covering what is still needed, put in
     * canonical form and cut to it, is joined to the text and put in that form; where that comes
     * short of the width, one more code point is needed and the fill is built again. Neither the
     * fill nor the join is shorter than {@code shrinks} times less than what it was built of, so
     * once what is needed is {@code shrinks} squared times the width the join is that wide: no more
     * is ever needed than that. The copies covering it are fewer than one pad more, the fill no
     * more than {@code grows} times them, the fill cut and the text no more than what is needed
     * and the width, and the join no more than {@code grows} times those. A width nothing ends is
     * no bound.
     */
    public Bound padded(BigInteger codePoints, @Nullable BigInteger width, BigInteger pad) {
        if (width == null) {
            return new Bound(null, null);
        }
        if (width.signum() <= 0 || pad.signum() == 0) {
            return new Bound(codePoints, codePoints);
        }
        BigInteger needed = shrinks.multiply(shrinks).multiply(width);
        BigInteger copied = needed.add(pad);
        BigInteger fill = grows.multiply(copied);
        BigInteger cutAndText = needed.add(width);
        BigInteger join = grows.multiply(cutAndText);
        BigInteger onTheWay = width.max(copied).max(fill).max(cutAndText).max(join);
        return new Bound(join.max(codePoints), onTheWay.max(codePoints));
    }

    /** Texts {@code codePoints} long together, each in canonical form, joined at {@code seams}
     *  places: no longer than they are together before it is put in the form, and each place
     *  adds no more than a seam does. */
    private Bound joined(BigInteger codePoints, BigInteger seams) {
        BigInteger answer = codePoints.add(seams.max(BigInteger.ZERO).multiply(seam));
        return new Bound(answer, answer);
    }

    /** A text built of at most {@code codePoints} code points, put in canonical form: no more than
     *  {@code grows} times as long, and no longer than that before it is put in it. */
    private Bound grown(BigInteger codePoints) {
        BigInteger answer = codePoints.multiply(grows);
        return new Bound(answer, answer.max(codePoints));
    }
}
