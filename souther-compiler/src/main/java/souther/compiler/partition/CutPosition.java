package souther.compiler.partition;

import souther.compiler.numeric.Count;

import java.math.BigDecimal;
import java.math.BigInteger;

/**
 * Where a rule's line falls on the quantity it cuts, in that quantity's own units.
 *
 * <p>Held as what the rule wrote and how much of the quantity it wrote it in, rather than as the
 * number that comes of dividing one by the other. {@code 3 * d <= 1} puts its line at a third, and
 * no decimal this language writes is a third — divided out, the position would have to be rounded to
 * a number the line is not at, and a report would ask for a row on the wrong side of it.
 *
 * <p>Which costs nothing, because nothing needs the quotient. Two positions are the same position
 * when the fractions reduce alike, and that is settled by multiplying rather than dividing.
 *
 * @param written what the rule compared against, on the form it was written in
 * @param per     how much of the quantity that form is, which is never zero and never negative
 */
public record CutPosition(Level written, BigDecimal per) {

    public CutPosition {
        if (written == null || per == null || per.signum() <= 0) {
            throw new IllegalArgumentException(
                    "a position is a level and a positive share of the quantity: " + written + " / "
                            + per);
        }
    }

    /** A line at a level of the quantity itself, which is what a rule that wrote the whole of it
     *  draws. */
    public static CutPosition at(Level written) {
        return new CutPosition(written, BigDecimal.ONE);
    }

    /**
     * What makes two positions one position: where the line falls, and not the units it was said in.
     *
     * <p>A third and two sixths are one place. Reduced rather than divided, so that a place no value
     * of the quantity stands at is still named exactly — which is the case this exists for, since a
     * position with a value either side of it is told from its neighbours by those values and never
     * reaches here ({@link Seam#key()}).
     *
     * <p>An order with no numbers answers with its own value. Nothing scales such a quantity — a
     * rule holding two strings apart writes the whole of it — so there is no fraction to reduce.
     */
    public String key() {
        BigDecimal at = numberOf(written);
        if (at == null) {
            return written.key();
        }
        int scale = Math.max(Math.max(at.scale(), per.scale()), 0);
        BigInteger top = at.setScale(scale).unscaledValue();
        BigInteger bottom = per.setScale(scale).unscaledValue();
        BigInteger common = top.gcd(bottom);
        if (common.signum() != 0) {
            top = top.divide(common);
            bottom = bottom.divide(common);
        }
        return top + "/" + bottom;
    }

    /**
     * Whether a value of the quantity is below, at or above where this line falls.
     *
     * <p>Asked by multiplying rather than by dividing, which is what lets a line at a place no value
     * stands at be compared exactly: a fifth is under a third and a half is over it, and neither
     * comparison needs a third to be written down.
     *
     * <p>The value is one of the quantity's own and the line was written in a multiple of it, so
     * bringing them together is what this is for. A reader that compared the two as they stand put
     * every decimal up to one below a line at a third.
     */
    public int compare(Level value) {
        BigDecimal at = numberOf(written);
        BigDecimal of = numberOf(value);
        // An order with no numbers is never scaled — a rule holding two strings apart writes the
        // whole of what it cuts — so the two are places of one order and compare as they stand.
        if (at == null || of == null) {
            return placeOf(value).compareTo(placeOf(written));
        }
        return of.multiply(per).compareTo(at);
    }

    private static souther.compiler.numeric.Place placeOf(Level level) {
        return switch (level) {
            case Level.ACount count -> count.at();
            case Level.OnACarrier on -> on.at();
        };
    }

    private static BigDecimal numberOf(Level level) {
        return switch (level) {
            case Level.ACount count -> count.at().at();
            case Level.OnACarrier on -> on.at() instanceof Count count ? count.at() : null;
        };
    }
}
