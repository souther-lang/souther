package souther.compiler.partition;

import souther.compiler.numeric.Towards;

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
     * This line as a value of the quantity, or null where it is not one.
     *
     * <p>The one way to get a level out of a position, and it answers null exactly where the rule
     * wrote a multiple of the quantity and the line does not land on one of its values — a third is
     * where {@code 3 * d <= 1} cuts and is no decimal this language writes. Every reader that took
     * the level the rule was written with for a value of the quantity had it wrong by the multiple:
     * a run read its own end against it, a line was asked whether it keeps a value it is not at, and
     * a search was handed a level of one order to look for on another.
     */
    public Level asALevelOfTheQuantity() {
        return per.compareTo(BigDecimal.ONE) == 0 ? written : null;
    }

    /**
     * The same line, said in units {@code k} times smaller.
     *
     * <p>A line at a place is at {@code k} times that number where the unit is a {@code k}th of the
     * one it was said in: what a quantity's own level is, the form that wrote {@code k} of it calls
     * {@code k} times as much. Multiplied rather than re-divided, so a line at a place no value
     * stands at travels between the two orders exactly.
     */
    public CutPosition times(BigDecimal k) {
        BigDecimal at = numberOf(written);
        if (at == null || k.compareTo(BigDecimal.ONE) == 0) {
            return this;
        }
        // Scaled by exactly the share the rule wrote, the share divides out: the line is at the
        // number the rule carried, in the units the rule carried it in. Left in, the position was
        // right and the reading of it was not — a line the form does stand at went on answering
        // that the quantity has no value there, and the run above it could not say where it starts.
        return k.compareTo(per) == 0
                ? new CutPosition(new Level.ACount(new Count(at)), BigDecimal.ONE)
                : new CutPosition(new Level.ACount(new Count(at.multiply(k))), per);
    }

    /**
     * This line as a value of the position the quantity is a multiple of, or null where the
     * position holds none there.
     *
     * <p>Apart from {@link #asALevelOfTheQuantity}, which asks about the order the rule wrote the
     * line on. This asks about the position underneath it, and the two differ exactly where a rule
     * wrote a multiple: {@code 2 * n == 8} names four and {@code 2 * n == 9} names nothing, and both
     * are lines of an order whose values are the even numbers.
     *
     * <p>Divided here and nowhere else, because here is the one question that needs the quotient to
     * be a value rather than a place: a rule that names a value names one the position holds or
     * names none. A quotient that does not end is not one, and neither is one the carrier's own
     * values step past.
     */
    public souther.compiler.numeric.Place asAValueOf(souther.compiler.check.Carrier carrier) {
        BigDecimal at = numberOf(written);
        if (carrier == null) {
            return null;
        }
        // An order with no numbers is never scaled — a rule holding two strings apart writes the
        // whole of what it cuts — so its line is its own value and there is nothing to divide.
        if (at == null) {
            return per.compareTo(BigDecimal.ONE) == 0 ? placeOf(written) : null;
        }
        BigDecimal quotient;
        try {
            quotient = at.divide(per);
        } catch (ArithmeticException _) {
            return null;   // a third is no value of anything this language writes
        }
        return carrier.onTheGrid(new Count(quotient));
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

    /**
     * Whether this line falls below, at or above where {@code other} does.
     *
     * <p>Cross-multiplied rather than divided, for the reason the rest of this is: a line at a third
     * and one at two sixths fall in one place, and neither of them is a number this language can
     * write out to compare.
     */
    public int compareTo(CutPosition other) {
        BigDecimal mine = numberOf(written);
        BigDecimal theirs = numberOf(other.written);
        if (mine == null || theirs == null) {
            return placeOf(written).compareTo(placeOf(other.written));
        }
        return mine.multiply(other.per).compareTo(theirs.multiply(per));
    }

    /**
     * This line as a rule an author could have written it: how much of the quantity, and what it
     * comes to.
     *
     * <p>Reduced, so that the two rules that draw one line write it one way — a third and two
     * sixths both come back as {@code 3} and {@code 1}. What names a class where the position holds
     * no value at the line: {@code 3 * d <= 1} says exactly where the values part and says it in
     * numbers this language has, which dividing them out would not.
     *
     * @return the multiple and the number it comes to, or null on an order with no numbers
     */
    public BigDecimal[] asARule() {
        BigDecimal at = numberOf(written);
        if (at == null) {
            return null;
        }
        int scale = Math.max(Math.max(at.scale(), per.scale()), 0);
        BigInteger top = at.setScale(scale).unscaledValue();
        BigInteger bottom = per.setScale(scale).unscaledValue();
        BigInteger common = top.gcd(bottom);
        if (common.signum() != 0) {
            top = top.divide(common);
            bottom = bottom.divide(common);
        }
        return new BigDecimal[] {new BigDecimal(bottom), new BigDecimal(top)};
    }

    /** The same, asked of a place of the order this line falls on. */
    public int compare(souther.compiler.numeric.Place at) {
        BigDecimal line = numberOf(written);
        // The same two answers as above, and the second for the same reason: an order with no
        // numbers is never scaled, so its places compare as they stand — and two carriers' places
        // brought together say so themselves rather than arriving here as a null.
        return at instanceof Count count && line != null
                ? count.at().multiply(per).compareTo(line)
                : at.compareTo(placeOf(written));
    }

    /**
     * A whole number of the quantity's units on one side of this line, for a search to start from.
     *
     * <p>Where the line falls between two of them, the whole number that way is past it — a third
     * rounded up is one and rounded down is nothing, and both are on the side they were rounded to.
     * A bound and never the answer: what is at a run is the run's to say, and this is only where to
     * begin looking.
     *
     * <p>Null on an order with no numbers, which is never scaled and so never needs this.
     */
    public souther.compiler.numeric.Place justBeyond(Towards towards, int digits) {
        BigDecimal at = numberOf(written);
        if (at == null) {
            return null;
        }
        BigDecimal past = at.divide(per, digits, towards == Towards.ABOVE
                ? java.math.RoundingMode.CEILING : java.math.RoundingMode.FLOOR);
        // Strictly past, which rounding gives only where the line is not itself a number of that
        // many digits. A line the quantity does stand at rounds to itself, and the run beyond it
        // does not hold it.
        if (past.multiply(per).compareTo(at) == 0) {
            BigDecimal step = BigDecimal.ONE.movePointLeft(digits);
            past = towards == Towards.ABOVE ? past.add(step) : past.subtract(step);
        }
        return new Count(past);
    }

    /**
     * How many digits it takes to name a number between this line and {@code other}.
     *
     * <p>Worked out from the two places and not guessed. Two lines are a definite distance apart —
     * a third and a third and a hundred-billionth are — and a decimal lies between any two of them;
     * how many digits it needs is what that distance says. Tried at a fixed handful of scales
     * instead, a run narrower than the widest of them was reported as one no value of the position
     * lies inside, which is a false answer rather than a search that gave up.
     *
     * <p>Exact, by comparing the two as fractions: the difference of {@code a/b} and {@code c/d} is
     * {@code (ad - cb) / bd}, and the digits needed are what it takes for a tenth of that many to
     * fit inside it. Zero where the two are the same place, which no run has.
     */
    public int digitsToTellApartFrom(CutPosition other) {
        BigDecimal mine = numberOf(written);
        BigDecimal theirs = numberOf(other.written);
        if (mine == null || theirs == null) {
            return 0;
        }
        int scale = Math.max(Math.max(mine.scale(), per.scale()),
                Math.max(theirs.scale(), other.per.scale()));
        scale = Math.max(scale, 0);
        BigInteger a = mine.setScale(scale).unscaledValue();
        BigInteger b = per.setScale(scale).unscaledValue();
        BigInteger c = theirs.setScale(scale).unscaledValue();
        BigInteger d = other.per.setScale(scale).unscaledValue();
        BigInteger apart = a.multiply(d).subtract(c.multiply(b)).abs();
        if (apart.signum() == 0) {
            return 0;
        }
        BigInteger over = b.multiply(d).abs();
        return over.divide(apart).toString().length() + 1;
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
