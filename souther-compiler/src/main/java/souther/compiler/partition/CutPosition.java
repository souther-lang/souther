package souther.compiler.partition;

import souther.compiler.numeric.Count;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.Towards;

import java.math.BigDecimal;

/**
 * Where a rule's line falls on the quantity it cuts, in that quantity's own units.
 *
 * <p>Held as what the rule wrote and how much of the quantity it wrote it in, rather than as the
 * number that comes of dividing one by the other. {@code 3 * d <= 1} puts its line at a third, and
 * the pair says where that is in the numbers the rule was written with — which is what a report
 * names the class by, and what {@link Seam#asARuleAbout} writes back out.
 *
 * <p>The exactness no longer rests on the pair. A level is an exact ratio wherever the quantity
 * counts to one, so dividing here loses nothing; what the pair keeps is the rule's own units, and
 * {@code 3 * d <= 1} and {@code d <= 1 / 3} draw one line and are two ways of writing it.
 *
 * @param written what the rule compared against, on the form it was written in
 * @param per     how much of the quantity that form is, which is never zero and never negative
 */
public record CutPosition(Level written, ExactRatio per) implements Comparable<CutPosition> {

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
        return new CutPosition(written, ExactRatio.ONE);
    }

    /**
     * Where this line falls, as the exact number it is — or null on an order with no numbers.
     *
     * <p>What the rule wrote over how much of the quantity it wrote, which is exact: both are
     * ratios and a ratio divided by a ratio is one. A third comes back a third, and the reader that
     * needs it as a value of something asks {@link #asAValueOf}.
     */
    public ExactRatio exactly() {
        ExactRatio at = numberOf(written);
        return at == null ? null : at.dividedBy(per);
    }

    /**
     * What makes two positions one position: where the line falls, and not the units it was said in.
     *
     * <p>A third and two sixths are one place, which an exact ratio in lowest terms already says.
     *
     * <p>An order with no numbers answers with its own value. Nothing scales such a quantity — a
     * rule holding two strings apart writes the whole of it — so there is no fraction to reduce.
     */
    public String key() {
        ExactRatio at = exactly();
        if (at == null) {
            return written.key();
        }
        ExactRatio.Fraction fraction = at.asFraction();
        return fraction.numerator() + "/" + fraction.denominator();
    }

    /**
     * This line written the one way {@link #key()} names it: the fraction reduced, and the place
     * spelled as the order spells it.
     *
     * <p>So that a value holding a position and compared as a value answers what {@link #key()}
     * would. A third and two sixths come back the same, and so do a line at {@code 0} and one at
     * {@code 0.00}.
     *
     * <p>An order with no numbers has no fraction to reduce, and its place is its own value.
     */
    public CutPosition canonical() {
        ExactRatio at = exactly();
        if (at == null) {
            return new CutPosition(written.canonical(), per);
        }
        return new CutPosition(reduced(written, at.numeratorAsRatio()), at.denominatorAsRatio());
    }

    /**
     * The same line on the quantity read the other way round.
     *
     * <p>The place negates and the share does not. How much of the quantity the rule wrote is a
     * fact about the rule's form and says nothing about which way the quantity is measured, so a
     * line at a third of {@code a - b} is at minus a third of {@code b - a} and is still a third of
     * whatever was written.
     */
    public CutPosition reflected() {
        return new CutPosition(written.negated(), per);
    }

    /**
     * The reduced numerator, put back on whatever order the line was written on.
     *
     * <p>A whole number, so a carrier's order has a count at it wherever it has counts at all.
     */
    private static Level reduced(Level written, ExactRatio to) {
        return switch (written) {
            case Level.OfTheQuantity _ -> new Level.OfTheQuantity(to);
            case Level.OnACarrier on -> Level.OnACarrier.held(on.of(), to);
        };
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
        return per.equals(ExactRatio.ONE) ? written : null;
    }

    /**
     * The same line, said in units {@code k} times smaller.
     *
     * <p>A line at a place is at {@code k} times that number where the unit is a {@code k}th of the
     * one it was said in: what a quantity's own level is, the form that wrote {@code k} of it calls
     * {@code k} times as much.
     */
    public CutPosition times(ExactRatio k) {
        ExactRatio at = numberOf(written);
        if (at == null || k.equals(ExactRatio.ONE)) {
            return this;
        }
        // Scaled by exactly the share the rule wrote, the share divides out: the line is at the
        // number the rule carried, in the units the rule carried it in. Left in, the position was
        // right and the reading of it was not — a line the form does stand at went on answering
        // that the quantity has no value there, and the run above it could not say where it starts.
        return k.equals(per)
                ? new CutPosition(new Level.OfTheQuantity(at), ExactRatio.ONE)
                : new CutPosition(new Level.OfTheQuantity(at.times(k)), per);
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
     * <p>The carrier edge for a line: an exact place becomes a value here or is none
     * ({@link Count#at}). A third is no count at all, and a count the carrier's own values step past
     * is no value of it either.
     */
    public souther.compiler.numeric.Place asAValueOf(souther.compiler.check.Carrier carrier) {
        if (carrier == null) {
            return null;
        }
        ExactRatio at = exactly();
        // An order with no numbers is never scaled — a rule holding two strings apart writes the
        // whole of what it cuts — so its line is its own value and there is nothing to divide.
        if (at == null) {
            return per.equals(ExactRatio.ONE) ? written.asAPlace() : null;
        }
        Count count = Count.at(at);
        return count == null ? null : carrier.onTheGrid(count);
    }

    /**
     * Whether a value of the quantity is below, at or above where this line falls.
     *
     * <p>Both are exact, so the comparison is exact and a line at a place no value stands at is
     * compared without being written down: a fifth is under a third and a half is over it.
     */
    public int compare(Level value) {
        ExactRatio line = exactly();
        ExactRatio of = numberOf(value);
        // An order with no numbers is never scaled — a rule holding two strings apart writes the
        // whole of what it cuts — so the two are places of one order and compare as they stand.
        if (line == null || of == null) {
            return value.asAPlace().compareTo(written.asAPlace());
        }
        return of.compareTo(line);
    }

    /**
     * Whether this line falls below, at or above where {@code other} does.
     *
     * <p>Exact, for the reason the rest of this is: a line at a third and one at two sixths fall in
     * one place, and neither of them is a number this language can write out to compare.
     */
    @Override
    public int compareTo(CutPosition other) {
        ExactRatio mine = exactly();
        ExactRatio theirs = other.exactly();
        if (mine == null || theirs == null) {
            return written.asAPlace().compareTo(other.written.asAPlace());
        }
        return mine.compareTo(theirs);
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
     * <p>The denominator is how much of the quantity and the numerator is what it comes to, which
     * is what a ratio in lowest terms already holds.
     *
     * @return where the line falls, or null on an order with no numbers
     */
    public ExactRatio asARule() {
        return exactly();
    }

    /**
     * The same, asked of a number the quantity comes to.
     *
     * <p>For a reader holding what a form added up to at one row rather than a level of an order:
     * the two are the same number and only one of them is a value of anything.
     */
    public int compare(ExactRatio value) {
        ExactRatio line = exactly();
        if (line == null) {
            throw new IllegalStateException(
                    "an order with no numbers was compared against one: " + written);
        }
        return value.compareTo(line);
    }

    /** The same, asked of a place of the order this line falls on. */
    public int compare(souther.compiler.numeric.Place at) {
        ExactRatio line = exactly();
        // The same two answers as above, and the second for the same reason: an order with no
        // numbers is never scaled, so its places compare as they stand — and two carriers' places
        // brought together say so themselves rather than arriving here as a null.
        return at instanceof Count count && line != null
                ? count.exactly().compareTo(line)
                : at.compareTo(written.asAPlace());
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
        ExactRatio line = exactly();
        if (line == null) {
            return null;
        }
        BigDecimal past = line.asDecimal(towards == Towards.ABOVE
                ? java.math.RoundingMode.CEILING : java.math.RoundingMode.FLOOR, digits);
        // Strictly past, which rounding gives only where the line is not itself a number of that
        // many digits. A line the quantity does stand at rounds to itself, and the run beyond it
        // does not hold it.
        if (ExactRatio.of(past).compareTo(line) == 0) {
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
     * <p>Exact, because both lines are: the digits needed are what it takes for a tenth of that many
     * to fit inside the distance. Zero where the two are the same place, which no run has.
     */
    public int digitsToTellApartFrom(CutPosition other) {
        ExactRatio mine = exactly();
        ExactRatio theirs = other.exactly();
        if (mine == null || theirs == null) {
            return 0;
        }
        ExactRatio apart = mine.minus(theirs).abs();
        if (apart.isZero()) {
            return 0;
        }
        return ExactRatio.ONE.dividedBy(apart).floor().toString().length() + 1;
    }

    private static ExactRatio numberOf(Level level) {
        return level.asANumber();
    }
}
