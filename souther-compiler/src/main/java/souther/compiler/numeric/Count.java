package souther.compiler.numeric;

import java.math.BigDecimal;

/**
 * The number a value counts to on its carrier's order, and never a number a model writes.
 *
 * <p>The interval algebra holds one number per position, and a type takes part in it by counting to
 * that number: a date counts days from an epoch, a date-time counts seconds, an {@code Int} counts
 * itself. Those counts and a model's own numbers were the same Java type, so the count a carrier is
 * made of could be written wherever a value of the position belonged and nothing objected — a
 * boundary row at a date-time carried the epoch second as an {@code Int}, and the report said the
 * search had refused every value rather than that the value made no sense.
 *
 * <p>Two of the four carriers went wrong here before this existed, in different directions: a day
 * count read by two readers that disagreed about it, and a second count reaching a row. Neither is a
 * mistake anybody makes twice on purpose; both are what a shared representation invites.
 *
 * <p>So the separation is the type and not a naming convention. What it buys is one thing: a count
 * cannot be passed where a value belongs, and a value cannot be passed where a count belongs, without
 * the build stopping. It deliberately does not distinguish one carrier's counts from another's — a
 * day count and a second count are both {@code Count} — because the confusion that has actually
 * happened is between the algebra's coordinates and the model's numbers, and a type per carrier would
 * be four more names to keep in step for a confusion nothing has made yet.
 *
 * <p>Which carrier a count is on is carried by whatever holds the count, and the conversion both ways
 * lives on {@link souther.compiler.numeric.Granularity the carrier} rather than here. Nothing in this
 * type knows what a date is.
 */
public record Count(BigDecimal at) implements Place {

    public static final Count ZERO = new Count(BigDecimal.ZERO);

    public Count {
        if (at == null) {
            throw new IllegalArgumentException("a count is a number; use null for no count");
        }
    }

    public static Count of(BigDecimal at) {
        return at == null ? null : new Count(at);
    }

    /**
     * The count a place is.
     *
     * <p>The one narrowing, so that a reader which reached arithmetic on a carrier that has none is
     * one line to find rather than a cast repeated wherever a number was wanted. Never reachable
     * from a model: every caller has already established which carrier it is on.
     */
    public static Count number(Place at) {
        if (!(at instanceof Count count)) {
            throw new IllegalStateException("a carrier with no counts was asked for a number: " + at);
        }
        return count;
    }

    public static Count of(long at) {
        return new Count(BigDecimal.valueOf(at));
    }

    /**
     * The count an exact number is, or null where no count is it.
     *
     * <p><b>The edge exact reasoning becomes a value on a carrier at, for a reader asking whether
     * it does.</b> Every carrier's order is counted in decimals and the algebra above it is not: a
     * form weighed by a third puts a level a third along, and no count is a third. Null says that
     * and never that this could not work it out — {@link ExactRatio#asWrittenDecimal} is exact, so a
     * caller is told which of the two it has rather than handed a number that cannot be asked.
     *
     * <p>Whether the carrier holds the count it is a separate question and the carrier's own
     * ({@link Granularity}): a third is no count anywhere, and a half is a count no whole-numbered
     * order stands at.
     *
     * <p>For a caller that has established there is one, {@link #number(ExactRatio)}. The two are
     * the same edge asked by two kinds of reader, and which of them a caller is decides what a
     * missing count means — so it is said in the signature rather than worked out again at each
     * call.
     */
    public static Count at(ExactRatio number) {
        BigDecimal written = number.asWrittenDecimal();
        return written == null ? null : new Count(written);
    }

    /**
     * The count an exact number is, where the caller has established that one is.
     *
     * <p>The same narrowing {@link #number(Place)} is, asked of the other side of the edge: there,
     * a caller holding a place has established which carrier it is on; here, a caller holding an
     * exact number has established that a carrier's order counts to it. A level the written form
     * attains is a whole multiple of what that form wrote, so reading it back in the quantity's own
     * units lands on a number the order has — and a reader that has that in hand has no use for an
     * absence.
     *
     * <p>Refused rather than answered with a level of the exact side. The two are values of
     * different spaces, and one handed over where the other was asked for travels until something
     * far from here asks it for a place. What reaches this is this compiler having broken the
     * premise the caller stands on, so it is said where the premise is.
     */
    public static Count number(ExactRatio at) {
        Count count = at(at);
        if (count == null) {
            throw new IllegalStateException(
                    "no count on any carrier's order is this number: " + at);
        }
        return count;
    }

    /** This count as the exact number it is, which never loses anything: every finite decimal is a
     *  ratio. */
    public ExactRatio exactly() {
        return ExactRatio.of(at);
    }

    /**
     * The count {@code steps} further along the order.
     *
     * <p>Whole steps only. What one step means is the carrier's — a day for a date, a second for a
     * date-time — and every caller stepping a count is stepping over a carrier that has a step at
     * all, which {@link Granularity} is what says.
     */
    public Count plus(long steps) {
        return new Count(at.add(BigDecimal.valueOf(steps)));
    }

    public Count minus(long steps) {
        return plus(-steps);
    }

    /**
     * The counts added, and the difference of two counts.
     *
     * <p>Both are counts, because the domain that proves what a position holds reasons over
     * differences: {@code a - b <= 0} bounds one position through another, and what it carries either
     * side of the comparison is a coordinate. Scaling is there for the same reason — a run is
     * stepped by so many of its steps — and the factor is a plain number rather than a count, since
     * how many steps is no place on any order.
     *
     * <p>Not what weighs a count by a coefficient. What a form comes to is on no carrier's order at
     * all and need not be a number any carrier counts to, so that arithmetic is
     * {@link ExactRatio}'s, reached through {@link #exactly}.
     */
    public Count plus(Count other) {
        return new Count(at.add(other.at));
    }

    public Count minus(Count other) {
        return new Count(at.subtract(other.at));
    }

    public Count times(BigDecimal factor) {
        return new Count(at.multiply(factor));
    }

    public Count negate() {
        return new Count(at.negate());
    }

    /** This count moved onto a whole one, which is what a discrete carrier's order is made of. */
    public Count rounded(java.math.RoundingMode towards) {
        return new Count(at.setScale(0, towards));
    }

    /**
     * The count halfway between this and {@code other}, exact where the halves land on the order and
     * rounded towards this one where they do not.
     *
     * <p>Rounded rather than refused, because a caller asking for the middle of two counts is asking
     * for one of them to stand for what lies between, and half a step is not a place on any carrier's
     * order. Where the carrier has no step at all the halves are exact and nothing rounds.
     */
    public Count halfwayTo(Count other, Granularity spacing) {
        BigDecimal span = other.at.subtract(at);
        return new Count(at.add(spacing == Granularity.DISCRETE
                ? span.divide(BigDecimal.valueOf(2), 0, java.math.RoundingMode.DOWN)
                : span.divide(BigDecimal.valueOf(2))));
    }

    /** Whether this counts to a place on an order that steps: a count with a fraction in it is
     * between two of a discrete carrier's values and is none of them. */
    public boolean whole() {
        return at.stripTrailingZeros().scale() <= 0;
    }

    public int signum() {
        return at.signum();
    }

    /**
     * The order, which is the numbers' own.
     *
     * <p>Against another count. A place on some other carrier's order is not below or above this
     * one, and the algebra never brings two together — so the mistake is said rather than answered
     * with whichever of the two happened to be a number.
     */
    @Override
    public int compareTo(Place other) {
        if (!(other instanceof Count count)) {
            throw Place.notOneOrder(this, other);
        }
        return at.compareTo(count.at);
    }

    /**
     * What makes two counts one line: the number, and not how many places it was written to.
     *
     * <p>Built from the two parts a decimal is held as once the trailing zeros are off it, which is
     * one pair per number — so two counts with this name are one count, and the name costs what
     * those parts cost. Spelled out instead, a bound at a decimal written at a wide scale is a
     * character per place: the value is a single digit and a scale, and naming it wrote every place
     * between them. What a reader sees is {@link #spelled}, and no line in the algebra is named by
     * asking for that.
     *
     * <p>Not {@link #equals}, which a record derives from {@link BigDecimal#equals} and which says
     * {@code 0.00} and {@code 0} are two places. The derived equality is left alone rather than
     * overridden so that a map keyed on counts keeps saying what a map keyed on {@code BigDecimal}
     * said; every comparison in the algebra goes through {@link #compareTo} or {@link Place#sameAs}.
     */
    @Override
    public String key() {
        BigDecimal canonical = at.stripTrailingZeros();
        return canonical.unscaledValue() + ";" + canonical.scale();
    }

    /** This count as the number it is. The trailing zeros are gone, so {@code 0.00} and {@code 0}
     *  are written one way — the same number {@link #key()} names, said in digits. */
    @Override
    public String spelled() {
        return at.stripTrailingZeros().toPlainString();
    }

    /** The same count with the trailing zeros gone, which is the number {@link #key()} names. */
    @Override
    public Count canonical() {
        return new Count(at.stripTrailingZeros());
    }

    @Override
    public String toString() {
        return spelled();
    }
}
