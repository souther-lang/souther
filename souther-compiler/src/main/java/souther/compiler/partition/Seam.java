package souther.compiler.partition;

/**
 * Where a rule parts one quantity's values: the last value on one side and the first on the other.
 *
 * <p><b>Not the number the rule was written with.</b> {@code n <= 4} and {@code n < 5} are two
 * comparisons and one division of the whole numbers, and a partition built on the two thresholds has
 * a class between them holding nothing any row could write. What a rule does to a quantity is part
 * its values, and that is what this records.
 *
 * <p>Which makes it a question about the order and never about the spelling. The same two operators
 * over a carrier whose values fill answer the other way — no decimal lies between {@code <= 0.5} and
 * {@code < 0.5}, and the two rules put {@code 0.5} itself on opposite sides — so this is derived from
 * the {@link LevelSpace} rather than from the comparison.
 *
 * @param at    where the rule's line falls, which the quantity need not take a value at. Carried
 *              because it is the only thing that says where the values part when neither side names
 *              a value: {@code 3 * d <= 1} and {@code 3 * d <= 2} both leave no last value below
 *              and no first value above, and they are two divisions
 * @param below the last value the quantity takes on the lower side, or null where the order names
 *              none there. Null is "no last value" and never "nothing below": a decimal below a line
 *              it does not keep has every value up to it and no greatest one
 * @param above the first value it takes on the upper side, or null on the same reading
 */
public record Seam(CutPosition at, Level below, Level above) {

    /**
     * Where {@code cut} parts the values of {@code space}, given which side the cut's own value
     * belongs to.
     *
     * <p>The cut need not be a value the quantity takes. {@code 2 * a <= 9} cuts a quantity whose
     * values are the even numbers, and the two sides part between eight and ten; asked of the
     * threshold alone, a reader would put a row at nine and call the rule exercised.
     *
     * @param belongsTo the side the cut's own value falls on where the quantity takes it, which is
     *                  what the operator says and the order does not
     */
    public static Seam of(LevelSpace space, Level cut, Towards belongsTo) {
        return of(space, cut, belongsTo, null);
    }

    /**
     * The same, where the rule wrote a multiple of the quantity rather than the quantity itself.
     *
     * <p>The two sides are found on the order the rule was written on — that is the order that knows
     * which levels the written form attains — and then read back in the quantity's own units. Exact
     * both ways: a level the written form attains is a multiple of what it wrote, so nothing rounds,
     * and where it attains no level there is nothing to read back.
     */
    public static Seam of(LevelSpace space, Level cut, Towards belongsTo, Scale into) {
        boolean attains = space.attainable(cut);
        Level below = attains && belongsTo == Towards.BELOW ? cut
                : beside(space, cut, Towards.BELOW);
        Level above = attains && belongsTo == Towards.ABOVE ? cut
                : beside(space, cut, Towards.ABOVE);
        return new Seam(
                new CutPosition(cut, into == null ? java.math.BigDecimal.ONE : into.per()),
                inUnitsOf(below, into), inUnitsOf(above, into));
    }

    /**
     * One of the quantity's own values, from a level of the form that wrote a multiple of it.
     *
     * <p>Written back on the carrier the quantity is ordered by, where it has one. A level is
     * compared by the number under it and a report spells it by the carrier over it, so a value that
     * kept the form's shape would read the same and write differently — which is the split that had
     * a day count printed as the number a model wrote.
     */
    private static Level inUnitsOf(Level level, Scale into) {
        // A rule that wrote the whole of the quantity wrote it in the quantity's own units, so
        // there is nothing to read back — including where the quantity has no numbers at all. A
        // rule holds two strings apart and writes the whole of what it cuts, and asking such a
        // level for its number is what {@link Level#asACount} exists to refuse.
        if (level == null || into == null || into.per().compareTo(java.math.BigDecimal.ONE) == 0) {
            return level;
        }
        java.math.BigDecimal at = level.asACount().at().divide(into.per());
        return into.onto() == null ? new Level.ACount(new souther.compiler.numeric.Count(at))
                : new Level.OnACarrier(into.onto(), new souther.compiler.numeric.Count(at));
    }

    /**
     * What makes two seams one seam: where the values part, and not how either number was written.
     *
     * <p>{@code invariant value >= 0.00} and {@code guard x <= 0m} part a carrier's values in one
     * place. Keyed by their spelling they are two, and then a position has two classes both holding
     * zero — the same rule {@link Level#key()} states, asked of a division rather than of a value.
     *
     * <p>Both sides, because either may be the one that differs: a seam with a last value below and
     * no first value above is not the seam with the opposite, and over a carrier whose values fill
     * those are exactly what {@code <=} and {@code <} come to at one number.
     *
     * <p>And the level the rule was written against where neither side names a value, because then
     * it is the only thing left that says where the values part. Which is not a second key: a
     * quantity that names a value on either side is divided by which values those are, and one that
     * names none on either is divided at a place nothing stands at. The written level is read here
     * and nowhere else, so two spellings of one division stay one wherever the quantity has values
     * to be told apart by.
     */
    public String key() {
        if (below == null && above == null) {
            return "@" + at.key();
        }
        return (below == null ? "" : below.key()) + "|" + (above == null ? "" : above.key());
    }

    /**
     * How a level written in one form's terms reads as a level of the quantity it is a multiple of.
     *
     * @param per  how much of the quantity the form wrote ({@link QuantityKey#per})
     * @param onto the carrier the quantity's own values are ordered by, or null where it has none
     */
    public record Scale(java.math.BigDecimal per, souther.compiler.check.Carrier onto) {}

    /**
     * One value of the quantity that this seam is at, for a reader putting several of them in the
     * order their values are in.
     *
     * <p>Either end will do and neither is the seam: the two are one step apart on an order that
     * steps, and where only one of them exists it is the one that says where the values part.
     */
    Level somewhere() {
        return below != null ? below : above != null ? above : at.written();
    }

    /**
     * The nearest value the quantity takes on one side of the cut.
     *
     * <p>The value beside the cut where the quantity takes the cut, and the first value it does take
     * otherwise. Two questions the order answers apart: {@code 2 * a <= 9} has no neighbour of nine
     * to ask for, because nine is not a level it stands at, and the level it stands at below nine is
     * not one step from anything.
     */
    private static Level beside(LevelSpace space, Level cut, Towards towards) {
        return (space.attainable(cut) ? space.neighbour(cut, towards)
                : space.nearestAtOrBeyond(cut, towards)).orElse(null);
    }
}
