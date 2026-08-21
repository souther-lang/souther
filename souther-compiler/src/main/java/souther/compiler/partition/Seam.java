package souther.compiler.partition;

import souther.compiler.numeric.Towards;

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
     * The same seam, said in units {@code k} times smaller.
     *
     * <p>What one quantity's lines come to for a rule that wrote a multiple of it: the arrangement
     * is held in the quantity's own units, because that is the only order every rule about it is
     * on, and each rule reads its rows through the form it was written as. Nothing here needs the
     * line to be a value of anything — it is a change of unit and not a change of order.
     */
    Seam scaledBy(java.math.BigDecimal k) {
        if (k.compareTo(java.math.BigDecimal.ONE) == 0) {
            return this;
        }
        return new Seam(at.times(k), scaled(below, k), scaled(above, k));
    }

    /**
     * One value of a quantity, as a value of the form that wrote {@code k} of it.
     *
     * <p>Which is a number of that form and no longer a value of anything the position holds: three
     * times a decimal is not a decimal the position is written at. So what comes back is counted
     * rather than carried on a carrier, whichever of the two went in.
     */
    private static Level scaled(Level level, java.math.BigDecimal k) {
        if (level == null) {
            return null;
        }
        java.math.BigDecimal at = switch (level) {
            case Level.ACount count -> count.at().at();
            case Level.OnACarrier on -> on.at() instanceof souther.compiler.numeric.Count count
                    ? count.at() : null;
        };
        if (at == null) {
            throw new IllegalStateException(
                    "an order with no numbers was asked for a multiple of one: " + level);
        }
        return new Level.ACount(new souther.compiler.numeric.Count(at.multiply(k)));
    }

    /**
     * The same place, read on another order.
     *
     * <p>What a line between two positions comes to once the other end of it is known: a distance
     * is a place of no carrier until then, and every part of the seam moves together. Mapped end by
     * end rather than by handing one level to all of them, which left a run with the same value at
     * both ends and a reader that could no longer tell which side of the line it lay.
     */
    Seam mappedBy(java.util.function.UnaryOperator<Level> onto) {
        Level line = at.asALevelOfTheQuantity();
        if (line == null) {
            // A line at a place the quantity has no value for has nothing to read on another order:
            // what would move is the place, and the place is a fraction of what the rule wrote.
            // Nothing asks for it — a rule between two positions writes the whole of what it cuts —
            // and reaching here would be a scaled reading of one order let loose on another.
            throw new IllegalStateException(
                    "a line the quantity has no value at cannot be read on another order: " + at);
        }
        Level moved = onto.apply(line);
        if (moved == null) {
            return null;   // the line itself has no place here, so neither has the seam
        }
        // An end with no place is an end the carrier does not reach, which is a run with no end
        // that way rather than a run that could not be read.
        return new Seam(CutPosition.at(moved), below == null ? null : onto.apply(below),
                above == null ? null : onto.apply(above));
    }

    /**
     * This line as the end of a run on one side of it, written as the rule that drew it.
     *
     * <p>For a line the quantity has no value at, which is the only case with nothing else to name
     * it by. Written as the rule rather than as the place — {@code 3 * x <= 1} and not a third
     * rounded to something it is not — and reduced, so the two rules that draw one line write it
     * one way. Null where the quantity has no numbers, which is never scaled and so always has a
     * value at its lines.
     *
     * @param muchOf how the reader writes so much of the quantity, which is the quantity's own
     *               answer where the reader has one to ask
     */
    public String asARuleAbout(java.util.function.Function<java.math.BigDecimal, String> muchOf,
                               Towards side) {
        java.math.BigDecimal[] rule = at.asARule();
        if (rule == null) {
            return null;
        }
        String much = muchOf.apply(rule[0]);
        return side == Towards.ABOVE ? plain(rule[1]) + " < " + much
                : much + " <= " + plain(rule[1]);
    }

    private static String plain(java.math.BigDecimal number) {
        return number.stripTrailingZeros().toPlainString();
    }

    /**
     * The line as a value the quantity has there, or null where it has none.
     *
     * <p>Apart from {@link CutPosition#asALevelOfTheQuantity}, which says the rule wrote the whole
     * of the quantity and not that the quantity stands anywhere near the line. The two part company
     * wherever a line is written in a quantity's own units and the quantity steps or fills past it:
     * {@code 3 * d > 1} writes one of {@code 3 * d}, whose values are the thirds of a decimal, and
     * one is not one of them.
     *
     * <p>Answered without an order to ask, because the seam already holds the answer: the quantity
     * has a value at the line exactly where one of the two values beside the line is the line. Asked
     * the other way, a run beside a line the quantity never reaches was written with both its ends
     * turned round — {@link #keepsItsOwnValueBelow} is false there for want of a value below rather
     * than because the line's own value lies above.
     */
    public Level attainedLine() {
        Level line = at.asALevelOfTheQuantity();
        if (line == null) {
            return null;
        }
        return below != null && below.key().equals(line.key())
                || above != null && above.key().equals(line.key()) ? line : null;
    }

    /**
     * Whether the line's own value is on the lower side of it.
     *
     * <p>What the two operators that part the values in one place disagree about, and the one thing
     * a run either side has to ask: the run below ends at the value where the line keeps it, and
     * starts past it where it does not. Read off the two ends rather than carried from the rule,
     * because two rules that part the values alike are one seam and only one of them was kept.
     */
    public boolean keepsItsOwnValueBelow() {
        return below != null && at.compare(below) == 0;
    }

    /**
     * One value of the quantity that this seam is at, for a reader putting several of them in the
     * order their values are in.
     *
     * <p>Either end will do and neither is the seam: the two are one step apart on an order that
     * steps, and where only one of them exists it is the one that says where the values part.
     */
    Level somewhere() {
        return below != null ? below : above != null ? above : at.asALevelOfTheQuantity();
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
