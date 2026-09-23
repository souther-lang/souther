package souther.compiler.partition;

import souther.compiler.numeric.ExactRatio;
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
        // Whether the order has a place there at all, which is not whether the quantity takes the
        // level: `2 * a <= 9` cuts between eight and ten and nine is neither. An order whose only
        // number is where two positions meet has one place and no others, and a level three along
        // it is a line nowhere — asked past that, the two sides came back with nothing at either
        // end and a seam was built out of a level the order has no room for.
        if (!space.canCutAt(cut)) {
            throw new IllegalArgumentException(
                    "this order has no place at " + cut + " for a line to be");
        }
        boolean attains = space.attainable(cut);
        Level below = attains && belongsTo == Towards.BELOW ? cut
                : beside(space, cut, Towards.BELOW);
        Level above = attains && belongsTo == Towards.ABOVE ? cut
                : beside(space, cut, Towards.ABOVE);
        return new Seam(
                new CutPosition(cut,
                        into == null ? ExactRatio.ONE : into.per()),
                inUnitsOf(below, into), inUnitsOf(above, into));
    }

    /**
     * Where a rule cutting {@code of} at {@code at} parts that quantity's values.
     *
     * <p>The one derivation of it, for the two things that need it: the reading that met the rule,
     * and a later reader holding the line the reading drew. Written twice, a border's own account of
     * where it parts the values would be free to differ from the one the rule was read to.
     *
     * <p>Found on the order the rule was written on, which is the order that knows which levels the
     * written form attains — {@code 2 * n <= 9} cuts the even numbers and nine is not one of them,
     * so the two sides part between eight and ten. Read back into the quantity's own units
     * afterwards, which is exact: a level the written form attains is a multiple of how much of the
     * quantity it wrote.
     *
     * @param claim what the rule states about the value it wrote. A rule that names a value parts
     *              the quantity twice, under what it names and over it, and this is the lower of the
     *              two — a place the values genuinely part, rather than a side chosen for a rule
     *              that has none
     */
    public static Seam where(BorderQuantity of, Level at, souther.compiler.check.ComparisonClaim claim) {
        Towards belongsTo = claim instanceof souther.compiler.check.ComparisonClaim.Cut order
                ? order.valueBelongs() : Towards.ABOVE;
        souther.compiler.numeric.LinearForm<souther.compiler.inputs.NumericTerm> direction =
                of.direction();
        ExactRatio per = QuantityKey.per(direction);
        return of(of.levels(), at, belongsTo, new Scale(per, direction.coefs().size() == 1
                ? of.carrierOf(direction.coefs().keySet().iterator().next()) : null));
    }

    /**
     * Which side of this seam a value of the quantity falls on.
     *
     * <p>Every value is on one side or the other, including the one the line is at: what parts the
     * values is a place between two of them, and the value at the line belongs to whichever side the
     * rule put it on. Which side that is is read off the seam rather than off the rule — a seam
     * names the last value below and the first above, and the line's own value is one of those two
     * exactly where the quantity takes it.
     */
    public Towards sideOf(ExactRatio value) {
        int where = at.compare(value);
        if (where != 0) {
            return where < 0 ? Towards.BELOW : Towards.ABOVE;
        }
        return below != null && at.compare(below) == 0 ? Towards.BELOW : Towards.ABOVE;
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
        // level for its number is what {@link Level#asAnExactNumber} exists to refuse.
        if (level == null || into == null
                || into.per().equals(ExactRatio.ONE)) {
            return level;
        }
        ExactRatio at = level.asAnExactNumber().dividedBy(into.per());
        if (into.onto() == null) {
            return new Level.OfTheQuantity(at);
        }
        // The carrier edge, crossed by a reader that has established it can be: a level the written
        // form attains is a whole multiple of what that form wrote, so reading it back in the
        // quantity's own units lands on a value the position holds. Both halves of that are asked,
        // because a number can be a count and be no value of this order — a half is a count and no
        // whole number is one.
        return Level.OnACarrier.held(into.onto(), at);
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
     * This division's coordinates written out as text: the last value on one side and the first on
     * the other.
     *
     * <p>The same three cases {@link #key()} has, because the two questions differ in the writing
     * and not in what is read. Each end is spelled as a level is ({@link Level#spelled}), so a
     * division of the days is two day counts and never two dates. An end the order names no value
     * at is written as nothing, the way it is named as nothing.
     */
    public String spelled() {
        if (below == null && above == null) {
            return "@" + at.spelled();
        }
        return (below == null ? "" : below.spelled()) + "|"
                + (above == null ? "" : above.spelled());
    }

    /** The same division with every level written the one way, for an identity to be built from.
     *  What {@link #key()} answers, kept as the seam rather than as a word. */
    public Seam canonical() {
        return new Seam(at.canonical(),
                below == null ? null : below.canonical(),
                above == null ? null : above.canonical());
    }

    /**
     * How a level written in one form's terms reads as a level of the quantity it is a multiple of.
     *
     * @param per  how much of the quantity the form wrote ({@link QuantityKey#per})
     * @param onto the carrier the quantity's own values are ordered by, or null where it has none
     */
    public record Scale(ExactRatio per,
                        souther.compiler.check.Carrier onto) {}

    /**
     * The same division of the quantity read the other way round.
     *
     * <p>The two sides change places. What was the last value below the line is the first value
     * above it once the quantity is measured backwards, and the line itself is at the negated
     * place — so a division that names a value on one side only still names it on one side only,
     * and on the other one.
     *
     * <p>Which is the whole of what makes a rule between two positions readable from either of
     * them. Negated without the swap, the seam would say the values part with the greater of them
     * below, and the run built from it would be an interval whose ends have crossed.
     */
    Seam reflected() {
        return new Seam(at.reflected(), above == null ? null : above.negated(),
                below == null ? null : below.negated());
    }

    /**
     * The same seam, said in units {@code k} times smaller.
     *
     * <p>What one quantity's lines come to for a rule that wrote a multiple of it: the arrangement
     * is held in the quantity's own units, because that is the only order every rule about it is
     * on, and each rule reads its rows through the form it was written as. Nothing here needs the
     * line to be a value of anything — it is a change of unit and not a change of order.
     */
    Seam scaledBy(ExactRatio k) {
        if (k.equals(ExactRatio.ONE)) {
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
    private static Level scaled(Level level, ExactRatio k) {
        if (level == null) {
            return null;
        }
        ExactRatio at = switch (level) {
            case Level.OfTheQuantity counted -> counted.at();
            case Level.OnACarrier on -> on.at() instanceof souther.compiler.numeric.Count count
                    ? count.exactly() : null;
        };
        if (at == null) {
            throw new IllegalStateException(
                    "an order with no numbers was asked for a multiple of one: " + level);
        }
        return new Level.OfTheQuantity(at.times(k));
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
    public String asARuleAbout(
            java.util.function.Function<ExactRatio, String> muchOf,
            Towards side) {
        ExactRatio rule = at.asARule();
        if (rule == null) {
            return null;
        }
        // The denominator is how much of the quantity and the numerator is what it comes to, which
        // is what a ratio in lowest terms holds: `3 * x <= 1` is the line at a third written as a
        // rule, and the two numbers are the ones an author would write.
        ExactRatio.Fraction both = rule.asFraction();
        String much = muchOf.apply(ExactRatio.of(both.denominator()));
        return side == Towards.ABOVE ? both.numerator() + " < " + much
                : much + " <= " + both.numerator();
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
        return (below != null && below.key().equals(line.key()))
                || (above != null && above.key().equals(line.key())) ? line : null;
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
     * Where a rule leaves off on one side: the last value the quantity takes there, or the line
     * itself where the order names none.
     *
     * <p><b>What a rule places, as against the number it wrote.</b> An order that steps has a next
     * value, so a rule refusing its own threshold keeps the values from one count in; an order that
     * fills has none, and what such a rule keeps comes arbitrarily close to the line without
     * reaching it. Both are one question and this is where it is answered — asked as the threshold
     * alone, a range that stops where the rule leaves off disagrees with it by exactly one count,
     * and asked as the side alone, an order that fills has no answer at all.
     *
     * <p>Null where the order names no value there and the line is not one of this quantity's levels
     * either, which is a rule that wrote a multiple of the quantity and refuses its own threshold.
     * There is nothing on that side to name, in the units a caller holding this is working in.
     */
    Level leaving(Towards side) {
        Level named = side == Towards.BELOW ? below : above;
        return named != null ? named : at.asALevelOfTheQuantity();
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
