package souther.compiler.partition;

import souther.compiler.check.Carrier;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.NumericDomain.LinearForm;
import souther.compiler.numeric.Place;
import souther.compiler.observe.ObservedValue;

import java.util.Map;

/**
 * What a border is a border <em>of</em>: the quantity a rule cuts.
 *
 * <p>A rule divides something, and what it divides is not always a position. {@code cost <= 100000}
 * cuts one position's own values; {@code charge > ceiling} cuts how far two positions stand apart;
 * {@code 300 * straw + 600 * choco <= 4800} cuts what an arithmetic form over several of them comes
 * to. All three are one thing cut at one place, and only the first of them is a place any position
 * has a value at.
 *
 * <p><b>Everything a border's readers ask is asked here, and which of these it is is asked
 * nowhere.</b> How the quantity's own values are ordered ({@link #levels}), whether a row stands at
 * one item ({@link #standsAt}), what a search has to solve to put a row there ({@link #standingAt}),
 * and how a report names it ({@link #left} and {@link #writtenAt}). A reader outside this file that
 * asked which of the variants it was holding would be asking the same question the old two shapes of
 * line asked, under a new name — and that question is what made a second shape cost a copy of the
 * border machinery in nine places: a criterion vocabulary, a border factory, a generator entry, a
 * probe method, an assessment path and a report arm apiece.
 *
 * <p><b>Sealed, so a quantity added is one this file answers for.</b> Sealed here and nowhere else:
 * what a variant costs is the four answers below, and nothing downstream gains an arm.
 */
public sealed interface BorderQuantity {

    /**
     * The number one position holds, which is the position's own values.
     *
     * <p>The only quantity whose levels a carrier can write, because they are the carrier's own
     * values. A line here divides the position into classes, which is why this one has an axis and
     * the others do not.
     */
    record OfACoordinate(AxisId axis, NumericTerm term, Carrier of) implements BorderQuantity {

        public OfACoordinate {
            if (axis == null || term == null || of == null) {
                throw new IllegalArgumentException("a coordinate quantity names a position and an "
                        + "order: " + axis + " " + term + " " + of);
            }
        }

        @Override
        public LevelSpace levels() {
            return LevelSpace.onACarrier(of);
        }

        @Override
        public Carrier carrier() {
            return of;
        }

        @Override
        public Stands standsAt(Criterion where, Observation row) {
            return switch (term.read(row.at(term.path()), of)) {
                case NumericTerm.Reading.Missing _ -> Stands.UNREADABLE;
                case NumericTerm.Reading.NotNumber _ -> Stands.NO;
                case NumericTerm.Reading.Number number ->
                        where.holds(levels(), new Level.OnACarrier(of, number.value()))
                                ? Stands.YES : Stands.NO;
            };
        }

        @Override
        public Standing standingAt(Criterion where) {
            return new Standing.OfOneCoordinate(term, of, where);
        }

        @Override
        public String named() {
            return axis.toString();
        }

        @Override
        public String left() {
            return axis.term();
        }

        /** The carrier's own spelling. A day count is a date here and nowhere else. */
        @Override
        public String writtenAt(Level level) {
            return of.written(placeOf(level));
        }

        @Override
        public BoundaryTarget.Shape shape() {
            return BoundaryTarget.Shape.AT_VALUE;
        }

        private Place placeOf(Level level) {
            if (!(level instanceof Level.OnACarrier on)) {
                throw new IllegalStateException(
                        "a coordinate was asked to write a level that is not one of its values: "
                                + level);
            }
            return on.at();
        }
    }

    /**
     * How far two positions on one carrier stand apart.
     *
     * <p>Drawn by a rule comparing one position against another. It divides neither of them — which
     * values of one are on which side depends on the other, and a class is a set of values of one
     * position — so this is a line without a partition, and the two answers are kept apart rather
     * than the second refusing the first.
     *
     * <p>Its levels are the difference of two counts and are on no carrier: two strings a rule holds
     * apart have no number between them, and a carrier with no numbers asked to write one is what
     * {@link Level} exists to make impossible. So a level here is written <em>beside</em> the other
     * position rather than turned into a value of either.
     *
     * <p>The difference, and not a number of steps walked from one side to the other. A walk is an
     * addition that only exists where the order has a smallest step, and two decimals a rule holds
     * one apart are one apart — read by walking, every such rule was met by no row and had no row
     * anything could compose.
     *
     * <p>One carrier, because both sides are ordered by it. Two operands may be comparable and share
     * no carrier — an enumeration's case is comparable on its sum's order without ranging over it —
     * so what makes this line measurable is the carrier and not the type the comparison type-checked
     * under.
     */
    record Apart(String behavior, NumericTerm on, NumericTerm against, Carrier of)
            implements BorderQuantity {

        public Apart {
            if (behavior == null || on == null || against == null || of == null) {
                throw new IllegalArgumentException("a distance names two positions and one order");
            }
        }

        /**
         * A whole number of the carrier's own steps, where it has one; every number where it does
         * not; and only the level where the two meet where the carrier's values do not count at all.
         *
         * <p>Three answers and not two. Two decimals stand every distance apart and no next distance
         * apart, and two strings stand no measurable distance apart and are still one above the
         * other — so what a carrier says about its steps and what it says about its numbers are
         * asked separately.
         */
        @Override
        public LevelSpace levels() {
            if (!of.counts()) {
                return LevelSpace.onlyWhereTheyMeet();
            }
            return of.spacing() == souther.compiler.numeric.Granularity.DISCRETE
                    ? LevelSpace.steppingBy(java.math.BigDecimal.ONE) : LevelSpace.dense();
        }

        @Override
        public Carrier carrier() {
            return of;
        }

        /**
         * Both sides through the term's own reader, which is the one that reaches a count through the
         * newtype a position may be written as. Compared as places and not as observed values: the
         * two positions are of one carrier and need not be of one type — {@code Charge} against
         * {@code Ceiling} is what the domain this was found in is made of — and two values of
         * different types are never equal however much the numbers inside them agree.
         *
         * <p>How far apart they stand is the difference of two counts, and where the carrier's
         * values do not count it is their order and nothing else. Taken by stepping one side to the
         * other, a carrier with no step answered "nowhere" for every pair — so a rule over two
         * decimals read as met by no row, including the rows that meet it.
         */
        @Override
        public Stands standsAt(Criterion where, Observation row) {
            NumericTerm.Reading here = on.read(row.at(on.path()), of);
            NumericTerm.Reading there = against.read(row.at(against.path()), of);
            if (here instanceof NumericTerm.Reading.Missing
                    || there instanceof NumericTerm.Reading.Missing) {
                return Stands.UNREADABLE;
            }
            if (!(here instanceof NumericTerm.Reading.Number onAt)
                    || !(there instanceof NumericTerm.Reading.Number againstAt)) {
                return Stands.NO;
            }
            if (!of.counts()) {
                // No number between them, and an order all the same. The only level such a quantity
                // takes is the one where they meet, so what the item asks is which way round they
                // stand from it.
                return holdsByOrder(where, onAt.value().compareTo(againstAt.value()))
                        ? Stands.YES : Stands.NO;
            }
            Count apart = Count.number(onAt.value()).minus(Count.number(againstAt.value()));
            return where.holds(levels(), new Level.ACount(apart)) ? Stands.YES : Stands.NO;
        }

        /** Whether a pair standing {@code order} round from where they meet is at the item, for a
         *  carrier whose values do not count. Only the level where they meet is a level here, so an
         *  item is at it, above it or below it and nothing else. */
        private static boolean holdsByOrder(Criterion where, int order) {
            return switch (where) {
                case Criterion.AtTheLevel _ -> order == 0;
                case Criterion.Beyond beyond ->
                        beyond.towards() == Towards.ABOVE ? order > 0 : order < 0;
                case Criterion.AnythingBut _ -> order != 0;
            };
        }

        @Override
        public Standing standingAt(Criterion where) {
            return new Standing.OfTwoOnOneCarrier(on, against, of, where);
        }

        @Override
        public String named() {
            return new AxisId(behavior, on.toString()).toString();
        }

        @Override
        public String left() {
            return on.toString();
        }

        /**
         * The other position, and how far from it.
         *
         * <p>The distance is on neither position, so it is written beside the other one rather than
         * folded into a value: a reader is told that the point is so far from where the two meet,
         * which is what it is.
         */
        @Override
        public String writtenAt(Level level) {
            Count apart = level.asACount();
            return apart.signum() == 0 ? against.toString()
                    : apart.signum() < 0 ? against + " - " + apart.negate().key()
                            : against + " + " + apart.key();
        }

        @Override
        public BoundaryTarget.Shape shape() {
            return BoundaryTarget.Shape.BETWEEN_POSITIONS;
        }

        /** The distance a level names, as a number of the carrier's counts. */
        static Count apartBy(Level level) {
            if (!(level instanceof Level.ACount count)) {
                throw new IllegalStateException(
                        "a distance was asked about a level that is not a number: " + level);
            }
            return count.at();
        }
    }

    /**
     * What an arithmetic form over several positions comes to.
     *
     * <p>The quantity domain testing exists for. An equivalence partition is defined by conditions
     * that may involve more than one variable (ISTQB CTAL-TA v4.0 §3.1.1), and each such condition
     * defines a border; a rule like {@code 300 * straw + 600 * choco <= 4800} draws a line that is
     * not a value of either position, and the four sides of the box those two positions sit in are
     * not it.
     *
     * <p><b>Its levels are a lattice.</b> What {@code 300x + 600y} comes to over whole numbers is
     * every multiple of three hundred and nothing between them, so the value past a threshold of
     * 4800 is 5100 — not 4801, and not whatever value some coordinate takes next. Which coordinates
     * move to reach it is the search's answer and not the report's: the report asks an author for a
     * row where the form comes to 5100, the same way a line between two positions asks for a row
     * where they stand one apart rather than naming a value for either.
     *
     * <p>Constant-free, because {@link AffineReading} moves the constant to the threshold. Left in,
     * the values {@code 2 * a} takes would be the even numbers under one spelling and the odd ones
     * shifted by nine under another.
     */
    record OverAForm(String behavior, LinearForm<NumericTerm> form, Carrier of)
            implements BorderQuantity {

        public OverAForm {
            if (behavior == null || form == null || of == null || form.coefs().isEmpty()) {
                throw new IllegalArgumentException("a form quantity names positions and one order");
            }
            if (form.constant().signum() != 0) {
                throw new IllegalArgumentException(
                        "a quantity carries no constant; it belongs to the threshold: " + form);
            }
        }

        /**
         * Every multiple of the greatest common divisor of the coefficients, where the positions
         * count in steps; every number where they do not.
         *
         * <p>Bézout's, and exact rather than a guess: the values {@code Σ cᵢxᵢ} takes over the whole
         * numbers are exactly the multiples of {@code gcd(cᵢ)}. What the rules leave the positions
         * does not enter here — a level this says the form takes may be one no row can be written
         * at, and that is the search's answer rather than a reason to move the border.
         */
        @Override
        public LevelSpace levels() {
            return of.spacing() == souther.compiler.numeric.Granularity.DISCRETE
                    ? LevelSpace.steppingBy(LevelSpace.stepOf(form.coefs().values()))
                    : LevelSpace.dense();
        }

        @Override
        public Carrier carrier() {
            return of;
        }

        @Override
        public Stands standsAt(Criterion where, Observation row) {
            java.math.BigDecimal at = java.math.BigDecimal.ZERO;
            for (Map.Entry<NumericTerm, java.math.BigDecimal> each : form.coefs().entrySet()) {
                NumericTerm.Reading read =
                        each.getKey().read(row.at(each.getKey().path()), of);
                if (read instanceof NumericTerm.Reading.Missing) {
                    return Stands.UNREADABLE;
                }
                if (!(read instanceof NumericTerm.Reading.Number number)) {
                    return Stands.NO;
                }
                at = at.add(Count.number(number.value()).at().multiply(each.getValue()));
            }
            return where.holds(levels(), new Level.ACount(new Count(at)))
                    ? Stands.YES : Stands.NO;
        }

        @Override
        public Standing standingAt(Criterion where) {
            return new Standing.OfAForm(form, of, levels(), where);
        }

        @Override
        public String named() {
            return new AxisId(behavior, left()).toString();
        }

        /**
         * The form as an author would write it.
         *
         * <p>In one order whatever order the coefficients were recorded in. A form is a map and a
         * report is a document that is compared against the one written last time, so the terms are
         * named in an order the form itself settles.
         */
        @Override
        public String left() {
            StringBuilder out = new StringBuilder();
            for (Map.Entry<NumericTerm, java.math.BigDecimal> each
                    : AffineReading.ordered(form)) {
                java.math.BigDecimal coef = each.getValue();
                if (out.isEmpty()) {
                    out.append(coef.signum() < 0 ? "-" : "");
                } else {
                    out.append(coef.signum() < 0 ? " - " : " + ");
                }
                java.math.BigDecimal size = coef.abs();
                if (size.compareTo(java.math.BigDecimal.ONE) != 0) {
                    out.append(size.stripTrailingZeros().toPlainString()).append(" * ");
                }
                out.append(each.getKey());
            }
            return out.toString();
        }

        @Override
        public String writtenAt(Level level) {
            if (!(level instanceof Level.ACount count)) {
                throw new IllegalStateException(
                        "a form was asked to write a level that is not a number: " + level);
            }
            return count.at().key();
        }

        @Override
        public BoundaryTarget.Shape shape() {
            return BoundaryTarget.Shape.OVER_A_FORM;
        }

    }

    /** How this quantity's own values are ordered, and which of them it can take. */
    LevelSpace levels();

    /** The order every position under this quantity is written back on, which is one order: a
     *  quantity over positions of two carriers is one nothing could write a row for. */
    Carrier carrier();

    /** Whether a row stands at one item of a border on this quantity, or whether it could not be
     *  read. */
    Stands standsAt(Criterion where, Observation row);

    /** What a search has to solve to put a row at one item. */
    Standing standingAt(Criterion where);

    /** The left of the {@code left = right} a report names a border on this by, qualified by the
     *  behavior it is an input of. */
    String named();

    /** The same, as the bare term a generated row is labelled with. */
    String left();

    /** One level of this quantity, as a report writes it. */
    String writtenAt(Level level);

    /**
     * Which shape a border on this has, for a reader that has to tell them apart without holding
     * either.
     *
     * <p>A published word and not a question this compiler asks itself. A report writes a line as
     * {@code left = right} whichever it is, and what stands on the right is a value in one case and a
     * position in another; a consumer reading the right as a value would read a position's name as
     * one, so the shape is said rather than inferred.
     */
    BoundaryTarget.Shape shape();

    /** Whether a row is at an item, where a row that could not be read is neither. */
    enum Stands {
        YES,
        NO,
        UNREADABLE
    }

    /** What one row holds at each of a behavior's positions, for a quantity reading its own value
     *  off it. Handed in rather than reached for: which rows there are and how a value is found in
     *  one belong to the measure, and a quantity only asks what stands at a path. */
    interface Observation {
        ObservedValue at(TermPath path);
    }
}
