package souther.compiler.partition;

import souther.compiler.check.Carrier;
import souther.compiler.inputs.BoundaryDomain;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Place;
import souther.compiler.observe.ObservedValue;

import java.util.Optional;

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
     * <p>Its levels are a count of the carrier's own steps and are on no carrier: two strings a rule
     * holds apart have no number between them, and a carrier with no numbers asked to write one is
     * what {@link Level} exists to make impossible. So a level here is stepped <em>from</em> the
     * other position rather than turned into a value — which is also how a report writes it, and the
     * two agree because there is one answer.
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

        /**
         * Both sides through the term's own reader, which is the one that reaches a count through the
         * newtype a position may be written as. Compared as places and not as observed values: the
         * two positions are of one carrier and need not be of one type — {@code Charge} against
         * {@code Ceiling} is what the domain this was found in is made of — and two values of
         * different types are never equal however much the numbers inside them agree.
         */
        @Override
        public Carrier carrier() {
            return of;
        }

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
            // Stepped from the other position rather than subtracted. A carrier whose values do not
            // count has no difference to take and does have an order, and stepping asks it only for
            // what it has: where the step is zero every carrier answers, and where it is not the
            // criterion only ever names a step the order was already asked for.
            Optional<Place> from = stepped(againstAt.value(), where.against());
            return from.isPresent() && holdsBetween(where, onAt.value(), from.get())
                    ? Stands.YES : Stands.NO;
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
         * The other position, stepped.
         *
         * <p>The step is on the distance and not on either position, so it is written beside the
         * other one rather than folded into a value: a reader is told that the point is so far from
         * where the two meet, which is what it is.
         */
        @Override
        public String writtenAt(Level level) {
            long steps = stepsOf(level);
            return steps == 0 ? against.toString()
                    : steps < 0 ? against + " - " + -steps : against + " + " + steps;
        }

        @Override
        public BoundaryTarget.Shape shape() {
            return BoundaryTarget.Shape.BETWEEN_POSITIONS;
        }

        /** The place the {@code on} term has to be at or past, which is the other one moved by the
         *  level. Empty where the carrier names no value that far, which is what leaves such an item
         *  unwritable rather than at a value nobody named. */
        Optional<Place> stepped(Place from, Level by) {
            BoundaryDomain domain = BoundaryDomain.on(of);
            long steps = stepsOf(by);
            Optional<Place> walked = Optional.of(from);
            for (long taken = 0; taken < Math.abs(steps); taken++) {
                walked = walked.flatMap(
                        at -> steps > 0 ? domain.successor(at) : domain.predecessor(at));
            }
            return walked;
        }

        private static long stepsOf(Level level) {
            if (!(level instanceof Level.ACount count)) {
                throw new IllegalStateException(
                        "a distance was asked about a level that is not a number of steps: " + level);
            }
            return count.at().at().longValueExact();
        }

        /** Whether {@code at} stands the criterion's way of the place the level names. Read off the
         *  criterion's own relation, so that the two positions are compared the way one position and
         *  a value are. */
        private static boolean holdsBetween(Criterion where, Place at, Place from) {
            int order = at.compareTo(from);
            return switch (where) {
                case Criterion.AtTheLevel _ -> order == 0;
                case Criterion.Beyond beyond ->
                        beyond.towards() == Towards.ABOVE ? order > 0 : order < 0;
                case Criterion.AnythingBut _ -> order != 0;
            };
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

    /** A level of this quantity written as a whole number of its own steps, for a caller that has one
     *  rather than a level. */
    static Level steps(long n) {
        return new Level.ACount(Count.of(n));
    }
}
