package souther.compiler.partition;

import souther.compiler.check.Carrier;
import souther.compiler.inputs.TermOrders;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.NumericDomain.LinearForm;
import souther.compiler.numeric.Place;
import souther.compiler.observe.ObservedValue;

import java.util.List;
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
    record OfACoordinate(AxisId axis, NumericTerm.FromOnePosition term, TermOrders of)
            implements BorderQuantity {

        public OfACoordinate {
            if (axis == null || term == null || of == null) {
                throw new IllegalArgumentException("a coordinate quantity names a position and an "
                        + "order: " + axis + " " + term + " " + of);
            }
        }

        @Override
        public LevelSpace levels() {
            return LevelSpace.onACarrier(of.answered());
        }

        @Override
        public List<NumericTerm> terms() {
            return List.of(term);
        }

        /** Null where the number it moved to is answered by no single position: what this quantity
         *  is is one position's own values, so a move that leaves it without one leaves it
         *  something else. */
        @Override
        public BorderQuantity movedTo(NumericTerm from, NumericTerm to, TermOrders orders) {
            NumericTerm.FromOnePosition landed = to.atOnePosition();
            return term.equals(from) && landed != null
                    ? new OfACoordinate(new AxisId(axis.behavior(), to.toString()), landed, orders)
                    : null;
        }

        /** Its one position's, and nothing about any other. */
        @Override
        public Carrier carrierOf(NumericTerm asked) {
            return term.equals(asked) ? of.answered() : null;
        }

        @Override
        public Stands standsAt(Criterion where, Observation row) {
            // Read on the order the value is written on and asked on the order the answer is
            // measured on. The two are one carrier for a position's own content and part for a term
            // that is what an operation answered — a time counts the seconds of its day and its hour
            // counts by one, so a reader handed the second decodes the first as nothing (#1027).
            return switch (term.read(row.at(term.position()), of)) {
                case NumericTerm.Reading.Missing _ -> Stands.UNREADABLE;
                case NumericTerm.Reading.NotNumber _ -> Stands.NO;
                case NumericTerm.Reading.Number number ->
                        where.holds(new Level.OnACarrier(of.answered(), number.value()))
                                ? Stands.YES : Stands.NO;
            };
        }

        @Override
        public Standing standingAt(Criterion where) {
            return new Standing.OfOneCoordinate(term, of.answered(), where);
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
            return of.answered().written(placeOf(level));
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
     * <p>An order apiece, and the two need not be one. Which order a position is read and written on
     * is a question about that position, and a distance runs between two positions that answer it
     * differently as readily as between two that agree: a decimal against a whole number is one
     * distance written two ways. Held as one order for the pair, whichever of them a caller happened
     * to have was used to write both back and to read both off a row — and where that order belonged
     * to neither, the border was met by no row and composed for by none (#1018).
     *
     * <p>What the two do have to share is the counts, and only where there are counts to share.
     * Where they meet is a place on both orders whatever they are; where they stand a number apart
     * is a number in one arithmetic, and two orders with different origins or different steps have
     * no such number ({@link Carrier#sharesCountSpaceWith}). A pair that shares none is an
     * arithmetic form over both positions and is read as {@link OverAForm}, whose coefficients are
     * where a conversion between two orders is written.
     */
    record Apart(String behavior, NumericTerm.FromOnePosition on,
                 NumericTerm.FromOnePosition against,
                 Map<NumericTerm, TermOrders> carriers) implements BorderQuantity {

        @Override
        public List<NumericTerm> terms() {
            return List.of(on, against);
        }

        @Override
        public BorderQuantity movedTo(NumericTerm from, NumericTerm to, TermOrders orders) {
            if (!on.equals(from) && !against.equals(from)) {
                return null;
            }
            // A distance is between two positions, so a move that leaves either end answered by no
            // single position leaves the pair something a distance is not.
            NumericTerm.FromOnePosition landed = to.atOnePosition();
            if (landed == null) {
                return null;
            }
            NumericTerm.FromOnePosition here = on.equals(from) ? landed : on;
            NumericTerm.FromOnePosition there = against.equals(from) ? landed : against;
            // A distance runs between two positions, and a name standing at more than one can bring
            // the two ends of one together. Answered here, because what a caller has in hand is a
            // name that moved and not a pair it chose.
            if (here.equals(there)) {
                return null;
            }
            Map<NumericTerm, TermOrders> moved = new java.util.LinkedHashMap<>();
            moved.put(here, on.equals(from) ? orders : carriers.get(on));
            moved.put(there, against.equals(from) ? orders : carriers.get(against));
            return new Apart(behavior, here, there, moved);
        }

        public Apart {
            if (behavior == null || on == null || against == null || carriers == null) {
                throw new IllegalArgumentException("a distance names two positions and their orders");
            }
            // First, because a distance between one position and itself is what the rest of this
            // cannot be asked about: two terms that are one term are one key, and a map of them
            // would refuse the pair with a sentence about maps.
            if (on.equals(against)) {
                throw new IllegalArgumentException(
                        "a distance runs between two positions, and this names one twice: " + on);
            }
            carriers = Map.copyOf(carriers);
            // An order per position, held here so no reader has to answer for a position with none.
            // A map beside a pair is two structures, and two structures are what come apart.
            if (!carriers.keySet().equals(java.util.Set.of(on, against))) {
                throw new IllegalArgumentException("a distance is between the positions it names,"
                        + " each on one order: " + java.util.Set.of(on, against) + " against "
                        + carriers.keySet());
            }
            Carrier here = carriers.get(on).answered();
            Carrier there = carriers.get(against).answered();
            if (!here.standsAgainst(there)) {
                throw new IllegalArgumentException("a distance is between two orders a value of"
                        + " one stands somewhere on: " + here + " against " + there);
            }
        }

        /** The order the first position is read and written on. */
        private Carrier onCarrier() {
            return carriers.get(on).answered();
        }

        /** The order the other position is read and written on. */
        private Carrier againstCarrier() {
            return carriers.get(against).answered();
        }

        /** Whether the two positions stand on one order, which is every pair a rule names itself and
         *  is what decides which search a point of this line is looked for by. */
        private boolean onOneCarrier() {
            return onCarrier().equals(againstCarrier());
        }

        /** Whether a distance between them is a number at all, which two strings give no. Asked of
         *  either, since a pair that shares its counts shares whether it has any. */
        private boolean counts() {
            return onCarrier().counts();
        }

        /**
         * A whole number of steps where both orders step; every number where either does not; and
         * only the level where the two meet where their values do not count at all.
         *
         * <p>Three answers and not two. Two decimals stand every distance apart and no next distance
         * apart, and two strings stand no measurable distance apart and are still one above the
         * other — so what an order says about its steps and what it says about its numbers are asked
         * separately.
         *
         * <p>Of both orders and not of one, which is the same rule a form of several positions is
         * spaced by ({@link LevelSpace#addedUpOver}): a distance between a whole number and a decimal
         * lands wherever the decimal does.
         */
        @Override
        public LevelSpace levels() {
            if (!counts()) {
                return LevelSpace.onlyWhereTheyMeet();
            }
            return LevelSpace.addedUpOver(carriers.values().stream()
                    .map(TermOrders::answered).toList())
                    == souther.compiler.numeric.Granularity.DISCRETE
                    ? LevelSpace.steppingBy(java.math.BigDecimal.ONE) : LevelSpace.dense();
        }

        /** That position's own, which is what it is read off a row and written back on. */
        @Override
        public Carrier carrierOf(NumericTerm asked) {
            TermOrders orders = carriers.get(asked);
            return orders == null ? null : orders.answered();
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
            // Each on its own order. Read on one order for the pair, a position written back
            // differently from the other was read as a value it does not hold — a date read as a
            // whole number is no number at all, and the row stood at nothing (#1018).
            NumericTerm.Reading here = on.read(row.at(on.subjectPath()), carriers.get(on));
            NumericTerm.Reading there =
                    against.read(row.at(against.subjectPath()), carriers.get(against));
            if (here instanceof NumericTerm.Reading.Missing
                    || there instanceof NumericTerm.Reading.Missing) {
                return Stands.UNREADABLE;
            }
            if (!(here instanceof NumericTerm.Reading.Number onAt)
                    || !(there instanceof NumericTerm.Reading.Number againstAt)) {
                return Stands.NO;
            }
            if (!counts()) {
                // No number between them, and an order all the same. The only level such a quantity
                // takes is the one where they meet, so what the item asks is which way round they
                // stand from it.
                return holdsByOrder(where, onAt.value().compareTo(againstAt.value()))
                        ? Stands.YES : Stands.NO;
            }
            Count apart = Count.number(onAt.value()).minus(Count.number(againstAt.value()));
            return where.holds(new Level.ACount(apart)) ? Stands.YES : Stands.NO;
        }

        /** Whether a pair standing {@code order} round from where they meet is at the item, for a
         *  carrier whose values do not count. Only the level where they meet is a level here, so an
         *  item is at it, above it or below it and nothing else. */
        private static boolean holdsByOrder(Criterion where, int order) {
            return switch (where) {
                case Criterion.AtTheLevel _ -> order == 0;
                // The only level such a quantity takes is the one where they meet, so which run a
                // pair is in is which way round they stand from it — said as that count, since the
                // sign is the whole of what the order has.
                case Criterion.Within within -> within.holds(
                        new Level.ACount(souther.compiler.numeric.Count.of(order)));
                case Criterion.AnythingBut _ -> order != 0;
            };
        }

        /**
         * The pair's own search where both stand on one order, and the form's where they do not.
         *
         * <p>Two lowerings and not a search that takes two orders. What a point of this line asks
         * for is an assignment of both positions, and there is already a search that assigns several
         * positions each on its own order ({@link Standing.OfAForm}) — a distance is that form with
         * coefficients of one and minus one. So the pair that needs it is handed to it, and the
         * search written for one order is left answering for exactly the pairs it was written for.
         *
         * <p>Which is not a preference between them. A form adds its positions up and two strings
         * add up to nothing, so a pair with no counts can only be searched for by the first;
         * generalising that one to two orders would have left it deciding, per pair, which of them
         * to walk along and which to land on — the same shape of premise this issue was about.
         *
         * <p>The quantity is unchanged either way. What a border is of and how a row for it is found
         * are two questions ({@link Standing}), so a distance searched for as a form is still a
         * distance, and a report still names it beside the other position rather than as a form.
         */
        @Override
        public Standing standingAt(Criterion where) {
            if (onOneCarrier()) {
                return new Standing.OfTwoOnOneCarrier(on, against, onCarrier(), where);
            }
            return new Standing.OfAForm(
                    LinearForm.<NumericTerm>atom(on).minus(LinearForm.atom(against)),
                    answeredOn(carriers), levels(), where);
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
    record OverAForm(String behavior, LinearForm<NumericTerm> form, Map<NumericTerm, TermOrders> on)
            implements BorderQuantity {

        @Override
        public List<NumericTerm> terms() {
            return List.copyOf(form.coefs().keySet());
        }

        @Override
        public BorderQuantity movedTo(NumericTerm from, NumericTerm to, TermOrders orders) {
            if (!form.coefs().containsKey(from) || form.coefs().containsKey(to)) {
                return null;
            }
            Map<NumericTerm, java.math.BigDecimal> coefs = new java.util.LinkedHashMap<>();
            form.coefs().forEach((term, coef) -> coefs.put(term.equals(from) ? to : term, coef));
            Map<NumericTerm, TermOrders> moved = new java.util.LinkedHashMap<>();
            on.forEach((term, its) -> moved.put(term.equals(from) ? to : term,
                    term.equals(from) ? orders : its));
            return new OverAForm(behavior,
                    new LinearForm<>(form.constant(), coefs), moved);
        }

        public OverAForm {
            if (behavior == null || form == null || on == null || form.coefs().isEmpty()) {
                throw new IllegalArgumentException("a form quantity names positions and their orders");
            }
            if (form.constant().signum() != 0) {
                throw new IllegalArgumentException(
                        "a quantity carries no constant; it belongs to the threshold: " + form);
            }
            on = Map.copyOf(on);
            // An order per position of the form, held here so no reader has to answer for a
            // position with none. A map beside a form is two structures, and two structures are
            // what come apart: written this way the pair that disagrees does not exist.
            if (!on.keySet().equals(form.coefs().keySet())) {
                throw new IllegalArgumentException("a form is over the positions it names, and each"
                        + " of them is read on one order: " + form.coefs().keySet() + " against "
                        + on.keySet());
            }
            // And each of those orders has counts under it, which is what a sum adds. Nothing
            // more: whether these positions add up to anything is settled by whatever produced the
            // form, and a rule here would be written without the coefficients. `b + a` over two
            // dates is the same orders in the same numbers as `b - a - n`, and only the second is a
            // count of days — which is the form issue #949 asks for.
            for (TermOrders orders : on.values()) {
                Carrier each = orders.answered();
                if (!each.counts()) {
                    throw new IllegalArgumentException(
                            "a form adds its positions up, and this order has no number under it: "
                                    + each);
                }
            }
        }

        /**
         * What the form takes, which is what its coefficients generate over the values its positions
         * take — and not what the order they sit on happens to be.
         *
         * <p>Over positions that step, Bézout's: exactly the multiples of {@code gcd(cᵢ)}. Over
         * positions whose values fill, every multiple of what is left of that divisor once the
         * factors a finite decimal can be divided by are taken out — which is dense and is not every
         * number. Read off the order alone, {@code 3 * a} was taken to reach one, and the border of
         * {@code 3 * a <= 1} owed a row at a level the quantity never arrives at.
         *
         * <p>What the rules leave the positions does not enter here. A level this says the form takes
         * may be one no row can be written at, and that is the search's answer rather than a reason
         * to move the border.
         */
        @Override
        public LevelSpace levels() {
            java.math.BigDecimal step = LevelSpace.stepOf(form.coefs().values());
            return spacing() == souther.compiler.numeric.Granularity.DISCRETE
                    ? LevelSpace.steppingBy(step)
                    : LevelSpace.overFiniteDecimals(LevelSpace.generatorOverFiniteDecimals(step));
        }

        /**
         * How the sum steps, which is how its positions step together.
         *
         * <p>Asked of {@link LevelSpace#addedUpOver}, which a distance asks too. The two are one
         * question — a distance is a form of two positions weighed one and minus one — and answered
         * apiece they were free to disagree about a pair of orders that step differently.
         */
        souther.compiler.numeric.Granularity spacing() {
            return LevelSpace.addedUpOver(on.values().stream()
                    .map(TermOrders::answered).toList());
        }

        /** The order that position is read and written on, and null for a position not in the
         *  form. */
        @Override
        public Carrier carrierOf(NumericTerm asked) {
            TermOrders orders = on.get(asked);
            return orders == null ? null : orders.answered();
        }

        @Override
        public Stands standsAt(Criterion where, Observation row) {
            java.math.BigDecimal at = java.math.BigDecimal.ZERO;
            for (Map.Entry<NumericTerm, java.math.BigDecimal> each : form.coefs().entrySet()) {
                // Each on its own order. Read on one order for the whole form, a position written
                // back differently from its neighbour was read as a value it does not hold.
                //
                // And each asked for what its own number is of: one value where a place answers the
                // term, every value where the term is over a run of them. Asked for one either way,
                // a total would be read off whichever element the row's reading happened to pick.
                TermOrders orders = on.get(each.getKey());
                NumericTerm.Reading read = switch (each.getKey()) {
                    case NumericTerm.FromOnePosition one ->
                            one.read(row.at(one.position()), orders);
                    case NumericTerm.TakenOver over ->
                            over.readOver(row.everyValueAt(over.subjectPath()), orders);
                };
                if (read instanceof NumericTerm.Reading.Missing) {
                    return Stands.UNREADABLE;
                }
                if (!(read instanceof NumericTerm.Reading.Number number)) {
                    return Stands.NO;
                }
                at = at.add(Count.number(number.value()).at().multiply(each.getValue()));
            }
            return where.holds(new Level.ACount(new Count(at)))
                    ? Stands.YES : Stands.NO;
        }

        @Override
        public Standing standingAt(Criterion where) {
            return new Standing.OfAForm(form, answeredOn(on), levels(), where);
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

    /**
     * Every term this quantity is taken of.
     *
     * <p>What a caller moving a quantity to another position has to know it is moving. Read off the
     * arm rather than off the direction the quantity runs in, which is the same list said twice as
     * long as the two agree and one reader's answer the day they do not.
     */
    List<NumericTerm> terms();

    /**
     * The same quantity, with {@code from} taken at {@code to} instead — or null where it is not
     * this quantity's term, or where the move leaves something a quantity cannot be.
     *
     * <p><b>For one name standing at more than one position.</b> A field every case of a sum spreads
     * is one field, so a quantity taken of it is one quantity and it is taken under each case; what
     * moves is where the number is taken, and the comparison that named it is read once and stays
     * one comparison.
     *
     * <p>Answered here rather than assembled by whoever resolved the name, because what has to hold
     * of a quantity is this type's: a distance runs between two positions on orders a value can be
     * counted from one to the other, and a caller building the pair itself would be the second place
     * that has to know it.
     *
     * @param orders what the term is read on and answers at its new position, which is a fact about
     *               where it lands and cannot be carried over from where it was
     */
    BorderQuantity movedTo(NumericTerm from, NumericTerm to, TermOrders orders);

    /**
     * The order one position under this quantity is read and written back on, or null where the
     * quantity is not over that position.
     *
     * <p>Asked per position rather than once. A quantity used to answer with the one order every
     * position under it was on, which a coordinate and a line between two positions can do because
     * they have one — and a form was then held to the same, so a form over positions written back
     * differently was no quantity at all.
     *
     * <p>Nothing is asked of the orders beyond each having counts under it. Which positions a form
     * weighs, and with what, is settled by the arithmetic or the operation semantics that produced
     * the form; this layer does not decide that again.
     */
    Carrier carrierOf(NumericTerm term);

    /** What each of a form's terms is measured on, for a reader of a line rather than of a row. */
    static Map<NumericTerm, Carrier> answeredOn(Map<NumericTerm, TermOrders> orders) {
        Map<NumericTerm, Carrier> out = new java.util.LinkedHashMap<>();
        orders.forEach((term, on) -> out.put(term, on.answered()));
        return Map.copyOf(out);
    }

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

    /**
     * How this quantity writes {@code times} of itself.
     *
     * <p>Asked of the quantity because only it knows what it is made of: twice a position is
     * {@code 2 * n}, and twice {@code 3 * a + 6 * b} is {@code 6 * a + 12 * b} rather than
     * {@code 2 * 3 * a + 6 * b} or anything else a reader outside this file would compose. Written
     * by prefixing, a run over a form came back asking for a row against {@code 2 * 3 * n <= 5},
     * which is the same rule the class beside it writes as {@code 6 * n <= 5}.
     */
    default String left(java.math.BigDecimal times) {
        if (this instanceof OverAForm form && times.compareTo(java.math.BigDecimal.ONE) != 0) {
            return new OverAForm(form.behavior(), form.form().times(times), form.on()).left();
        }
        return times(times, left());
    }

    /**
     * The same of a quantity said under another name.
     *
     * <p>Which is what a debt writes: a line an {@code invariant} drew is on {@code
     * String.length(value)} wherever the type goes, and the reading that met it is at some
     * behavior's own position. One spelling rule, so that the two say a multiple of the quantity the
     * same way.
     */
    static String times(java.math.BigDecimal times, String left) {
        return times.compareTo(java.math.BigDecimal.ONE) == 0 ? left
                : times.stripTrailingZeros().toPlainString() + " * " + left;
    }

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

        /** The one value standing at {@code path}, for a number taken of what is there. */
        ObservedValue at(TermPath path);

        /**
         * Every value standing at {@code path}, for a number taken over a run of them.
         *
         * <p>Beside {@link #at} and not instead of it. What a row holds at a place inside a
         * sequence is as many values as it wrote, and which question is being asked decides what to
         * do with them: a rule relating two positions is about one element and picks, and a rule
         * about what they add up to is about all of them and does not. Answered by one method, the
         * caller that wanted one would be handed a list to choose from and the choosing would move
         * to whoever asked — which is the reading of a row being made twice.
         */
        java.util.List<ObservedValue> everyValueAt(TermPath path);
    }
}
