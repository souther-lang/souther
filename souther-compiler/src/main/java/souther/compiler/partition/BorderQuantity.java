package souther.compiler.partition;

import souther.compiler.check.Carrier;
import souther.compiler.inputs.FilingCoordinate;
import souther.compiler.inputs.Quantities;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.inputs.TermOrders;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.NumericTerms;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.Quantity;
import souther.compiler.meaning.Relation;
import souther.compiler.numeric.Rel;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Place;
import souther.compiler.observe.ObservedValue;

import java.util.List;
import java.util.Map;
import java.util.Set;

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
 * what a variant costs is the answers this interface asks for below, and nothing downstream gains
 * an arm.
 */
public sealed interface BorderQuantity permits LinearQuantity, BorderQuantity.HowMany {

    /**
     * The number one position holds, which is the position's own values.
     *
     * <p>The only quantity whose levels a carrier can write, because they are the carrier's own
     * values. A line here divides the position into classes, which is why this one has an axis and
     * the others do not.
     */
    record OfACoordinate(String behavior, NumericTerm.FromOnePosition term, TermOrders of)
            implements LinearQuantity {

        public OfACoordinate {
            if (behavior == null || behavior.isEmpty() || term == null || of == null) {
                throw new IllegalArgumentException("a coordinate quantity is a behavior's number "
                        + "on an order: " + behavior + " " + term + " " + of);
            }
            // The orders say which number they are of. The second spelling is refused rather than
            // carried into a document.
            of.areOf(term);
        }

        /**
         * What a report calls the position this cuts.
         *
         * <p>Worked out from the number rather than handed in beside it, which is what
         * {@link Axis} holds a measure to for the same reason: a name a caller chooses is a name
         * that can be one number's while the cut is on another, and every reader that goes by it —
         * which behavior the line is of, what a document calls it, whether a measurement divides
         * there — would then be answering about a position this line is not on.
         */
        public AxisId axis() {
            return AxisId.of(behavior, term);
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
        public LinearQuantity movedTo(NumericTerm from, TermOrders to) {
            NumericTerm.FromOnePosition landed = to.term().atOnePosition();
            return term.equals(from) && landed != null
                    ? new OfACoordinate(behavior, landed, to)
                    : null;
        }

        /** Its one position's, and nothing about any other. */
        @Override
        public TermOrders ordersOf(NumericTerm asked) {
            return term.equals(asked) ? of : null;
        }

        /** The position itself, weighed once. */
        @Override
        public LinearForm<NumericTerm> direction() {
            return LinearForm.atom(term);
        }

        @Override
        public Stands standsAt(Criterion where, QuantityReading reading) {
            // Asked on the order the answer is measured on, the value having been read on the order
            // it is written on. The two are one carrier for a position's own content and part for a
            // term that is what an operation answered — a time counts the seconds of its day and its
            // hour counts by one, so a reader handed the second decodes the first as nothing. Which
            // is why the reading is asked for by the orders: read on the other one, this position
            // is a number this quantity does not have.
            return switch (reading.of(of)) {
                case WhatATermRead.CameToNothing(ReadingGap why) -> Stands.couldNotTell(why);
                case WhatATermRead.NoNumberOfTheValue _, WhatATermRead.NothingWrittenThere _ ->
                        Stands.NO;
                case WhatATermRead.Number(Place value) ->
                        where.holds(new Level.OnACarrier(of.answered(), value))
                                ? Stands.YES : Stands.NO;
            };
        }

        @Override
        public Standing standingAt(Criterion where) {
            return new Standing.OfOneCoordinate(term, of.answered(), where);
        }

        @Override
        public String named() {
            return axis().toString();
        }

        @Override
        public String left() {
            return term.toString();
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
    record Apart(String behavior, TermOrders on, TermOrders against) implements LinearQuantity {

        /** The position at one end. */
        public NumericTerm.FromOnePosition onTerm() {
            return on.term().atOnePosition();
        }

        /** The position at the other. */
        public NumericTerm.FromOnePosition againstTerm() {
            return against.term().atOnePosition();
        }

        @Override
        public List<NumericTerm> terms() {
            return List.of(on.term(), against.term());
        }

        @Override
        public LinearQuantity movedTo(NumericTerm from, TermOrders to) {
            if (!on.term().equals(from) && !against.term().equals(from)) {
                return null;
            }
            TermOrders here = on.term().equals(from) ? to : on;
            TermOrders there = against.term().equals(from) ? to : against;
            // A distance is between two positions, so a move that leaves either end answered by no
            // single position leaves the pair something a distance is not. And a name standing at
            // more than one can bring the two ends of one together — answered here, because what a
            // caller has in hand is a name that moved and not a pair it chose.
            if (here.term().atOnePosition() == null || there.term().atOnePosition() == null
                    || here.term().equals(there.term())) {
                return null;
            }
            return new Apart(behavior, here, there);
        }

        public Apart {
            if (behavior == null || on == null || against == null) {
                throw new IllegalArgumentException("a distance names two positions and their orders");
            }
            // Each end is a position's own number on the order that position is read and written
            // on, and the orders say which position that is. Held as a pair of positions beside a
            // map from position to orders, the keys could name the right pair with the values the
            // other way round, and both structures would check out.
            if (on.term().atOnePosition() == null || against.term().atOnePosition() == null) {
                throw new IllegalArgumentException("a distance runs between two positions, and this"
                        + " names " + on.term() + " against " + against.term());
            }
            if (on.term().equals(against.term())) {
                throw new IllegalArgumentException("a distance runs between two positions, and this"
                        + " names one twice: " + on.term());
            }
            if (!on.answered().standsAgainst(against.answered())) {
                throw new IllegalArgumentException("a distance is between two orders a value of"
                        + " one stands somewhere on: " + on.answered() + " against "
                        + against.answered());
            }
        }

        /** The order the first position is read and written on. */
        private Carrier onCarrier() {
            return on.answered();
        }

        /** The order the other position is read and written on. */
        private Carrier againstCarrier() {
            return against.answered();
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
            return LevelSpace.addedUpOver(List.of(on.answered(), against.answered()))
                    == souther.compiler.numeric.Granularity.DISCRETE
                    ? LevelSpace.steppingBy(ExactRatio.ONE) : LevelSpace.dense();
        }

        /** That position's own, which is what it is read off a row and written back on. */
        @Override
        public TermOrders ordersOf(NumericTerm asked) {
            if (on.term().equals(asked)) {
                return on;
            }
            return against.term().equals(asked) ? against : null;
        }

        /** Their difference, which is what standing apart is. */
        @Override
        public LinearForm<NumericTerm> direction() {
            return LinearForm.difference(on.term(), against.term());
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
        public Stands standsAt(Criterion where, QuantityReading reading) {
            // Each end taken by its own orders, which is what the end is: a position read on the
            // other end's order is a value it does not hold, and the pair would stand a distance
            // apart that neither of them is at.
            WhatATermRead here = reading.of(on);
            WhatATermRead there = reading.of(against);
            // Both sides, and not the first of them. The pair is unreadable for whatever stopped
            // either, and a reader told about one end is being told which end this happened to
            // look at first.
            Set<ReadingGap> stopped = new java.util.LinkedHashSet<>();
            boolean wroteNothing = false;
            for (WhatATermRead end : List.of(here, there)) {
                switch (end) {
                    case WhatATermRead.CameToNothing(ReadingGap why) -> stopped.add(why);
                    case WhatATermRead.NothingWrittenThere _ -> wroteNothing = true;
                    case WhatATermRead.NoNumberOfTheValue _, WhatATermRead.Number _ -> { }
                }
            }
            // A row that wrote nothing at one end has no pair to stand anywhere, whatever the other
            // end came to. Answered after the reasons instead, a row that settles the point would
            // leave it open because the end nobody needed was unreadable.
            if (wroteNothing) {
                return Stands.NO;
            }
            Stands unread = Stands.couldNotTell(stopped);
            if (unread != null) {
                return unread;
            }
            // Which leaves the numbers to take out, the ends having been told apart above.
            if (!(here instanceof WhatATermRead.Number onAt)
                    || !(there instanceof WhatATermRead.Number againstAt)) {
                return Stands.NO;
            }
            if (!counts()) {
                // No number between them, and an order all the same. The only level such a quantity
                // takes is the one where they meet, so what the item asks is which way round they
                // stand from it.
                return holdsByOrder(where, onAt.value().compareTo(againstAt.value()))
                        ? Stands.YES : Stands.NO;
            }
            // The distance is a level of the quantity and is never put on a carrier, so it stays the
            // exact number it is. Where this cannot hold that number the pair stands somewhere this
            // did not work out, which is neither at the item nor away from it.
            ExactAnswer<ExactRatio> apart = Count.number(onAt.value()).exactly()
                    .minus(Count.number(againstAt.value()).exactly());
            if (apart instanceof ExactAnswer.Unheld<ExactRatio> unheld) {
                return Stands.couldNotTell(ReadingGap.of(unheld.why()));
            }
            return where.holds(new Level.OfTheQuantity(apart.orNull())) ? Stands.YES : Stands.NO;
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
                        new Level.OfTheQuantity(ExactRatio.of(order)));
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
                return new Standing.OfTwoOnOneCarrier(onTerm(), againstTerm(), onCarrier(), where);
            }
            return new Standing.OfAForm(
                    LinearForm.difference(on.term(), against.term()),
                    Map.of(on.term(), on.answered(), against.term(), against.answered()),
                    levels(), where);
        }

        @Override
        public String named() {
            return new AxisId(behavior, onTerm().toString()).toString();
        }

        @Override
        public String left() {
            return onTerm().toString();
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
            ExactRatio apart = level.asAnExactNumber();
            String there = againstTerm().toString();
            return apart.signum() == 0 ? there
                    : apart.signum() < 0 ? there + " - " + apart.negated().spelled()
                            : there + " + " + apart.spelled();
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
            implements LinearQuantity {

        /** Walked by what each term is called, which is what a form's own equality cannot see. */
        @Override
        public List<NumericTerm> terms() {
            return NumericTerms.inOrder(form.coefs().keySet());
        }

        @Override
        public LinearQuantity movedTo(NumericTerm from, TermOrders to) {
            NumericTerm landed = to.term();
            if (!form.coefs().containsKey(from) || form.coefs().containsKey(landed)) {
                return null;
            }
            Map<NumericTerm, ExactRatio> coefs = new java.util.LinkedHashMap<>();
            form.coefs().forEach((term, coef) -> coefs.put(term.equals(from) ? landed : term, coef));
            Map<NumericTerm, TermOrders> moved = new java.util.LinkedHashMap<>();
            on.forEach((term, its) -> moved.put(term.equals(from) ? landed : term,
                    term.equals(from) ? to : its));
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
                        + " of them is read on one order: "
                        + NumericTerms.inOrder(form.coefs().keySet())
                        + " against " + NumericTerms.inOrder(on.keySet()));
            }
            // And each entry's orders are that position's own. The key set agreeing says the map
            // is about the right positions and says nothing about which of them each answer came
            // from: a table with the two ends swapped has exactly the same keys.
            on.forEach((term, orders) -> orders.areOf(term));
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
            ExactRatio step = LevelSpace.stepOf(form.coefs().values());
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
            return LevelSpace.addedUpOver(NumericTerms.inOrder(on.keySet()).stream()
                    .map(term -> on.get(term).answered()).toList());
        }

        /** The order that position is read and written on, and null for a position not in the
         *  form. */
        @Override
        public TermOrders ordersOf(NumericTerm asked) {
            return on.get(asked);
        }

        /** The form itself, which is what it weighs its positions by. */
        @Override
        public LinearForm<NumericTerm> direction() {
            return form;
        }

        @Override
        public Stands standsAt(Criterion where, QuantityReading reading) {
            ExactRatio at = ExactRatio.ZERO;
            // Every term before anything is concluded. What stopped a reading is collected over the
            // whole form rather than taken from whichever term the map handed over first: the form
            // is unreadable for whatever stopped any of it, and stopping at the first said which
            // term this walk happened to begin with. A term that read as no number at all is held
            // until then for the same reason — a form with one of each is one nothing could read,
            // and answering that it does not stand would be this compiler's own gap said as the
            // model's answer.
            Set<ReadingGap> stopped = new java.util.LinkedHashSet<>();
            boolean noNumber = false;
            boolean wroteNothing = false;
            for (Map.Entry<NumericTerm, ExactRatio> each
                    : NumericTerms.entriesInOrder(form.coefs())) {
                // Taken by the orders this form reads that term on. What the term read is the
                // reading's to say and what it is worth to the number is the form's, and a
                // coefficient put against a value read on another order weighs a position by a
                // number it does not hold.
                switch (reading.of(on.get(each.getKey()))) {
                    case WhatATermRead.CameToNothing(ReadingGap why) -> stopped.add(why);
                    case WhatATermRead.NoNumberOfTheValue _ -> noNumber = true;
                    case WhatATermRead.NothingWrittenThere _ -> wroteNothing = true;
                    case WhatATermRead.Number(Place value) -> {
                        // A term of the sum a fine decimal makes, weighed against the terms already
                        // summed, can put the exact sum out of this arithmetic's reach — the same way
                        // a distance of two row values can (see the try/catch above). Held here as
                        // one more reason nothing could be said, rather than let it end the compile.
                        switch (Count.number(value).exactly().times(each.getValue()).flatMap(at::plus)) {
                            case ExactAnswer.Held<ExactRatio> held -> at = held.value();
                            case ExactAnswer.Unheld<ExactRatio> unheld ->
                                    stopped.add(ReadingGap.of(unheld.why()));
                        }
                    }
                }
            }
            // Every term, and the answer after them. Left as soon as one of these was known, the
            // terms behind it would go unasked — and asking them is how the measure finds out how
            // many elements each position holds, which is what says how many readings of the row
            // there are to try. A quantity that answered early would be choosing the readings.
            //
            // A term whose position the row wrote nothing at leaves the form no value at this row,
            // and that is the row's answer rather than a reading that came to nothing. It outranks
            // the reasons for the reason it is not one of them: those are what this compiler could
            // not find out, and this is what the row says.
            if (wroteNothing) {
                return Stands.NO;
            }
            Stands unread = Stands.couldNotTell(stopped);
            if (unread != null) {
                return unread;
            }
            if (noNumber) {
                return Stands.NO;
            }
            return where.holds(new Level.OfTheQuantity(at)) ? Stands.YES : Stands.NO;
        }

        @Override
        public Standing standingAt(Criterion where) {
            return new Standing.OfAForm(form, LinearQuantity.answeredOn(on), levels(), where);
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
            return OrderedAffineBoundary.spelled(form.coefs());
        }

        @Override
        public String writtenAt(Level level) {
            if (!(level instanceof Level.OfTheQuantity counted)) {
                throw new IllegalStateException(
                        "a form was asked to write a level that is not a number: " + level);
            }
            return counted.at().spelled();
        }

        @Override
        public BoundaryTarget.Shape shape() {
            return BoundaryTarget.Shape.OVER_A_FORM;
        }

    }

    /**
     * How many elements of a container meet a statement: a whole number from none to as many as
     * the container holds.
     *
     * <p>No form over a row's numbers. It turns on every element and on whatever else the
     * statement names — {@code x > limit} reads {@code limit} beside each element — so a row is
     * read at it whole, element by element, and a line on it divides no position.
     *
     * <p>One quantity wherever it is written: the same container and the same statement are the
     * same count, however the statement's element was named ({@link Quantity.HowManyMeet}).
     */
    final class HowMany implements BorderQuantity {

        private final String behavior;
        private final TermPath container;
        private final Proposition meeting;
        private final AStatementAtARow perElement;

        /**
         * @param container  the container the elements are counted in
         * @param meeting    what an element is counted for meeting, over the element's own
         *                   numbers and the input's
         * @param perElement {@code meeting} put to rows, which is what an element is asked
         */
        HowMany(String behavior, TermPath container, Proposition meeting,
                AStatementAtARow perElement) {
            if (behavior == null || container == null || meeting == null || perElement == null) {
                throw new IllegalArgumentException("a count is a behavior's count of the elements"
                        + " of some container meeting something");
            }
            this.behavior = behavior;
            this.container = container;
            this.meeting = meeting;
            this.perElement = perElement;
        }

        /** The container the elements are counted in. */
        public TermPath container() {
            return container;
        }

        /** What an element is counted for meeting. */
        public Proposition meeting() {
            return meeting;
        }

        @Override
        public String behavior() {
            return behavior;
        }

        /** Every whole number; that none is the least is what the rules leave it
         *  ({@link #runsWithin}). */
        @Override
        public LevelSpace levels() {
            return LevelSpace.steppingBy(ExactRatio.ONE);
        }

        /**
         * Where the count stands at a row, read off every element of the container.
         *
         * <p>An element the statement could not be read at is neither counted nor left out: the
         * count is somewhere between the elements that meet it and those together with every
         * element nothing could say of. The row stands at the item only where every number in
         * that run does, and stands away from it only where none does; between the two it could
         * not be told, and an unread element is never counted as one that fails.
         */
        @Override
        public Stands standsAt(Criterion where, Observation row) {
            AStatementAtARow.HowManyAtARow counted = perElement.howManyMeetIn(container, row);
            if (counted == null) {
                return Stands.couldNotTell(ReadingGap.COULD_NOT_WALK);
            }
            return switch (counted.whether(count -> ExactAnswer.held(
                    where.holds(new Level.OfTheQuantity(ExactRatio.of(count)))))) {
                case AStatementAtARow.Answer.Holds _ -> Stands.YES;
                case AStatementAtARow.Answer.Fails _ -> Stands.NO;
                case AStatementAtARow.Answer.CouldNotTell(var why) -> Stands.couldNotTell(why);
            };
        }

        /**
         * The container, and every number the statement reads beside an element.
         *
         * <p>Not the elements one at a time: they are read together for the count, and a walk
         * finding containers would otherwise take the counted container for one whose elements
         * are each a reading of the row.
         */
        @Override
        public void lookAt(Observation row) {
            row.eachElementOf(container);
            perElement.lookAt(row, Set.of(container));
        }

        @Override
        public Standing standingAt(Criterion where) {
            return new Standing.OfACount(container, meeting, numbers(), where);
        }

        @Override
        public String named() {
            return new AxisId(behavior, left()).toString();
        }

        /** The count as an author would read it: the container, and what its elements meet. */
        @Override
        public String left() {
            return "#" + container + " [" + said(meeting) + "]";
        }

        /** A statement over the input's own numbers, written the way a comparison is. */
        private static String said(Proposition stated) {
            return switch (stated) {
                case Proposition.Always(boolean holds) -> String.valueOf(holds);
                case Proposition.All all -> all.parts().stream().map(HowMany::grouped)
                        .collect(java.util.stream.Collectors.joining(" && "));
                case Proposition.Any any -> any.parts().stream().map(HowMany::grouped)
                        .collect(java.util.stream.Collectors.joining(" || "));
                case Proposition.Some some -> (some.holds() ? "some " : "no ") + some.container()
                        + " [" + said(some.ofTheElement()) + "]";
                case Proposition.Compared compared -> switch (compared.relation()) {
                    case Relation.Affine affine -> {
                        LinearForm<NumericTerm> form = WhatTheRulesLeave.ofTheInput(affine.form());
                        Rel rel = compared.holds() ? affine.proposition()
                                : affine.proposition().denied();
                        Quantity.HowManyMeet count = AStatementAtARow.countIn(affine);
                        // The count's weight is above nought, a relation facing the one way.
                        if (form == null && count != null) {
                            ExactRatio weight = affine.form().coefs().get(count);
                            yield "#" + count.container() + " [" + said(count.ofTheElement())
                                    + "] " + written(rel) + " "
                                    + affine.form().constant().negated().dividedBy(weight)
                                            .map(ExactRatio::spelled).orNull();
                        }
                        yield form == null ? stated.key()
                                : OrderedAffineBoundary.spelled(form.coefs()) + " " + written(rel)
                                        + " " + form.constant().negated().spelled();
                    }
                    case Relation.Ordered ordered -> ordered.term().spelled() + " "
                            + written(compared.holds() ? ordered.proposition()
                                    : ordered.proposition().denied())
                            + " " + ordered.at().spelled();
                };
                default -> stated.key();
            };
        }

        /** A part of a joined statement, bracketed where it is a join itself. */
        private static String grouped(Proposition part) {
            return part instanceof Proposition.All || part instanceof Proposition.Any
                    ? "(" + said(part) + ")" : said(part);
        }

        private static String written(Rel rel) {
            return switch (rel) {
                case EQ -> "==";
                case NE -> "/=";
                case LT -> "<";
                case LE -> "<=";
                case GT -> ">";
                case GE -> ">=";
            };
        }

        @Override
        public String writtenAt(Level level) {
            if (!(level instanceof Level.OfTheQuantity counted)) {
                throw new IllegalStateException(
                        "a count was asked to write a level that is not a number: " + level);
            }
            return counted.at().spelled();
        }

        @Override
        public BoundaryTarget.Shape shape() {
            return BoundaryTarget.Shape.COUNT_OF_ELEMENTS;
        }

        @Override
        public boolean equals(Object other) {
            return other instanceof HowMany that && behavior.equals(that.behavior)
                    && container.equals(that.container) && meeting.equals(that.meeting)
                    && perElement.equals(that.perElement);
        }

        @Override
        public int hashCode() {
            return java.util.Objects.hash(behavior, container, meeting, perElement);
        }

        @Override
        public String toString() {
            return "HowMany[" + behavior + ": " + left() + "]";
        }
    }

    /** How this quantity's own values are ordered, and which of them it can take. */
    LevelSpace levels();

    /**
     * Whether a bound on this quantity is what stops the range the rules leave it.
     *
     * <p>What a position holds is what its own declarations leave it, so a bound on it is that
     * range's end and the two are one fact read twice — which is what lets a reader hold them
     * against each other. What a rule relating positions cuts runs between whatever their ranges
     * leave it: {@code a - b} over two fields each stopping at ten runs from minus ten to ten
     * whatever any rule about the pair says, and a rule cutting it at zero cuts inside that. Held
     * to the same reading, every relation a model states would be refused as a bound that stops
     * short of its own line.
     */
    default boolean aBoundOnItEndsItsRange() {
        return switch (this) {
            case OfACoordinate _ -> true;
            // What a count runs between is none to as many as the container holds, whatever any
            // rule about the count says.
            case Apart _, OverAForm _, HowMany _ -> false;
        };
    }

    /**
     * What a row standing at {@code where} asks of each of the terms this is taken of.
     *
     * <p><b>The item is about this quantity, and only one kind of quantity is a term's own
     * values.</b> Where a row's number is one position's, what the item leaves the quantity is what
     * it leaves that position and a search of it may run to the end of that. Where the number is
     * taken of several — how far two of them stand apart, what a form of them comes to — the item
     * says one thing about the several: either term may take any number the others leave room for,
     * so what is left of it on its own is every number the order has and the item travels whole.
     *
     * <p>Which is why an item holding one number is not each term holding one. The rules leaving a
     * distance at exactly ten leave the near position wherever the far one is ten from, and a
     * search that tried one such pair has tried one — the pair the solver picked. Read off the
     * item, the same search would have walked every value there is of both.
     *
     * <p>Asked here because which quantity this is is asked nowhere else, and this is one more
     * answer a quantity added has to give rather than an arm downstream.
     */
    default NumbersAskedFor asksOfEachTerm(Criterion where) {
        return switch (this) {
            case OfACoordinate _ -> NumbersAskedFor.of(where.region());
            case Apart _, OverAForm _, HowMany _ ->
                    NumbersAskedFor.onlyTogether(new QuantityInRegion(this, where.region()));
        };
    }

    /** What a search has to solve to put a row at one item. */
    Standing standingAt(Criterion where);

    /**
     * Whether the row {@code row} is a reading of stands at one item of a border on this quantity,
     * or whether it could not be read.
     *
     * <p>What the row is read for is each quantity's own: a form reads one number per term, and a
     * count of the elements meeting something reads each element of its container.
     */
    Stands standsAt(Criterion where, Observation row);

    /**
     * Reads {@code row} the way {@link #standsAt} does and asks nothing of what it read, for the
     * walk that finds which containers this quantity's numbers stand inside.
     *
     * <p>What it reads is not this walk's to know: which containers there are says how many
     * readings of the row to try, and a quantity that left off early would be choosing them.
     */
    void lookAt(Observation row);

    /**
     * What makes two quantities one quantity, as a name a map can hold — or null where nothing
     * does: a form whose coefficients over what they share no ratio holds has no smallest form to
     * be named by, and a line on it is refused where lines are drawn.
     *
     * <p>A form is named by its smallest multiple ({@link QuantityKey}), since a form and its
     * multiples order the rows the same way.
     */
    default String identity() {
        return switch (this) {
            case LinearQuantity form -> {
                QuantityKey key = QuantityKey.tryOf(form.direction());
                yield key == null ? null : key.key();
            }
            case HowMany count -> count.left();
        };
    }

    /**
     * How much of the quantity a level written in a rule's own terms is, which is what such a
     * level divides by to be one of the quantity's own values ({@link QuantityKey#per}).
     */
    default ExactRatio per() {
        return switch (this) {
            case LinearQuantity form -> QuantityKey.per(form.direction());
            case HowMany _ -> ExactRatio.ONE;
        };
    }

    /**
     * Every number of a row this quantity is read from.
     *
     * <p>A form's terms, which are what it weighs. A quantity that is no form is still read from
     * numbers of the row, and a reader asking which numbers a row has to settle together to stand
     * at an item asks this and not which terms there are.
     */
    default List<NumericTerm> numbers() {
        return switch (this) {
            case LinearQuantity form -> form.terms();
            case HowMany count -> count.perElement.numbers();
        };
    }

    /** What the rules leave this quantity: the least and most it comes to over the rows they
     *  admit. */
    default NumericDomain.Bounds runsWithin(Quantities quantities) {
        return switch (this) {
            case LinearQuantity form -> quantities.runsBetween(form.direction());
            case HowMany _ -> NONE_OR_MORE;
        };
    }

    /** What a count of elements runs between: none at the least, and no most it is told. */
    NumericDomain.Bounds NONE_OR_MORE = new NumericDomain.Bounds(Endpoint.inclusive(Count.of(0)),
            null);

    /** What {@code region} leaves this quantity, or that it leaves it nothing. */
    default NumericDomain.FormProjection projectedIn(SearchRegion region) {
        return switch (this) {
            case LinearQuantity form -> region.projectionOf(form.direction());
            // A region holds relations over a row's numbers, and no relation it holds is about a
            // count of elements: it leaves the count what a count runs between.
            case HowMany _ -> new NumericDomain.FormProjection.Within(NONE_OR_MORE);
        };
    }

    /**
     * Where a rule about this quantity is filed, as a reader is sent to it: the numbers it is
     * taken of, in the order a document names them ({@link AffineReading#filedAt}).
     */
    default List<FilingCoordinate> filedAt() {
        return switch (this) {
            case LinearQuantity form -> AffineReading.filedAt(form.direction().coefs().keySet());
            case HowMany _ -> AffineReading.filedAt(numbers());
        };
    }

    /**
     * Whether a value a rule singles out on this quantity, where no position is divided to hold it
     * as a class, still has values beside it a row can be owed at.
     *
     * <p>A count does: it is one number, and the counts either side of the one named are the
     * nearest rows that do not meet it, as the values either side of a position's singled value
     * are. A form over several positions does not: where it comes to the value named is reached
     * by every way its positions can be written, and the rows either side of it are one class.
     */
    default boolean singlesWithSides() {
        return switch (this) {
            case LinearQuantity _ -> false;
            case HowMany _ -> true;
        };
    }

    /** Whether this is a number read over a run of values rather than a form over positions,
     *  which is a different thing to tell a reader who found no partition. */
    default boolean readOverARun() {
        return switch (this) {
            case LinearQuantity form -> form.direction().coefs().keySet().stream()
                    .anyMatch(term -> term.atOnePosition() == null);
            case HowMany _ -> true;
        };
    }

    /**
     * The order this quantity's values are written back on, where it is one term's — a position's
     * own values, or a number taken of one — and null where it is not.
     */
    default Carrier writtenBackOn() {
        return switch (this) {
            case LinearQuantity form -> form.direction().coefs().size() == 1
                    ? form.carrierOf(form.direction().coefs().keySet().iterator().next()) : null;
            case HowMany _ -> null;
        };
    }

    /**
     * Which behavior's input this quantity is of.
     *
     * <p>Every quantity is some behavior's: a coordinate is a position of one, and a distance or a
     * form is over positions of one. Asked here so that a reading of a line has one answer to which
     * behavior read it, rather than a second copy of this beside the target that nothing checks
     * agrees with it.
     */
    String behavior();

    /** The left of the {@code left = right} a report names a border on this by, qualified by the
     *  behavior it is an input of ({@link #behavior}). */
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
    default String left(ExactRatio times) {
        if (this instanceof OverAForm form && !times.equals(ExactRatio.ONE)) {
            LinearForm<NumericTerm> scaled = form.form().times(times).orNull();
            // A form whose numbers no ratio holds once scaled has no coefficients to write out, and
            // is named the way any other quantity is: by how many of it.
            if (scaled != null) {
                return new OverAForm(form.behavior(), scaled, form.on()).left();
            }
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
    static String times(ExactRatio times, String left) {
        return times.equals(ExactRatio.ONE) ? left : times.spelled() + " * " + left;
    }

    /** One level of this quantity, as a report writes it. */
    String writtenAt(Level level);

    /**
     * Whether {@link #writtenAt} says the same thing at every reading of one line.
     *
     * <p><b>What a debt may be written from.</b> A line an {@code invariant} drew is owed once for
     * the module and is read at every position the type reaches, so a sentence about the debt may
     * hold nothing that differs between those readings. Two of the three quantities write a level
     * as a number or as a value of a carrier, and neither of those is a reading's; one writes it as
     * a distance from another position, and what that position is called is the path a walk reached
     * it by.
     *
     * <p>So this says whether there is a declaration-relative wording at all — not whether two
     * readings happen to agree. The readings of a difference disagree because the answer is a
     * reading's, which is a fact about the quantity and is known without asking any of them; a
     * report that compared the spellings and refused where they differed was asking whether the
     * model was written a certain way and getting an answer about which position a walk met first
     * (issue #1251).
     *
     * <p>Exhaustive here, so a quantity added decides this rather than being read as one of the
     * others by a reader that guessed. Saying yes wrongly puts one reading's position into a
     * sentence about a line; saying no wrongly leaves a value unsaid that could have been said, and
     * only the first of those is a report claiming something.
     */
    default boolean statesADeclarationRelativeLevel() {
        return switch (this) {
            // A carrier's own value, which the type declares. The same at every reading, since what
            // it writes is the value and not where the value stands.
            case OfACoordinate _ -> true;
            // A number the form comes to, likewise the form's and not a position's.
            case OverAForm _ -> true;
            // How far from the other position, whose name is the path this reading reached it by.
            // A declaration has no name for it: the rule relates two positions and places no end,
            // so nothing about the pair is kept in the declaration's own terms (ADR-0090).
            case Apart _ -> false;
            // How many, which is the count's and not a position's.
            case HowMany _ -> true;
        };
    }

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

    /**
     * Whether a row is at an item, where a row that could not be read is neither.
     *
     * <p>The third carries what stopped the reading, because that is a fact about this compiler's
     * observation and never one about the model. Answered without it, a reader is left to work out
     * from what it has why there was nothing to compare — and what it has is the absence of a
     * number, which reads exactly like a number that did not match.
     */
    sealed interface Stands {

        /** The values stand at the item. */
        record Yes() implements Stands {}

        /** They were read, and they do not. */
        record No() implements Stands {}

        /**
         * There was no number to compare, and this is every reason there was none.
         *
         * <p>More than one where the quantity reads more than one term: a rule relating two
         * positions and a form over several come to nothing for whatever stopped any of them, and
         * naming one would be picking which of them a reader is told about. Which is as true of the
         * two kinds of reason as it is of two observations, so both kinds are in the set and
         * neither is chosen over the other ({@link ReadingGap}).
         */
        record CouldNotTell(Set<ReadingGap> why) implements Stands {

            public CouldNotTell {
                if (why == null || why.isEmpty()) {
                    throw new IllegalArgumentException(
                            "a reading nothing could be made of says what stopped it");
                }
                // In the order they were met, because a report prints them and a report that
                // changes between runs cannot be compared between runs.
                why = java.util.Collections.unmodifiableSet(new java.util.LinkedHashSet<>(why));
            }
        }

        Stands YES = new Yes();

        Stands NO = new No();

        /** Come to nothing for one reason, which is what a quantity reading one term has. */
        static Stands couldNotTell(ReadingGap why) {
            return new CouldNotTell(Set.of(why));
        }

        /** The same over several terms, or null where nothing stopped any of them. */
        static Stands couldNotTell(Set<ReadingGap> why) {
            return why.isEmpty() ? null : new CouldNotTell(why);
        }
    }

    /** What one row holds at each of a behavior's positions, for a quantity reading its own value
     *  off it. Handed in rather than reached for: which rows there are and how a value is found in
     *  one belong to the measure, and a quantity only asks what stands at a path. */
    interface Observation {

        /**
         * What stands at {@code path}, for a number taken of what is there.
         *
         * <p>The walk's own answer first, because a position this compiler could not walk to is not
         * a position a row holds nothing at. What a reading of a number does about the two differs,
         * and a measure handing back one shape for both would settle that here, where nothing knows
         * enough to.
         */
        WalkResult<ObservationAtPoint> at(TermPath path);

        /**
         * Every value standing at {@code path}, for a number taken over a run of them.
         *
         * <p>Beside {@link #at} and not instead of it. What a row holds at a place inside a
         * container is as many values as it wrote, and which question is being asked decides what to
         * do with them: a rule relating two positions is about one element and picks, and a rule
         * about what they add up to is about all of them and does not. Answered by one method, the
         * caller that wanted one would be handed a list to choose from and the choosing would move
         * to whoever asked — which is the reading of a row being made twice.
         *
         * <p>Under the same walk as {@link #at}, and holding none where the row wrote no element. A
         * total over nothing is what a run starts from rather than a value nobody could read, so
         * there is nothing here for a row that wrote an empty container to be told apart as.
         */
        WalkResult<java.util.List<ObservedValue>> everyValueAt(TermPath path);

        /**
         * One observation per element of the container at {@code container}, each the row with
         * that element chosen and whatever this one chose of the other containers.
         *
         * <p>For a number taken of the elements together, each read as one element. Beside
         * {@link #everyValueAt}, which hands back the values at one path: a statement about an
         * element reads several of its paths, and read path by path, the values of one element
         * would be paired with another's.
         *
         * <p>Under the same walk as {@link #at}. A container the row wrote empty, or wrote nothing
         * at, has no elements to read.
         */
        WalkResult<java.util.List<Observation>> eachElementOf(TermPath container);
    }
}
