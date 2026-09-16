package souther.compiler.query;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Place;
import souther.compiler.numeric.Towards;
import souther.compiler.partition.OrderedAffineBoundary;
import souther.compiler.partition.QuantityKey;
import souther.compiler.partition.StandingAtAPoint;

import java.math.BigDecimal;
import java.math.RoundingMode;
import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Whether the rows say where a line is, or only that it is somewhere near.
 *
 * <p>The four points of a border are met by rows standing where the line is and beside it, and a
 * border all four of whose points are met has been shown not to have moved. It has not been shown
 * not to have turned: every row can stand exactly where the model says and stand in the same place
 * under a line weighing a position differently, and then no row written answers differently under
 * either. That is what this asks, and it asks it of the lines the model's own weights put one step
 * away ({@link FaultFamily}).
 *
 * <p><b>A line the rows allow is named, and never inferred.</b> What establishes one is a threshold
 * that keeps every row on the side the model puts it on — so the answer carries the line it found,
 * and the input the two part company at where one could be worked out. A reader told only that a
 * border is not pinned down has been told to write more rows and not which.
 *
 * <p><b>And the walk that names one has to have read every row.</b> A row read is a constraint on
 * the lines the rows allow: reading more of them leaves fewer standing, never more. So a walk that
 * went without a row may say that nothing else stands — the rows it did read were enough — and may
 * not say that something does, because the row it went without is exactly what would have ruled it
 * out.
 *
 * <p><b>Four answers, and only one of them is about the model.</b> Two settle the question, one says
 * it was put and could not be settled, and {@link NoSuchQuestion} says there is no such question to
 * put. What goes in the last of those is a fact about the line itself — a line over one position has
 * no line one step from it — and never a limit of this compiler or of the strategy it was asked
 * under. A question this cannot answer, filed as a question that does not exist, is a verdict
 * settled on the strength of something nobody established.
 */
public sealed interface AnotherLineTheRowsAllow {

    /** The rows tell this line from every line one step from it. */
    record NoneDoes() implements AnotherLineTheRowsAllow {}

    /**
     * This one they do not, and this is where the two part company.
     *
     * @param direction   the line one step from the model's that every row answers alike under
     * @param cut         where along it the threshold falls that keeps every row where it is
     * @param tellsApartAt an input the two lines answer differently at, or null where none was
     *                    worked out. What a row there would show is the whole of the work this
     *                    names, so it is said wherever it can be
     */
    record OneDoes(QuantityKey direction, BigDecimal cut,
                   Map<NumericTerm, Place> tellsApartAt) implements AnotherLineTheRowsAllow {

        public OneDoes {
            if (direction == null || cut == null) {
                throw new IllegalArgumentException("a line the rows allow is a direction and a"
                        + " place along it: " + direction + " " + cut);
            }
            tellsApartAt = tellsApartAt == null ? null
                    : Collections.unmodifiableMap(new LinkedHashMap<>(tellsApartAt));
        }

        /** How a report names the line, which is the direction spelled as an author writes a form. */
        public String label() {
            return OrderedAffineBoundary.spelled(direction.direction()) + " = "
                    + cut.stripTrailingZeros().toPlainString();
        }

        /**
         * What the walk that named this went without, which is nothing.
         *
         * <p>Here so that a finding made from this takes what found it, as every finding does. The
         * condition is carried rather than the consequence: a line the rows allow is named only
         * where every reading of every row was read
         * ({@link StandingAtAPoint.RowsRead#everyOne}), and a walk that went without one comes back
         * as {@link CouldNotTell}. So there is nothing for a finding off this to be weakened by —
         * and a caller handing over some measure beside it would give this finding whatever another
         * line of the same behavior went without.
         */
        public WeakeningSet weakening() {
            return WeakeningSet.none();
        }
    }

    /**
     * The question was put and could not be settled, and this is what stopped it.
     *
     * <p>Apart from {@link NoSuchQuestion}, which is the nearest thing and is not this. There the
     * line has no line one step from it and nothing anybody writes changes that; here there is a
     * question, and what is missing is a reading, a strategy or a proof. Held as one arm, a
     * shortfall of this compiler's was published as a fact about the model, and a verdict rested on
     * it.
     *
     * <p><b>Only this arm weakens the measure.</b> A walk short of a row that still left no line
     * standing has settled the question: reading more rows leaves fewer lines standing, never more,
     * so what it established holds over every row it did not read. So being short is not what makes
     * a measure partial — coming back unsettled is, and a measure weakened by every partial walk
     * would hold a verdict open over a question that was answered.
     */
    record CouldNotTell(Unsettled why) implements AnotherLineTheRowsAllow {

        public CouldNotTell {
            java.util.Objects.requireNonNull(why, "a question not settled says what stopped it");
        }
    }

    /**
     * Why a question that was put could not be settled.
     *
     * <p>Each of these is a different thing to do about it, so each is its own shape rather than a
     * word in one list. What a reading went without is said in the vocabulary a reading answers in
     * ({@link souther.compiler.partition.ReadingGap}); what no strategy reaches is not a reading
     * that came to nothing, and a word shared between them would put a rule this compiler read in
     * full under the reason for one it could not read.
     */
    sealed interface Unsettled {

        /**
         * The rows were read in part, and a line beside this one still stands after them.
         *
         * <p>What a walk over rows went without is one value and there is one of it
         * ({@link ReadingReasons}) — the reasons each once in the order they are published in, and
         * whether the readings they were met in are all there were. A pair written again here would
         * be the same two facts under a second name, free to put them in another order.
         */
        record RowsIncomplete(ReadingReasons met) implements Unsettled {

            public RowsIncomplete {
                java.util.Objects.requireNonNull(met, "a walk says what it went without");
                if (met.eachKindOnce().isEmpty()
                        && met.tried() instanceof StandingAtAPoint.ReadingsTried.EveryOne) {
                    throw new IllegalArgumentException("a walk that went without nothing and read"
                            + " every reading there is read the rows in full, and this says it read"
                            + " them in part");
                }
            }
        }

        /**
         * Nothing was read against this line at all, and this is the reading that says why.
         *
         * <p>The reading's own answer, carried whole. What a measure over these lines is worth is
         * what that reading is worth, and a word invented here would be a second account of one
         * thing.
         */
        record TheRowsWereNotRead(Measurement<ItemAssessment.Coverage> as) implements Unsettled {

            public TheRowsWereNotRead {
                if (as instanceof Measurement.Complete) {
                    throw new IllegalArgumentException("a reading that was made is not why nothing"
                            + " was read: " + as);
                }
            }
        }

        /**
         * Every row this quantity has a value at falls on one side of the line.
         *
         * <p>So the rows pin no threshold on any line beside it, and every one of them stands.
         * Which is not a line this can name: what makes a line the rows allow nameable is a
         * threshold the rows themselves put it at, and rows all on one side put it nowhere. Said as
         * nothing standing, a border no row is beside would read as one the rows had pinned down.
         *
         * <p>A border all four of whose points are met never comes back this way, whichever side of
         * its line the value it names belongs to: one of the two points against the line satisfies
         * the rule and the other does not.
         */
        record TheRowsAreAllOnOneSide() implements Unsettled {}

        /**
         * There is a line beside this one and this compiler holds no border against it.
         *
         * <p>A limit of the strategy and not of the model. A rule that names a value divides the
         * quantity at the value it names, and weighing one of its positions differently is as much
         * a fault there as it is at a rule that orders the values — what is missing is a side to
         * keep a row on, which is a thing to write rather than a thing that does not exist.
         */
        record NoStrategyForIt(Strategy which) implements Unsettled {

            public NoStrategyForIt {
                java.util.Objects.requireNonNull(which, "a strategy that is missing is named");
            }
        }
    }

    /** Which shape of border this compiler holds against no line beside it. */
    enum Strategy {
        /** A rule that names a value rather than ordering the values around it. */
        A_RULE_THAT_NAMES_A_VALUE
    }

    /**
     * There is no line one step from this one, so there is nothing here to ask.
     *
     * <p>A fact about the line and about nothing else. Every reason below is one no row anybody
     * writes and no run allowing more would change — which is what makes this the one arm a settled
     * verdict may rest on.
     */
    record NoSuchQuestion(Reason why) implements AnotherLineTheRowsAllow {

        public NoSuchQuestion {
            java.util.Objects.requireNonNull(why, "a question that does not exist says why");
        }
    }

    /** Why a line has no line one step from it. */
    enum Reason {
        /** The line is on an order with no numbers under it — two strings stand one above the other
         *  and no distance apart — so there are no weights for another line to write differently. */
        THE_QUANTITY_HAS_NO_NUMBERS,
        /** The line is on one position, which has no line one step from it: weighed one less it is
         *  nothing, and weighed one more it is the same line. */
        THE_LINE_IS_ON_ONE_POSITION,
        /** No position of it is weighed by a number a model writes. A date counts from an origin
         *  nobody wrote, so a line weighing one of them two is a line nobody can state — such a
         *  border can shift and cannot turn. */
        NO_POSITION_OF_IT_IS_WEIGHED_BY_A_NUMBER
    }

    AnotherLineTheRowsAllow NONE_DOES = new NoneDoes();

    /**
     * What the rows leave standing beside {@code boundary}.
     *
     * <p>One pass over the family, and the first line the rows allow is the one named. They are as
     * many as the quantity has positions and each is a line a row would rule out; naming all of them
     * would put a reader in front of a list every entry of which is the same row to write.
     */
    static AnotherLineTheRowsAllow of(souther.compiler.partition.Border border,
                                      java.util.function.Supplier<StandingAtAPoint.RowsRead> read,
                                      List<OrderedAffineBoundary> elsewhere) {
        // The two ways a border is not a line another line can be written beside, told apart. A
        // rule that names a value orders nothing and has no side to keep a row on; a rule on an
        // order with no numbers has no weights to write differently. Read off one answer, either
        // would be published under the other's word.
        // What the line is, before what its rule states about it. Whether there is a line one step
        // from this one is the line's own answer and is the same whichever way the rule reads it —
        // so a bound on one position comes back as a question that does not arise, and never as one
        // this compiler declined to put.
        souther.compiler.partition.BorderQuantity of = border.cut().of();
        if (!OrderedAffineBoundary.weighable(of)) {
            return new NoSuchQuestion(Reason.THE_QUANTITY_HAS_NO_NUMBERS);
        }
        QuantityKey runs = QuantityKey.of(of.direction());
        if (runs.direction().size() == 1) {
            return new NoSuchQuestion(Reason.THE_LINE_IS_ON_ONE_POSITION);
        }
        Set<NumericTerm> weighed = OrderedAffineBoundary.weighedByANumber(of);
        if (weighed.isEmpty()) {
            return new NoSuchQuestion(Reason.NO_POSITION_OF_IT_IS_WEIGHED_BY_A_NUMBER);
        }
        List<QuantityKey> family = new FaultFamily(runs, weighed).others();
        if (family.isEmpty()) {
            // Weighed every way one step allows and every one of them is this line. There is
            // nothing to be told from, which is the same fact the reasons above are.
            return new NoSuchQuestion(Reason.THE_LINE_IS_ON_ONE_POSITION);
        }
        // And now the rule. There is a line one step from this one, and a rule that names a value
        // orders nothing — so it has no side to keep a row on and nothing here holds it against its
        // neighbours. A strategy nobody wrote, and not a question the model does not raise: the
        // second would settle a verdict on something nobody established.
        OrderedAffineBoundary boundary = OrderedAffineBoundary.of(border);
        if (boundary == null) {
            return new CouldNotTell(
                    new Unsettled.NoStrategyForIt(Strategy.A_RULE_THAT_NAMES_A_VALUE));
        }
        // The rows read here and not before. Reading them is a walk of its own over every row, and
        // every question above is about the line alone — so a border with no line beside it, which
        // is every bound on a position, pays nothing for being asked.
        StandingAtAPoint.RowsRead rows = read.get();
        List<Map<NumericTerm, Place>> satisfying = new ArrayList<>();
        List<Map<NumericTerm, Place>> refusing = new ArrayList<>();
        for (Map<NumericTerm, Place> values : rows.each()) {
            (boundary.satisfiedBy(values) ? satisfying : refusing).add(values);
        }
        // No row the rule keeps, so there is nothing a threshold on any other line has to keep, and
        // the tightest one there is falls below every row instead of at one of them — which is a
        // place this cannot name without a step of the other line's own. Where the rows are all on
        // the kept side the tightest threshold is the furthest of them, so that side is answered
        // below like any other.
        if (satisfying.isEmpty()) {
            return new CouldNotTell(new Unsettled.TheRowsAreAllOnOneSide());
        }
        for (QuantityKey other : family) {
            BigDecimal cut = keeping(other, boundary.satisfiedOn(), satisfying, refusing);
            if (cut == null) {
                continue;
            }
            if (!rows.everyOne()) {
                return new CouldNotTell(new Unsettled.RowsIncomplete(
                        ReadingReasons.of(rows.why(), rows.tried())));
            }
            return new OneDoes(other, cut,
                    partingAt(boundary, other, cut, satisfying, refusing, elsewhere));
        }
        // Nothing stands, which the rows that were read establish however few of them there were:
        // a row read leaves fewer lines standing and never more, so a line none of these allows is
        // one none of the rest would have allowed either.
        return NONE_DOES;
    }

    /**
     * Where a threshold on {@code other} would have to fall to leave every row where the model puts
     * it, or null where no threshold does.
     *
     * <p>The tightest one there is: the far edge of the rows the model is satisfied by. Every row the
     * model keeps has to be kept, so the threshold is at least as far along as the furthest of them;
     * every row the model refuses has to be refused, so it is nearer than the nearest of those. Where
     * the first is past the second there is nowhere to put it, and the rows have told the two lines
     * apart.
     */
    private static BigDecimal keeping(QuantityKey other, Towards satisfiedOn,
                                      List<Map<NumericTerm, Place>> satisfying,
                                      List<Map<NumericTerm, Place>> refusing) {
        // Some row the rule keeps, which is settled before this is called. Asked without one, the
        // loop below would leave the threshold at nothing and read as a line the rows tell this one
        // from — which is the opposite of what such rows establish.
        if (satisfying.isEmpty()) {
            throw new IllegalArgumentException("a threshold that keeps none of the rows");
        }
        BigDecimal furthest = null;
        for (Map<NumericTerm, Place> values : satisfying) {
            BigDecimal at = OrderedAffineBoundary.along(other.direction(), values);
            furthest = furthest == null ? at : beyond(satisfiedOn, furthest, at);
        }
        for (Map<NumericTerm, Place> values : refusing) {
            BigDecimal at = OrderedAffineBoundary.along(other.direction(), values);
            // Strictly past the threshold, because the threshold itself is kept: a row the model
            // refuses that lands exactly there would be kept by this line, and the two would not
            // answer alike at it.
            if (satisfiedOn == Towards.BELOW ? at.compareTo(furthest) <= 0
                    : at.compareTo(furthest) >= 0) {
                return null;
            }
        }
        return furthest;
    }

    /** Whichever of the two is further along the side the rule is satisfied on. */
    private static BigDecimal beyond(Towards satisfiedOn, BigDecimal a, BigDecimal b) {
        return satisfiedOn == Towards.BELOW ? a.max(b) : a.min(b);
    }

    /**
     * An input the two lines answer differently at, or null where none was worked out.
     *
     * <p>Found by moving along the model's own line, which is what leaves its answer where it was
     * and moves the other one: a step that the model weighs to nothing is a step every row can take
     * without crossing it, and the two lines are not parallel, so the same step does cross the other
     * one. How many steps it takes is arithmetic and not a search.
     *
     * <p>Taken from a row and not from nowhere, so the input this names is one the rows already
     * reach. A step is whole numbers of each position's own units, and where a position has no value
     * at the number it lands on there is nothing here to name.
     *
     * <p><b>And the ones the model's other rules keep come first.</b> An input the two lines answer
     * differently at is a row that tells them apart, and a row whose answer another rule settles
     * before this line is consulted tells a reader nothing they can see — the two lines part company
     * there and the behavior answers the same either way. So the inputs every other line of this
     * behavior is satisfied at are preferred, and the nearest of those is named; where the rules
     * leave none, the nearest input of any kind is still an input the two part company at, and it is
     * said rather than nothing.
     */
    private static Map<NumericTerm, Place> partingAt(OrderedAffineBoundary boundary,
                                                     QuantityKey other, BigDecimal cut,
                                                     List<Map<NumericTerm, Place>> satisfying,
                                                     List<Map<NumericTerm, Place>> refusing,
                                                     List<OrderedAffineBoundary> elsewhere) {
        Map<NumericTerm, BigDecimal> along = alongTheLine(boundary.direction(), other);
        if (along == null) {
            return null;
        }
        BigDecimal moves = weighing(other, along);
        if (moves.signum() == 0) {
            return null;
        }
        // Every row, on whichever side of the line it is: which way a step has to go to cross the
        // other line depends on where the row already stands.
        List<Parting> found = new ArrayList<>();
        for (Map<NumericTerm, Place> values : satisfying) {
            partings(boundary, other, cut, values, along, moves, true, elsewhere, found);
        }
        for (Map<NumericTerm, Place> values : refusing) {
            partings(boundary, other, cut, values, along, moves, false, elsewhere, found);
        }
        return found.stream()
                .min(java.util.Comparator.comparingInt((Parting each) -> each.reached() ? 0 : 1)
                        .thenComparing(Parting::steps))
                .map(Parting::at).orElse(null);
    }

    /**
     * The inputs near one row that the two lines part company at.
     *
     * @param reached whether the model's other lines are satisfied there
     * @param steps   how far from the row it is, which is what makes one input nearer than another
     */
    record Parting(Map<NumericTerm, Place> at, boolean reached, BigDecimal steps) {}

    /** Whatever {@code values} reaches by stepping along the model's own line, collected into
     *  {@code found}. */
    private static void partings(OrderedAffineBoundary boundary, QuantityKey other, BigDecimal cut,
                                 Map<NumericTerm, Place> values,
                                 Map<NumericTerm, BigDecimal> along, BigDecimal moves,
                                 boolean kept, List<OrderedAffineBoundary> elsewhere,
                                 List<Parting> found) {
        BigDecimal at = OrderedAffineBoundary.along(other.direction(), values);
        for (BigDecimal steps
                : stepsAround(cut.subtract(at).divide(moves, 0, RoundingMode.DOWN))) {
            // Asked by standing at the input rather than by reasoning about which way the
            // arithmetic came out. Which side of its own threshold a value falls on is the same
            // question here as everywhere, and a number of steps worked out from the signs would be
            // a second answer to it, right until one of the four ways the signs can fall was
            // written down wrong.
            if (kept == keeps(boundary.satisfiedOn(), cut, at.add(steps.multiply(moves)))) {
                continue;
            }
            Map<NumericTerm, Place> moved = movedBy(boundary, values, along, steps);
            if (moved != null) {
                found.add(new Parting(moved, reachedBy(elsewhere, moved), steps.abs()));
            }
        }
    }

    /** Whether every other line of this behavior is satisfied at an input, which is what puts it
     *  where this line is what settles the answer. */
    private static boolean reachedBy(List<OrderedAffineBoundary> elsewhere,
                                     Map<NumericTerm, Place> at) {
        for (OrderedAffineBoundary each : elsewhere) {
            // A line over positions this input says nothing about is a line it does not reach past,
            // and is no reason to prefer one input over another.
            if (at.keySet().containsAll(each.direction().direction().keySet())
                    && !each.satisfiedBy(at)) {
                return false;
            }
        }
        return true;
    }


    /** Whether a line satisfied on {@code satisfiedOn} of {@code cut} keeps a value at {@code at}.
     *  The threshold's own value is kept, which is what makes it the tightest one there is. */
    private static boolean keeps(Towards satisfiedOn, BigDecimal cut, BigDecimal at) {
        return satisfiedOn == Towards.BELOW ? at.compareTo(cut) <= 0 : at.compareTo(cut) >= 0;
    }

    /**
     * The whole numbers of steps to try, nearest first.
     *
     * <p>The inputs a step reaches that the two lines answer differently at are every step past
     * where they cross, so the nearest of them is beside the crossing — which is what the quotient
     * names. Standing still is not among them: the rows already answer alike there, which is what
     * the threshold was chosen to make true.
     */
    private static List<BigDecimal> stepsAround(BigDecimal crossing) {
        List<BigDecimal> out = new ArrayList<>();
        for (int away = -2; away <= 2; away++) {
            BigDecimal steps = crossing.add(BigDecimal.valueOf(away));
            if (steps.signum() != 0) {
                out.add(steps);
            }
        }
        out.sort(java.util.Comparator.comparing(BigDecimal::abs));
        return out;
    }

    /** What a direction weighs a step to, where a step names only the positions it moves. */
    private static BigDecimal weighing(QuantityKey of, Map<NumericTerm, BigDecimal> step) {
        BigDecimal at = BigDecimal.ZERO;
        for (Map.Entry<NumericTerm, BigDecimal> each : step.entrySet()) {
            at = at.add(weight(of, each.getKey()).multiply(each.getValue()));
        }
        return at;
    }

    /**
     * A step the model's line weighs to nothing and {@code other} does not, in whole numbers of each
     * position's own units — or null where the two lines are not over numbers this can step in.
     *
     * <p>Two positions the two lines weigh differently are all it takes: weighing one by what the
     * model weighs the other, and the other by what the model weighs the first the other way round,
     * leaves the model's own weight of the pair at nothing. That the same step is not nothing under
     * {@code other} is what the two weighing them differently means.
     */
    private static Map<NumericTerm, BigDecimal> alongTheLine(QuantityKey wrote, QuantityKey other) {
        List<NumericTerm> terms = new ArrayList<>(named(wrote, other));
        for (int i = 0; i < terms.size(); i++) {
            for (int j = i + 1; j < terms.size(); j++) {
                BigDecimal mine = weight(wrote, terms.get(i));
                BigDecimal ours = weight(wrote, terms.get(j));
                BigDecimal turned = weight(other, terms.get(i)).multiply(ours)
                        .subtract(weight(other, terms.get(j)).multiply(mine));
                if (turned.signum() == 0 || !whole(mine) || !whole(ours)) {
                    continue;
                }
                Map<NumericTerm, BigDecimal> step = new LinkedHashMap<>();
                step.put(terms.get(i), ours);
                step.put(terms.get(j), mine.negate());
                return step;
            }
        }
        return null;
    }

    /** The row's positions moved {@code steps} steps along {@code step}, or null where one of them
     *  has no value where it lands. */
    private static Map<NumericTerm, Place> movedBy(OrderedAffineBoundary boundary,
                                                   Map<NumericTerm, Place> values,
                                                   Map<NumericTerm, BigDecimal> step,
                                                   BigDecimal steps) {
        Map<NumericTerm, Place> moved = new LinkedHashMap<>();
        for (Map.Entry<NumericTerm, Place> each : values.entrySet()) {
            BigDecimal by = step.getOrDefault(each.getKey(), BigDecimal.ZERO);
            BigDecimal at = Count.number(each.getValue()).at().add(by.multiply(steps));
            souther.compiler.check.Carrier carrier = boundary.of().carrierOf(each.getKey());
            Place there = carrier == null ? null : carrier.onTheGrid(new Count(at));
            if (there == null) {
                return null;
            }
            moved.put(each.getKey(), there);
        }
        return moved;
    }

    /** Every position either line is over, in an order the terms settle. Taken in the order a
     *  direction is held in, which pair of them a step is built from moves between runs, and so
     *  does the input a report names. */
    private static List<NumericTerm> named(QuantityKey wrote, QuantityKey other) {
        Set<NumericTerm> terms = new LinkedHashSet<>(wrote.direction().keySet());
        terms.addAll(other.direction().keySet());
        return terms.stream().sorted(java.util.Comparator.comparing(NumericTerm::toString))
                .toList();
    }

    private static BigDecimal weight(QuantityKey of, NumericTerm term) {
        return of.direction().getOrDefault(term, BigDecimal.ZERO);
    }

    private static boolean whole(BigDecimal at) {
        return at.stripTrailingZeros().scale() <= 0;
    }

}
