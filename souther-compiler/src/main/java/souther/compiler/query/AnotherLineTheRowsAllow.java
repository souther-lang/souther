package souther.compiler.query;

import souther.compiler.check.Carrier;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Place;
import souther.compiler.numeric.Rel;
import souther.compiler.numeric.Towards;
import souther.compiler.partition.Border;
import souther.compiler.partition.BorderQuantity;
import souther.compiler.partition.OnTheWay;
import souther.compiler.partition.OrderedAffineBoundary;
import souther.compiler.partition.QuantityKey;
import souther.compiler.partition.StandingAtAPoint;
import souther.compiler.partition.TakenConstraint;
import souther.compiler.partition.WayToTheBorder;

import java.math.BigDecimal;
import java.math.RoundingMode;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;

/**
 * Whether the rows say where a line is, or only that it is somewhere near.
 *
 * <p>The four points of a border are met by rows standing where the line is and beside it, and a
 * border all four of whose points are met has been shown not to have moved. Nothing about them
 * bears on how it runs: every row can stand exactly where the model says and stand in the same place
 * under a line weighing a position differently, and then no row written answers differently under
 * either. That is what this asks, and it asks it of the lines the model's own weights put one step
 * away ({@link FaultFamily}) — so what a border none of them survives beside has been shown is that
 * no fault of one step in one weight is left in it, and never that the line is where it is.
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
     * <p><b>What is missing here is a condition and not a place.</b> The inputs that would show
     * which of the two lines the model draws are every input this line keeps and the model's
     * refuses, and {@link #tellsApartAt} is one of them — the one the rows themselves lead to. A
     * search asked for the place would be held to whichever input the walk over the rows reached
     * first, and an input it cannot compose a row at would come back as work nobody can do while
     * the rest of the set went unlooked at. So the condition is what travels
     * ({@link #tellingThemApart}), and the place is what the measurement saw.
     *
     * @param direction   the line one step from the model's that every row answers alike under
     * @param cut         where along it the threshold falls that keeps every row where it is
     * @param keptOn      the side of that threshold this line keeps a row on, which is the side the
     *                    model's own rule is satisfied on
     * @param tellsApartAt an input the two lines answer differently at, or null where none was
     *                    worked out. What the measurement itself reached, and never where a row has
     *                    to be written: it is a witness of the condition and not the condition
     */
    record OneDoes(QuantityKey direction, BigDecimal cut, Towards keptOn,
                   Map<NumericTerm, Place> tellsApartAt) implements AnotherLineTheRowsAllow {

        public OneDoes {
            if (direction == null || cut == null || keptOn == null) {
                throw new IllegalArgumentException("a line the rows allow is a direction, a"
                        + " place along it and a side it keeps: " + direction + " " + cut + " "
                        + keptOn);
            }
            tellsApartAt = tellsApartAt == null ? null
                    : Collections.unmodifiableMap(new LinkedHashMap<>(tellsApartAt));
        }

        /**
         * Where a row that tells the two lines apart has to stand, as a refinement of {@code
         * within}.
         *
         * <p>Half of the condition and the half that is this line's. The other half is the model's
         * own line, which a row at its {@code OFF} point already satisfies by standing there — so a
         * row inside this region at that point is one the model refuses and this line keeps, which
         * is the whole of what tells them apart.
         *
         * <p>Which also says why the rows already written are outside it. {@code cut} is the
         * threshold that keeps every row the model keeps and refuses every row it refuses, so a row
         * in the file answers alike under both lines — a search handed the rows to avoid would be
         * listing what the condition already leaves out.
         */
        public SearchRegion tellingThemApart(SearchRegion within) {
            return within.assuming(new LinearForm<>(cut.negate(), direction.direction()),
                    keptOn == Towards.BELOW ? Rel.LE : Rel.GE);
        }

        /**
         * Whether this line keeps a row whose positions read as {@code values}.
         *
         * <p>The same question {@link OrderedAffineBoundary#satisfiedBy} puts to the line the model
         * drew, put to the line it did not. A row the two answer differently at is one that tells
         * them apart, which is the whole of what a row here is asked for — so both halves of that
         * are read the same way, and neither is an arrangement of the other.
         */
        public boolean keeps(Map<NumericTerm, Place> values) {
            return AnotherLineTheRowsAllow.keeps(keptOn, cut,
                    OrderedAffineBoundary.along(direction.direction(), values));
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
            Objects.requireNonNull(why, "a question not settled says what stopped it");
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
                Objects.requireNonNull(met, "a walk says what it went without");
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
         * A row was left out because nothing watched its run, so whether it reached the rule could
         * not be told.
         *
         * <p>Which is not a row that says nothing. A row that ran and never got an answer out of
         * this comparison is an answer about that row and is left out with nothing gone without;
         * this one may have reached and may not, and a line that stands after the rest of the rows
         * is one it might have ruled out.
         */
        record TheRunsWereNotWatched() implements Unsettled {}

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
         * A line beside this one stands after every row, and nothing here could show an input that
         * tells the two apart and reaches this rule.
         *
         * <p>Which is what a line beside this one has to have to be a fault anybody could show. Two
         * lines that part company only where the rules never send a row are one line as far as this
         * behavior is concerned, and naming the second of them would be asking for a row that shows
         * nothing. So an input is named only where the conditions on the way to the rule answer the
         * same at it as at a row that reached — and where one of them could not be read, or the
         * arithmetic does not come out in whole steps, this is what is left.
         */
        record NoReachableDistinguisher() implements Unsettled {}

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
                Objects.requireNonNull(which, "a strategy that is missing is named");
            }
        }
    }

    /** Which shape of border this compiler holds against no line beside it. */
    enum Strategy {
        /** A rule that names a value rather than ordering the values around it. */
        A_RULE_THAT_NAMES_A_VALUE
    }

    /**
     * The rows have not yet met the points of this border, so this question is not due.
     *
     * <p><b>The question after the points and never instead of them.</b> A border short of a row at
     * one of its points is already short of the rows that show where it falls, and what the rows
     * leave standing beside it is asked of a border every point of which a row is at. Asked sooner,
     * an author is given two sentences about one border, the second of which the first one's row may
     * well answer — and a border whose kept side the rules leave no value at would be held open on a
     * row nobody could ever write.
     *
     * <p>So this is settled without being answered, and weakens nothing: what the rows are short of
     * here is what the points say they are short of, said once, where it is owed.
     */
    record NotDueYet() implements AnotherLineTheRowsAllow {}

    /**
     * There is no line one step from this one, so there is nothing here to ask.
     *
     * <p>A fact about the line and about nothing else. Every reason below is one no row anybody
     * writes and no run allowing more would change — which is what makes this the one arm a settled
     * verdict may rest on.
     */
    record NoSuchQuestion(Reason why) implements AnotherLineTheRowsAllow {

        public NoSuchQuestion {
            Objects.requireNonNull(why, "a question that does not exist says why");
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

    AnotherLineTheRowsAllow NOT_DUE_YET = new NotDueYet();

    /**
     * What the rows leave standing beside {@code boundary}.
     *
     * <p>One pass over the family, and the first line the rows allow is the one named. They are as
     * many as the quantity has positions and each is a line a row would rule out; naming all of them
     * would put a reader in front of a list every entry of which is the same row to write.
     */
    static AnotherLineTheRowsAllow of(Border border,
                                      boolean everyPointMet,
                                      java.util.function.Supplier<StandingAtAPoint.RowsRead> read,
                                      List<OrderedAffineBoundary> elsewhere,
                                      WayToTheBorder way) {
        // The two ways a border is not a line another line can be written beside, told apart. A
        // rule that names a value orders nothing and has no side to keep a row on; a rule on an
        // order with no numbers has no weights to write differently. Read off one answer, either
        // would be published under the other's word.
        // What the line is, before what its rule states about it. Whether there is a line one step
        // from this one is the line's own answer and is the same whichever way the rule reads it —
        // so a bound on one position comes back as a question that does not arise, and never as one
        // this compiler declined to put.
        BorderQuantity of = border.cut().of();
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
        // And the rows have met its points. Asked sooner, a border the rows have not caught up with
        // would be held open on what the points already say — and one whose kept side the rules
        // leave no value at would be held open on a row nobody could ever write.
        if (!everyPointMet) {
            return NOT_DUE_YET;
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
            // What was gone without, in the words of the thing that went without it. A row nothing
            // watched and a reading that came to nothing are two different things to do about, so
            // the first is answered before the second rather than folded into the reasons a reading
            // answers in.
            if (rows.unwatched()) {
                return new CouldNotTell(new Unsettled.TheRunsWereNotWatched());
            }
            if (!rows.everyOne()) {
                return new CouldNotTell(new Unsettled.RowsIncomplete(
                        ReadingReasons.of(rows.why(), rows.tried())));
            }
            // And an input the two part company at that the rules do send a row to. A line this
            // one parts company with only where nothing arrives is the same line here, so it is no
            // fault and this walks on to the next; where nothing could show either, the question
            // stands rather than being answered by whichever way it fell.
            Map<NumericTerm, Place> parting =
                    partingAt(boundary, other, cut, satisfying, refusing, elsewhere, way);
            if (parting == null) {
                return new CouldNotTell(new Unsettled.NoReachableDistinguisher());
            }
            return new OneDoes(other, cut, boundary.satisfiedOn(), parting);
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
     * <p><b>And it has to be an input the rules send a row to.</b> Two lines that part company only
     * where nothing arrives at this rule are one line as far as this behavior goes, so naming the
     * second of them would be asking for a row that shows nothing. What says a step keeps the input
     * arriving is the way to the border: every condition on it has to answer the same at the input
     * as it did at the row the step began from, and that row arrived. A condition this compiler
     * could not take in is one nothing here can answer that of, so a way holding one names no input
     * at all.
     */
    private static Map<NumericTerm, Place> partingAt(OrderedAffineBoundary boundary,
                                                     QuantityKey other, BigDecimal cut,
                                                     List<Map<NumericTerm, Place>> satisfying,
                                                     List<Map<NumericTerm, Place>> refusing,
                                                     List<OrderedAffineBoundary> elsewhere,
                                                     WayToTheBorder way) {
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
        Reaches reaches = new Reaches(way, along.keySet());
        List<Parting> found = new ArrayList<>();
        for (Map<NumericTerm, Place> values : satisfying) {
            partings(boundary, other, cut, values, along, moves, true, reaches, elsewhere, found);
        }
        for (Map<NumericTerm, Place> values : refusing) {
            partings(boundary, other, cut, values, along, moves, false, reaches, elsewhere, found);
        }
        // Of the inputs the rules still send a row to, the one whose difference an author can see,
        // and the nearest of those. Reaching is the condition: an input the way turns away is not a
        // worse answer than another, it is no answer, because two lines answering differently where
        // no row arrives is not something a row could show. What the behavior's other lines do with
        // it is the preference beside that: where they keep it, this line is what settles the answer
        // there, and where they do not the two part company under a rule that has already decided.
        return found.stream().filter(Parting::reached)
                .min(Comparator.comparingInt((Parting each) -> each.visible() ? 0 : 1)
                        .thenComparing(Parting::steps))
                .map(Parting::at).orElse(null);
    }

    /**
     * The inputs near one row that the two lines part company at.
     *
     * @param reached whether a row still arrives at this rule there, which is the condition
     * @param visible whether the behavior's other lines keep it, so that what this line answers is
     *                what the behavior answers — the preference, and never the condition
     * @param steps   how far from the row it is, which is what makes one input nearer than another
     */
    record Parting(Map<NumericTerm, Place> at, boolean reached, boolean visible,
                   BigDecimal steps) {}

    /** Whatever {@code values} reaches by stepping along the model's own line, collected into
     *  {@code found}. */
    private static void partings(OrderedAffineBoundary boundary, QuantityKey other, BigDecimal cut,
                                 Map<NumericTerm, Place> values,
                                 Map<NumericTerm, BigDecimal> along, BigDecimal moves,
                                 boolean kept, Reaches reaches,
                                 List<OrderedAffineBoundary> elsewhere,
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
                found.add(new Parting(moved, reaches.stillArrives(values, moved),
                        keptByTheOthers(elsewhere, moved), steps.abs()));
            }
        }
    }

    /**
     * Whether the behavior's other lines are satisfied at an input.
     *
     * <p>A preference and never a condition. Where they are, this line is what settles what the
     * behavior answers there, so an author writing the row sees the two lines part company; where
     * they are not, the two still part company at the line and a rule that has already decided
     * covers it over. Both are inputs the two lines answer differently at, which is what the
     * sentence says — this only decides which of them is worth naming.
     */
    private static boolean keptByTheOthers(List<OrderedAffineBoundary> elsewhere,
                                           Map<NumericTerm, Place> at) {
        for (OrderedAffineBoundary each : elsewhere) {
            if (at.keySet().containsAll(each.direction().direction().keySet())
                    && !each.satisfiedBy(at)) {
                return false;
            }
        }
        return true;
    }

    /**
     * Whether a step from a row that arrived at this rule leaves the input still arriving.
     *
     * <p>Asked of the way to the border, which is every condition a row passed to get there. A
     * condition the step moves no position of answers at the input exactly what it answered at the
     * row, and the row arrived — so it holds, with nothing to work out. One the step does move a
     * position of has to be read at the input, which takes the input holding a number at every
     * position that condition is over.
     *
     * <p><b>And a condition nothing here took in turns every step away.</b> What such a way leaves
     * is not known to be what reaches the border — that is what {@link
     * WayToTheBorder} says of itself — so an input past it is one nothing
     * here can say a row arrives at. Read as arriving, a line two borders part company at somewhere
     * unreachable would be published as a fault, and the row asked for would show nothing.
     */
    final class Reaches {

        private final WayToTheBorder way;

        private final Set<NumericTerm> moved;

        Reaches(WayToTheBorder way, Set<NumericTerm> moved) {
            this.way = way;
            this.moved = Set.copyOf(moved);
        }

        boolean stillArrives(Map<NumericTerm, Place> from, Map<NumericTerm, Place> at) {
            for (OnTheWay each : way.onTheWay()) {
                switch (each) {
                    // Nothing here turned it into something a row can be held against, so nothing
                    // here can say whether the input still passes it.
                    case OnTheWay.Declined _ -> {
                        return false;
                    }
                    // Which case a value turned out to be. A step moves numbers and a narrowing is
                    // about a position being one of its cases, so a step that moves no number of
                    // that position leaves it as the row had it; one that does is past what this
                    // reads.
                    case OnTheWay.Narrowed(var _, var position) -> {
                        if (moved.stream().anyMatch(term -> term.subjectPath().equals(position))) {
                            return false;
                        }
                    }
                    case OnTheWay.TakenIn(var _, var taken) -> {
                        if (Collections.disjoint(taken.terms(), moved)) {
                            continue;   // the row's answer at it, unmoved
                        }
                        Boolean holds = holdsAt(taken, from, at);
                        if (holds == null || !holds) {
                            return false;
                        }
                    }
                }
            }
            return true;
        }
    }

    /**
     * Whether a condition still holds at an input a step reached, or null where nothing here can
     * say.
     *
     * <p>Where the input holds a number at every position the condition is over, it is read there
     * and that is the answer. Where it does not, the condition is still decidable without those
     * numbers more often than not: the row it was stepped from passed the condition, the step moves
     * only the positions the border is over, and what the step does to the condition is a number
     * this can work out from the step alone — the positions it does not move cancel.
     *
     * <p>So a condition satisfied below nought that the step moves down is still satisfied, and one
     * satisfied at nought that the step moves at all is not. What is left unknown is a step that
     * moves a condition the way it could break it, and a hole a step could land in.
     */
    private static Boolean holdsAt(TakenConstraint taken,
                                   Map<NumericTerm, Place> from, Map<NumericTerm, Place> at) {
        if (at.keySet().containsAll(taken.terms())) {
            return switch (taken) {
                case TakenConstraint.Affine(var form, var rel) ->
                        rel.holds(OrderedAffineBoundary.along(form.coefs(), at)
                                .add(form.constant()).signum());
                case TakenConstraint.Ordered(
                        var term, var place, var rel) -> rel.holds(at.get(term).compareTo(place));
                case TakenConstraint.AwayFrom(var term, var place) ->
                        at.get(term).compareTo(place) != 0;
            };
        }
        // A bound on one position and a hole at one are over the position they name, and a step
        // that moves it has that position's number in hand — so the only condition that reaches
        // here is a form over positions this input says nothing about.
        if (!(taken instanceof TakenConstraint.Affine(
                var form, var rel))) {
            return null;
        }
        return whatAStepDoesTo(rel, moves(form.coefs(), from, at));
    }

    /** What a step does to a form: the positions it moves, weighed as the form weighs them. The
     *  rest are the same at both ends and cancel, which is why the numbers this does not have are
     *  not needed. */
    private static BigDecimal moves(Map<NumericTerm, BigDecimal> coefs,
                                    Map<NumericTerm, Place> from, Map<NumericTerm, Place> at) {
        BigDecimal by = BigDecimal.ZERO;
        for (Map.Entry<NumericTerm, BigDecimal> each : coefs.entrySet()) {
            Place was = from.get(each.getKey());
            Place now = at.get(each.getKey());
            if (was == null || now == null) {
                continue;   // not a position the step moves, so it is the same at both ends
            }
            by = by.add(Count.number(now).at().subtract(Count.number(was).at())
                    .multiply(each.getValue()));
        }
        return by;
    }

    /** Whether a condition that held still holds once what it is over has moved by {@code by}, or
     *  null where the move could go either way. */
    private static Boolean whatAStepDoesTo(Rel rel, BigDecimal by) {
        if (by.signum() == 0) {
            return true;   // nothing moved it, so it answers what it answered
        }
        return switch (rel) {
            case LE, LT -> by.signum() < 0 ? Boolean.TRUE : null;
            case GE, GT -> by.signum() > 0 ? Boolean.TRUE : null;
            // It held at nought and no longer stands there, which settles it the other way.
            case EQ -> Boolean.FALSE;
            // It held away from nought and a step of any size could land on it.
            case NE -> null;
        };
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
        out.sort(Comparator.comparing(BigDecimal::abs));
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
            Carrier carrier = boundary.of().carrierOf(each.getKey());
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
        return terms.stream().sorted(Comparator.comparing(NumericTerm::toString))
                .toList();
    }

    private static BigDecimal weight(QuantityKey of, NumericTerm term) {
        return of.direction().getOrDefault(term, BigDecimal.ZERO);
    }

    private static boolean whole(BigDecimal at) {
        return at.stripTrailingZeros().scale() <= 0;
    }

}
