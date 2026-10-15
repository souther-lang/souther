package souther.compiler.query;

import souther.compiler.check.Carrier;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.NumericTerms;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Place;
import souther.compiler.numeric.Rel;
import souther.compiler.numeric.Towards;
import souther.compiler.numeric.UnheldNumber;
import souther.compiler.partition.Border;
import souther.compiler.partition.Demand;
import souther.compiler.partition.DomainPoint;
import souther.compiler.partition.NotOwedReason;
import souther.compiler.partition.LinearQuantity;
import souther.compiler.partition.ObligationIdentity;
import souther.compiler.partition.OnTheWay;
import souther.compiler.partition.OrderedAffineBoundary;
import souther.compiler.partition.QuantityKey;
import souther.compiler.partition.ReadingGap;
import souther.compiler.partition.RowDemand;
import souther.compiler.partition.StandingAtAPoint;
import souther.compiler.partition.TakenConstraint;
import souther.compiler.partition.WayToTheBorder;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;
import java.util.function.Predicate;
import java.util.function.UnaryOperator;

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
 * <p><b>Five answers, and two of them settle a verdict without a row.</b> {@link ByDirection}
 * answers each line of the family, {@link NotDueYet} says the question waits on the points,
 * {@link CouldNotTell} says it was put and could not be settled, {@link NoSuchQuestion} says there is
 * no such question to put, and {@link NotApplicable} says the model's rules leave no row that could
 * settle it. What goes in the last two is a fact — about the line itself, or a proof read off the
 * rules — and never a limit of this compiler or of the strategy it was asked under. A question this
 * cannot answer, filed as one that does not exist or does not apply, is a verdict settled on the
 * strength of something nobody established.
 */
public sealed interface AnotherLineTheRowsAllow {

    /**
     * The family held against the rows, each line of it answered on its own.
     *
     * <p><b>Every line of the family and not the first one standing.</b> A row that rules one of
     * them out need not rule out the next: on {@code y >= x} the rows can leave both {@code y = 0}
     * and {@code -x + 2 * y = 0} standing, and a row at {@code (1, 0)} answers the first and not the
     * second. Named one at a time, each run would find the next only once the row for the last was
     * written, and a block pasted whole would never reach the state where nothing is owed.
     *
     * <p>What a line is owed is a direction and never a threshold along it ({@link
     * ObligationIdentity.OfABorder}). Which threshold the rows leave standing moves with every row,
     * and which directions the family holds does not, so the entries here are the family's own in
     * the family's own order.
     *
     * @param each one answer per line of the family, in the order the family names them
     */
    record ByDirection(List<Direction> each) implements AnotherLineTheRowsAllow {

        public ByDirection {
            each = List.copyOf(each);
            if (each.isEmpty()) {
                throw new IllegalArgumentException("a family held against the rows has a line in"
                        + " it, and one with none is a question that does not arise");
            }
            Set<QuantityKey> seen = new LinkedHashSet<>();
            for (Direction one : each) {
                if (!seen.add(one.direction())) {
                    throw new IllegalArgumentException("one line of the family answered twice: "
                            + one.direction());
                }
            }
        }

        /** The lines the rows leave standing, each of which is owed a row. */
        public List<Stands> standing() {
            return each.stream().filter(Stands.class::isInstance).map(Stands.class::cast)
                    .toList();
        }

        /** The lines the question was put of and could not be settled for. */
        public List<Undecided> undecided() {
            return each.stream().filter(Undecided.class::isInstance).map(Undecided.class::cast)
                    .toList();
        }

        /** Whether the rows rule out every line of the family, which is the border told apart from
         *  every line one step from it. */
        public boolean everyOneRuledOut() {
            return each.stream().allMatch(RuledOut.class::isInstance);
        }

        /** The directions the family holds, which is what this border is owed rows over. */
        public List<QuantityKey> family() {
            return each.stream().map(Direction::direction).toList();
        }
    }

    /**
     * What the rows came to about one line of the family.
     *
     * <p>Three answers, and only one of them is settled in the model's favour. A line nothing here
     * could settle is neither ruled out nor standing, and read as either it is a verdict nobody
     * established — ruled out, a border would be shown told apart from a line no row tells it from;
     * standing, an author would be asked for a row the question never showed is owed.
     */
    sealed interface Direction {

        /** The line of the family this is about. */
        QuantityKey direction();
    }

    /** The rows tell the border from this line whatever threshold it is drawn at. */
    record RuledOut(QuantityKey direction) implements Direction {

        public RuledOut {
            Objects.requireNonNull(direction, "a line ruled out is some line");
        }
    }

    /**
     * The question was put of this line and could not be settled, and this is what stopped it.
     *
     * <p>Never read as ruled out. A row this compiler could not read, an input nothing could show
     * arriving and a sum the exact arithmetic could not hold all leave the line where it was, and
     * what weakens the measure is that.
     */
    record Undecided(QuantityKey direction, Unsettled why) implements Direction {

        public Undecided {
            Objects.requireNonNull(direction, "a line left undecided is some line");
            Objects.requireNonNull(why, "a line left undecided says what stopped it");
        }
    }

    /**
     * The rows do not rule this line out, and this is where they leave it.
     *
     * <p><b>What is owed is the direction and not the line drawn along it.</b> The rows leave a
     * range of thresholds standing on it: past every row the model keeps and short of every row it
     * refuses. {@link #cut} is the near end of that range and {@link #refusedFrom} is what bounds
     * it at the far end. A row that answers differently from the line at {@code cut} need not
     * leave the range empty — one the model keeps that lands inside it moves the threshold to
     * itself, and the next run finds the same direction standing at the new one. So what a row has
     * to do here is leave no threshold standing ({@link #ruledOutBy}), and the search, the reading
     * of an offered row and the input named for it all ask that one question.
     *
     * <p><b>What is missing here is a condition and not a place.</b> {@link #tellsApartAt} is one
     * input that would settle it — the one the rows themselves lead to. A search asked for the
     * place would be held to whichever input the walk over the rows reached first, so the condition
     * is what travels ({@link #onTheRefusedSide}, {@link #onTheKeptSide}), and the place is what the
     * measurement saw.
     *
     * @param direction    the line one step from the model's that every row answers alike under
     * @param cut          the furthest along it of the rows the model keeps, which is the
     *                     tightest threshold that keeps every one of them
     * @param refusedFrom  the nearest along it of the rows the model refuses, or null where the
     *                     rows read on this line hold none
     * @param keptOn       the side of the threshold this line keeps a row on, which is the side the
     *                     model's own rule is satisfied on
     * @param tellsApartAt an input that would rule this line out, or null where none was worked
     *                     out or every one that was is one the declarations are shown to leave
     *                     nothing at. What the measurement itself reached, and never where a row has
     *                     to be written: it is a witness of the condition and not the condition
     */
    record Stands(QuantityKey direction, ExactRatio cut, ExactRatio refusedFrom, Towards keptOn,
                  Map<NumericTerm, Place> tellsApartAt) implements Direction {

        public Stands {
            if (direction == null || cut == null || keptOn == null) {
                throw new IllegalArgumentException("a line the rows allow is a direction, a"
                        + " place along it and a side it keeps: " + direction + " " + cut + " "
                        + keptOn);
            }
            if (!new Ends(direction, keptOn, cut, refusedFrom).apart()) {
                throw new IllegalArgumentException("a line standing where a row the model refuses"
                        + " is no further along it than one it keeps: " + cut + " and "
                        + refusedFrom);
            }
            tellsApartAt = tellsApartAt == null ? null
                    : Collections.unmodifiableMap(new LinkedHashMap<>(tellsApartAt));
        }

        private Stands(Ends ends, Map<NumericTerm, Place> tellsApartAt) {
            this(ends.direction(), ends.kept(), ends.refused(), ends.keptOn(), tellsApartAt);
        }

        private Ends ends() {
            return new Ends(direction, keptOn, cut, refusedFrom);
        }

        /**
         * Whether a row whose positions read as {@code values} leaves no threshold on this line
         * standing beside the rows already read, with {@code drawn} the model's own line — or why
         * that could not be worked out.
         *
         * <p>The rows already read with this one added, and asked the question they were asked:
         * the same fold, so that a row offered for the line and the rows that left it standing are
         * held to one rule. Which side of the model's line the row is on is read here and nowhere
         * else, from the line itself: handed in as a yes or no, a sum the exact arithmetic could not
         * hold came in as a no, and a row the model keeps ruled the line out as one it refuses.
         */
        public ExactAnswer<Boolean> ruledOutBy(OrderedAffineBoundary drawn,
                                               Map<NumericTerm, Place> values) {
            return ends().with(drawn, values).map(after -> !after.apart());
        }

        /**
         * Where a row the model refuses has to stand to rule this line out, as a refinement of
         * {@code within}.
         *
         * <p>Within reach of the near end: a refused row there is one every threshold on this line
         * keeps, and none of them can keep it and the rows the model keeps apart. Which also says
         * why the rows already written are outside it: every row the model refuses is past {@code
         * cut} by the arithmetic that put {@code cut} where it is.
         */
        public SearchRegion onTheRefusedSide(SearchRegion within) {
            // The region is asked to take the line in and carries it, which the direction's own
            // type has already settled: a boundary of this kind exists only where every term of
            // the quantity has a carrier that counts (OrderedAffineBoundary.weighable), and a
            // region refuses a form only for a term with no carrier at all.
            return within.assuming(new LinearForm<>(cut.negated(), direction.direction()),
                    keptOn == Towards.BELOW ? Rel.LE : Rel.GE).taken();
        }

        /**
         * Where a row the model keeps has to stand to rule this line out, as a refinement of a
         * region, or empty where the rows hold no row the model refuses for a kept one to be past.
         *
         * <p>At or past the far end, and not merely past {@code cut}. A kept row between the two is
         * kept by a threshold drawn at itself, which still refuses every row the model refuses —
         * so the line survives it, and a row offered there would be answered by the next run with
         * the same line at another place.
         */
        public Optional<UnaryOperator<SearchRegion>> onTheKeptSide() {
            if (refusedFrom == null) {
                return Optional.empty();
            }
            LinearForm<NumericTerm> past =
                    new LinearForm<>(refusedFrom.negated(), direction.direction());
            Rel rel = keptOn == Towards.BELOW ? Rel.GE : Rel.LE;
            return Optional.of(within -> within.assuming(past, rel).taken());
        }

        /**
         * Whether {@code other} is the same line beside the same border, whatever input each names.
         *
         * <p>Two readings of one border read the same rows and so leave the same range standing;
         * the input named for it is a further answer that each reading's own way to the border and
         * declarations can give differently.
         */
        public boolean isTheLineOf(Stands other) {
            return direction.equals(other.direction) && cut.equals(other.cut)
                    && Objects.equals(refusedFrom, other.refusedFrom) && keptOn == other.keptOn;
        }

        /** How a report names the line, which is the direction spelled as an author writes a form,
         *  at the tightest threshold the rows leave it. */
        public String label() {
            return OrderedAffineBoundary.spelled(direction.direction()) + " = " + cut.spelled();
        }

        /**
         * What the walk that named this went without, which is nothing.
         *
         * <p>Here so that a finding made from this takes what found it, as every finding does. The
         * condition is carried rather than the consequence: a line the rows allow is named only
         * where every reading of every row was read
         * ({@link StandingAtAPoint.RowsRead#everyOne}), and a walk that went without one comes back
         * as {@link Undecided}. So there is nothing for a finding off this to be weakened by — and
         * a caller handing over some measure beside it would give this finding whatever another
         * line of the same behavior went without.
         */
        public WeakeningSet weakening() {
            return WeakeningSet.none();
        }

        /**
         * The range of thresholds the rows read so far leave on one line, by its two ends.
         *
         * <p>One fold for every question about it. The measurement folds every row in and asks
         * whether a range is left; a row offered for the line is folded into what the measurement
         * left and asked the same; a step taken to name an input is asked it too. Which way along
         * the line is "further" turns on the side the line keeps, and it is turned here and nowhere
         * else.
         *
         * @param kept    the furthest along of the rows the model keeps, or null before one
         * @param refused the nearest along of the rows the model refuses, or null before one
         */
        private record Ends(QuantityKey direction, Towards keptOn, ExactRatio kept,
                            ExactRatio refused) {

            /** No row read yet. */
            static Ends none(QuantityKey direction, Towards keptOn) {
                return new Ends(direction, keptOn, null, null);
            }

            /**
             * These ends with a row whose positions read as {@code values} folded in, on the side
             * of {@code drawn} — the model's own line — that it falls; or why either sum, the
             * model's or this line's, could not be held.
             *
             * <p>Both read here. Which side of the model's line a row is on is half of what the row
             * says about this one, and a fold handed that half by its caller is a fold that takes
             * whatever the caller made of a sum it could not hold.
             */
            ExactAnswer<Ends> with(OrderedAffineBoundary drawn, Map<NumericTerm, Place> values) {
                return drawn.satisfies(values).flatMap(modelKeeps ->
                        OrderedAffineBoundary.along(direction, values)
                                .map(at -> withAt(modelKeeps, at)));
            }

            /** The same, for a row already read as how far along the line it is. */
            Ends withAt(boolean modelKeeps, ExactRatio at) {
                if (modelKeeps) {
                    return new Ends(direction, keptOn, kept == null ? at : further(kept, at),
                            refused);
                }
                // The nearer of the two, which is the one the other keeps.
                return new Ends(direction, keptOn, kept,
                        refused == null || keeps(keptOn, refused, at) ? at : refused);
            }

            /**
             * Whether some threshold keeps every kept row and refuses every refused one.
             *
             * <p>The threshold itself is kept, so a refused row exactly at the furthest kept one
             * leaves none: the line would keep it, and the two would not answer alike at it.
             */
            boolean apart() {
                return kept == null || refused == null || !keeps(keptOn, kept, refused);
            }

            /** Whichever of the two is further along the side the line keeps a row on. */
            private ExactRatio further(ExactRatio a, ExactRatio b) {
                return keeps(keptOn, a, b) ? a : b;
            }
        }
    }

    /**
     * The question was put of the border and could not be settled for any line of it, and this is
     * what stopped it.
     *
     * <p>Apart from {@link NoSuchQuestion}, which is the nearest thing and is not this. There the
     * line has no line one step from it and nothing anybody writes changes that; here there is a
     * question, and what is missing is a reading, a strategy or a proof. Held as one arm, a
     * shortfall of this compiler's was published as a fact about the model, and a verdict rested on
     * it. What stopped one line of the family and not the rest is that line's ({@link Undecided}).
     *
     * <p><b>Only this arm and an undecided line weaken the measure.</b> A walk short of a row that
     * still ruled a line out has settled it: reading more rows leaves fewer lines standing, never
     * more, so what it established holds over every row it did not read. So being short is not what
     * makes a measure partial — coming back unsettled is, and a measure weakened by every partial
     * walk would hold a verdict open over a question that was answered.
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

        /**
         * A model's own decimals put a step of the fault family out of the exact arithmetic's reach,
         * so the family is not known whole.
         *
         * <p>Not the same as a family with nothing in it: that is a border every step turned back
         * onto this line, and this is a step this compiler could not even try. An empty or a
         * surviving family read either way here would be a settled verdict resting on a walk that
         * did not finish.
         */
        record AFaultFamilyMemberWasNotComposed() implements Unsettled {}

        /**
         * The values beside this line were not worked out, so there is no inequality to hold
         * against the lines beside it.
         *
         * <p>Not {@link NoStrategyForIt}, which is a rule that names a value and orders nothing: this
         * rule orders the values, and what stopped the reading is the exact arithmetic on the numbers
         * beside its line. And not a row whose sum could not be held, on this line or on one beside
         * it: that is a row read in part ({@link RowsIncomplete}), and is said in the words a
         * reading short of a number answers in.
         *
         * @param why which of the two ways the number was not held
         */
        record TheLineWasNotWorkedOut(UnheldNumber why) implements Unsettled {

            public TheLineWasNotWorkedOut {
                Objects.requireNonNull(why, "a line not worked out says why");
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
     *
     * <p>Which lines the question will be put of is known already. The family is the line's own
     * and no row moves it, so a reader counting what a border is owed is told the same lines
     * before its points are met as after.
     *
     * @param family the lines one step from this one, in the order the family names them
     */
    record NotDueYet(List<QuantityKey> family) implements AnotherLineTheRowsAllow {

        public NotDueYet {
            family = List.copyOf(family);
            if (family.isEmpty()) {
                throw new IllegalArgumentException("a question not due yet is about some line of"
                        + " the family, and a family with none is a question that does not arise");
            }
        }
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
            Objects.requireNonNull(why, "a question that does not exist says why");
        }
    }

    /**
     * There are lines one step from this one, and the model's own rules leave no value on the side
     * of it the border refuses, so holding the border against them is no obligation of the rows.
     *
     * <p>Not {@link NoSuchQuestion}: the lines exist, and a row the model keeps can even be answered
     * differently by one of them drawn at some threshold. What no row can do is rule a line out
     * whatever threshold it is drawn at — that takes a row the model refuses, or one it keeps past
     * a row it refuses, and the rules refuse every such value at construction. Given only rows the
     * model keeps, a threshold past every one of them always keeps them all. So the fault this would
     * ask about is one the rows cannot settle, and what keeps a value on the right side of the line
     * is the rules that refuse the rest — which is their guarantee to make, at construction and
     * where outside data is turned into a value, and not something a row of a behavior over such
     * values could show.
     *
     * <p>Not {@link Undecided} either, which is a question this compiler could not settle. This one
     * is settled by a proof read off the model ({@link NotOwedReason#NO_VALUE_CAN_STAND_THERE} at
     * every point the border has on its refused side), and nothing a row is written at or a search
     * tries would change it — so a verdict may rest on it, and a search that found nothing there is
     * never taken for it.
     *
     * @param family the lines one step from this one, which are not owed a row
     * @param because what the model says of the refused side, which is the proof
     */
    record NotApplicable(List<QuantityKey> family, NotOwedReason because)
            implements AnotherLineTheRowsAllow {

        public NotApplicable {
            family = List.copyOf(family);
            if (family.isEmpty()) {
                throw new IllegalArgumentException("lines not owed a row are some lines, and a family"
                        + " with none is a question that does not arise");
            }
            if (because != NotOwedReason.NO_VALUE_CAN_STAND_THERE) {
                throw new IllegalArgumentException("only no value standing on a side is a proof that"
                        + " no row is there to write: " + because);
            }
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
        /** The line is on a number that is no form over positions — how many elements of a
         *  container meet something — so there are no weights for another line to write
         *  differently. */
        THE_QUANTITY_IS_NO_FORM,
        /** No position of it is weighed by a number a model writes. A date counts from an origin
         *  nobody wrote, so a line weighing one of them two is a line nobody can state — such a
         *  border can shift and cannot turn. */
        NO_POSITION_OF_IT_IS_WEIGHED_BY_A_NUMBER
    }

    /**
     * What the rows leave standing beside {@code boundary}.
     *
     * <p>Every line of the family, each answered on its own ({@link ByDirection}). A row that rules
     * one of them out need not rule out another, so a pass that stopped at the first one standing
     * would hand a reader one row to write and leave the next line for the run after it.
     *
     * <p>{@code refused} says whether the declarations of the positions are shown to leave nothing
     * at an input. It decides which input is named for the line and never whether the line stands:
     * an input is worked out by stepping along a line, which knows the arithmetic and nothing of
     * what a position's type refuses.
     */
    static AnotherLineTheRowsAllow of(Border border,
                                      boolean everyPointMet,
                                      java.util.function.Supplier<StandingAtAPoint.RowsRead> read,
                                      List<OrderedAffineBoundary> elsewhere,
                                      WayToTheBorder way,
                                      Predicate<Map<NumericTerm, Place>> refused) {
        // The two ways a border is not a line another line can be written beside, told apart. A
        // rule that names a value orders nothing and has no side to keep a row on; a rule on an
        // order with no numbers has no weights to write differently. Read off one answer, either
        // would be published under the other's word.
        // What the line is, before what its rule states about it. Whether there is a line one step
        // from this one is the line's own answer and is the same whichever way the rule reads it —
        // so a bound on one position comes back as a question that does not arise, and never as one
        // this compiler declined to put.
        if (!(border.cut().of() instanceof LinearQuantity of)) {
            return new NoSuchQuestion(Reason.THE_QUANTITY_IS_NO_FORM);
        }
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
        FaultFamily.Found found = new FaultFamily(runs, weighed).others();
        // A step a model's own decimals put out of the exact arithmetic's reach is not the same as a
        // step that landed back on this line: an empty family here is not the whole of what turning
        // every line away establishes, so it must not be read as the settled fact that reading would
        // be everywhere else.
        if (!found.everyStepWasComposed()) {
            return new CouldNotTell(new Unsettled.AFaultFamilyMemberWasNotComposed());
        }
        List<QuantityKey> family = found.lines();
        if (family.isEmpty()) {
            // Weighed every way one step allows and every one of them is this line. There is
            // nothing to be told from, which is the same fact the reasons above are.
            return new NoSuchQuestion(Reason.THE_LINE_IS_ON_ONE_POSITION);
        }
        // And a side to refuse a row on. Where no value stands on the side the border refuses,
        // nothing a row is written at could rule a line of the family out, and that is a proof read
        // off the model rather than anything the rows or a search came to — so it is asked before
        // either of them, and whether the points are met is beside the point.
        if (noValueStandsOnTheFarSide(border)) {
            return new NotApplicable(family, NotOwedReason.NO_VALUE_CAN_STAND_THERE);
        }
        // And the rows have met its points. Asked sooner, a border the rows have not caught up with
        // would be held open on what the points already say — and one whose kept side the rules
        // leave no value at would be held open on a row nobody could ever write.
        if (!everyPointMet) {
            return new NotDueYet(family);
        }
        // And now the rule. There is a line one step from this one, and a rule that names a value
        // orders nothing — so it has no side to keep a row on and nothing here holds it against its
        // neighbours. A strategy nobody wrote, and not a question the model does not raise: the
        // second would settle a verdict on something nobody established.
        ExactAnswer<Optional<OrderedAffineBoundary>> drawn = OrderedAffineBoundary.of(border);
        if (drawn instanceof ExactAnswer.Unheld<Optional<OrderedAffineBoundary>> unheld) {
            return new CouldNotTell(new Unsettled.TheLineWasNotWorkedOut(unheld.why()));
        }
        Optional<OrderedAffineBoundary> held =
                ((ExactAnswer.Held<Optional<OrderedAffineBoundary>>) drawn).value();
        if (held.isEmpty()) {
            return new CouldNotTell(
                    new Unsettled.NoStrategyForIt(Strategy.A_RULE_THAT_NAMES_A_VALUE));
        }
        OrderedAffineBoundary boundary = held.get();
        // The rows read here and not before. Reading them is a walk of its own over every row, and
        // every question above is about the line alone — so a border with no line beside it, which
        // is every bound on a position, pays nothing for being asked.
        StandingAtAPoint.RowsRead rows = read.get();
        // The rows on each side, for the steps an input is named by. A row whose sum on the model's
        // own line could not be held is on neither: the fold below meets it again and says what it
        // leaves undecided.
        List<Map<NumericTerm, Place>> satisfying = new ArrayList<>();
        List<Map<NumericTerm, Place>> refusing = new ArrayList<>();
        Set<ReadingGap> sideNotHeld = new LinkedHashSet<>();
        for (Map<NumericTerm, Place> values : rows.each()) {
            switch (boundary.satisfies(values)) {
                case ExactAnswer.Held<Boolean> side ->
                        (side.value() ? satisfying : refusing).add(values);
                case ExactAnswer.Unheld<Boolean> unheld ->
                        sideNotHeld.add(new ReadingGap.CouldNotWorkOut(unheld.why()));
            }
        }
        // No row the rule keeps, so there is nothing a threshold on any other line has to keep, and
        // the tightest one there is falls below every row instead of at one of them — which is a
        // place this cannot name without a step of the other line's own. Where the rows are all on
        // the kept side the tightest threshold is the furthest of them, so that side is answered
        // below like any other. And where a row this could not place may be the one the rule keeps,
        // the rows were read in part, in the words a reading short of a number answers in.
        if (satisfying.isEmpty()) {
            if (!sideNotHeld.isEmpty()) {
                Set<ReadingGap> met = new LinkedHashSet<>(rows.why());
                met.addAll(sideNotHeld);
                return new CouldNotTell(new Unsettled.RowsIncomplete(
                        ReadingReasons.of(met, rows.tried())));
            }
            return new CouldNotTell(new Unsettled.TheRowsAreAllOnOneSide());
        }
        List<Direction> each = new ArrayList<>();
        for (QuantityKey other : family) {
            each.add(assessed(boundary, other, rows, satisfying, refusing, elsewhere, way,
                    refused));
        }
        return new ByDirection(each);
    }

    /**
     * Whether no value is shown to stand at any point the border has on the side it refuses.
     *
     * <p>Every such point, and at least one. The point beside the line out there and the run past it
     * are the whole of that side as far as a row at this border goes: a value past where the run
     * stops is decided by another rule before it reaches this one, and is no row here. So where no
     * value stands at either there is no row the model refuses at this border. A point owed nothing
     * for any other reason — an order naming no value beside the line — is not that proof, and
     * neither is a point whose place could not be worked out: the question is then put as it is
     * everywhere else.
     */
    private static boolean noValueStandsOnTheFarSide(Border border) {
        boolean any = false;
        for (DomainPoint point : border.answers().keySet()) {
            if (border.roleOf(point).inside()) {
                continue;
            }
            any = true;
            if (!(border.demand(point) instanceof Demand.NotOwed(var why))
                    || why != NotOwedReason.NO_VALUE_CAN_STAND_THERE) {
                return false;
            }
        }
        return any;
    }

    /**
     * What the rows come to about one line of the family.
     *
     * <p>Every row folded into the range of thresholds the line could be drawn at ({@link
     * Stands.Ends}), and the line ruled out where none is left. Every row the model keeps has to be
     * kept, so the threshold is at least as far along as the furthest of them; every row it refuses
     * has to be refused, so the threshold is short of the nearest of those. Where the first is not
     * short of the second there is nowhere to put it, and the rows have told the two lines apart.
     *
     * <p>A row the exact arithmetic cannot hold — its sum on the model's own line, which says which
     * side it is on, or its sum along this one — is left out of the fold and remembered as a row
     * read in part. Ruled out without it, the line is ruled out — a row read leaves fewer lines
     * standing, never more — and otherwise that row is what leaves the line undecided, and never
     * what rules it out.
     */
    private static Direction assessed(OrderedAffineBoundary boundary, QuantityKey other,
                                      StandingAtAPoint.RowsRead rows,
                                      List<Map<NumericTerm, Place>> satisfying,
                                      List<Map<NumericTerm, Place>> refusing,
                                      List<OrderedAffineBoundary> elsewhere,
                                      WayToTheBorder way,
                                      Predicate<Map<NumericTerm, Place>> refused) {
        Stands.Ends ends = Stands.Ends.none(other, boundary.satisfiedOn());
        Set<ReadingGap> notHeld = new LinkedHashSet<>();
        for (Map<NumericTerm, Place> values : rows.each()) {
            switch (ends.with(boundary, values)) {
                case ExactAnswer.Held<Stands.Ends> held -> ends = held.value();
                case ExactAnswer.Unheld<Stands.Ends> unheld ->
                        notHeld.add(new ReadingGap.CouldNotWorkOut(unheld.why()));
            }
        }
        if (!ends.apart()) {
            return new RuledOut(other);
        }
        // What was gone without, in the words of the thing that went without it. A row nothing
        // watched and a reading that came to nothing are two different things to do about, so
        // the first is answered before the second rather than folded into the reasons a reading
        // answers in.
        if (rows.unwatched()) {
            return new Undecided(other, new Unsettled.TheRunsWereNotWatched());
        }
        // A row this could not hold is a row read in part: every value came back and the number
        // they come to did not, which is a reason a reading answers in already. Said beside the
        // reasons the walk over the rows met, as one account of what the rows went without.
        if (!notHeld.isEmpty() || !rows.everyOne()) {
            Set<ReadingGap> met = new LinkedHashSet<>(rows.why());
            met.addAll(notHeld);
            return new Undecided(other, new Unsettled.RowsIncomplete(
                    ReadingReasons.of(met, rows.tried())));
        }
        // And an input that rules the line out and that the rules do send a row to. Where nothing
        // could show one, the question stands rather than being answered by whichever way it fell.
        Distinguisher parting =
                partingAt(boundary, ends, satisfying, refusing, elsewhere, way, refused);
        if (parting == null) {
            return new Undecided(other, new Unsettled.NoReachableDistinguisher());
        }
        return new Stands(ends, parting.named());
    }

    /**
     * An input that rules the line out, or null where none was worked out.
     *
     * <p>Found by moving along the model's own line, which is what leaves its answer where it was
     * and moves the other one: a step that the model weighs to nothing is a step every row can take
     * without crossing it, and the two lines are not parallel, so the same step does cross the other
     * one. How many steps it takes is arithmetic and not a search.
     *
     * <p>Crossing to the far end of the range and not to the near one. A row the model keeps is
     * stepped until it is at or past the nearest row the model refuses, and a refused row until it
     * is within reach of the furthest kept one; a kept row stepped only past the near end would be
     * an input the line answers differently at its current threshold and not one that rules it out,
     * and naming it would hand an author a row the next run answers with the same line moved.
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
     *
     * <p><b>And one the declarations are not shown to leave nothing at, where there is one.</b> A
     * step is arithmetic over amounts, so over positions whose types refuse some values it can land
     * on one of those. Such an input is passed over for another that is not, and where every input
     * that arrives is one of them the answer is still one, with none named: the two lines part
     * company, and nothing here says where an author could write a row.
     */
    private static Distinguisher partingAt(OrderedAffineBoundary boundary, Stands.Ends ends,
                                           List<Map<NumericTerm, Place>> satisfying,
                                           List<Map<NumericTerm, Place>> refusing,
                                           List<OrderedAffineBoundary> elsewhere,
                                           WayToTheBorder way,
                                           Predicate<Map<NumericTerm, Place>> refused) {
        QuantityKey other = ends.direction();
        Map<NumericTerm, ExactRatio> along = alongTheLine(boundary.direction(), other);
        if (along == null) {
            return null;
        }
        ExactRatio moves = weighing(other, along);
        if (moves == null || moves.signum() == 0) {
            return null;
        }
        // Every row, on whichever side of the line it is: which way a step has to go to cross the
        // other line depends on where the row already stands.
        Reaches reaches = new Reaches(way, along.keySet());
        List<Parting> found = new ArrayList<>();
        for (Map<NumericTerm, Place> values : satisfying) {
            partings(boundary, ends, values, along, moves, true, reaches, elsewhere, found);
        }
        for (Map<NumericTerm, Place> values : refusing) {
            partings(boundary, ends, values, along, moves, false, reaches, elsewhere, found);
        }
        // Of the inputs the rules still send a row to, the one whose difference an author can see,
        // and the nearest of those. Reaching is the condition: an input the way turns away is not a
        // worse answer than another, it is no answer, because two lines answering differently where
        // no row arrives is not something a row could show. What the behavior's other lines do with
        // it is the preference beside that: where they keep it, this line is what settles the answer
        // there, and where they do not the two part company under a rule that has already decided.
        List<Parting> arriving = found.stream().filter(Parting::reached)
                .sorted(Comparator.comparingInt((Parting each) -> each.visible() ? 0 : 1)
                        .thenComparing(Parting::steps))
                .toList();
        if (arriving.isEmpty()) {
            return null;
        }
        // In that order, and the first the declarations are not shown to leave nothing at. Asked
        // one at a time and stopping there: each asking reads the declarations again.
        for (Parting each : arriving) {
            if (!refused.test(each.at())) {
                return new Distinguisher(each.at());
            }
        }
        return new Distinguisher(null);
    }

    /**
     * What rules the line out where a row arrives.
     *
     * @param named an input that rules the line out and the declarations are not shown to leave
     *              nothing at — not that a row can be written there — or null where every input
     *              that arrives is one they are shown to refuse
     */
    record Distinguisher(Map<NumericTerm, Place> named) {}

    /**
     * The inputs near one row that rule the line out.
     *
     * @param reached whether a row still arrives at this rule there, which is the condition
     * @param visible whether the behavior's other lines keep it, so that what this line answers is
     *                what the behavior answers — the preference, and never the condition
     * @param steps   how far from the row it is, which is what makes one input nearer than another
     */
    record Parting(Map<NumericTerm, Place> at, boolean reached, boolean visible,
                   ExactRatio steps) {}

    /** Whatever {@code values} reaches by stepping along the model's own line, collected into
     *  {@code found}. */
    private static void partings(OrderedAffineBoundary boundary, Stands.Ends ends,
                                 Map<NumericTerm, Place> values,
                                 Map<NumericTerm, ExactRatio> along, ExactRatio moves,
                                 boolean kept, Reaches reaches,
                                 List<OrderedAffineBoundary> elsewhere,
                                 List<Parting> found) {
        // The end of the range a row on this side has to reach. A kept row with no refused row to
        // reach has nothing it could cross to rule the line out.
        ExactRatio toward = kept ? ends.refused() : ends.kept();
        if (toward == null) {
            return;
        }
        // Wherever a model's own decimals put this row's sum, the end, or a step along the line out
        // of the exact arithmetic's reach, this stepping composes no partings for this row — the
        // same as a row the reduction below already skips for want of one. Fewer candidate inputs is
        // what every caller here already reads a gap this way, never a claim the model has none.
        ExactRatio at = OrderedAffineBoundary.along(ends.direction(), values).orNull();
        ExactRatio apart = at == null ? null : toward.minus(at).orNull();
        BigInteger truncated = apart == null ? null
                : apart.dividedBy(moves).flatMap(ExactRatio::truncated).orNull();
        if (truncated == null) {
            return;
        }
        for (ExactRatio steps : stepsAround(truncated)) {
            // Asked by standing at the input rather than by reasoning about which way the
            // arithmetic came out. Which side of its own threshold a value falls on is the same
            // question here as everywhere, and a number of steps worked out from the signs would be
            // a second answer to it, right until one of the four ways the signs can fall was
            // written down wrong.
            ExactRatio movedAt = steps.times(moves).flatMap(at::plus).orNull();
            if (movedAt == null || ends.withAt(kept, movedAt).apart()) {
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
     * sentence says — this only decides which of them is worth naming. So a line whose sum at the
     * input could not be held is one not shown to keep it, and the input is merely not preferred.
     */
    private static boolean keptByTheOthers(List<OrderedAffineBoundary> elsewhere,
                                           Map<NumericTerm, Place> at) {
        for (OrderedAffineBoundary each : elsewhere) {
            if (at.keySet().containsAll(each.direction().direction().keySet())
                    && !Boolean.TRUE.equals(each.satisfies(at).orNull())) {
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
                    // One of several ways, and which the row took is not followed through a step:
                    // a step that keeps it on one may move it off it, and nothing here asks which.
                    case OnTheWay.OneOf _ -> {
                        return false;
                    }
                    // Settled for every row: past it whatever a step moves, or past it for none.
                    case OnTheWay.Settled settled -> {
                        if (!settled.thisWay()) {
                            return false;
                        }
                    }
                    // Which case a value turned out to be. A step moves numbers and a narrowing is
                    // about a position being one of its cases, so a step that moves no number of
                    // that position leaves it as the row had it; one that does is past what this
                    // reads. Where the position is an enumeration's, its number is the case's place
                    // on the order, and the narrowing is the places it leaves out: a step moving it
                    // still arrives where the place it moves to is none of those.
                    case OnTheWay.Narrowed(var _, var position, var _, var onItsOrder) -> {
                        if (moved.stream().anyMatch(term -> term.subjectPath().equals(position))) {
                            return false;
                        }
                        for (TakenConstraint.AwayFrom hole : onItsOrder) {
                            if (Collections.disjoint(hole.terms(), moved)) {
                                continue;
                            }
                            Boolean holds = holdsAt(hole, from, at);
                            if (holds == null || !holds) {
                                return false;
                            }
                        }
                    }
                    case OnTheWay.TakenIn(var _, RowDemand.Relational(var taken)) -> {
                        if (Collections.disjoint(taken.terms(), moved)) {
                            continue;   // the row's answer at it, unmoved
                        }
                        Boolean holds = holdsAt(taken, from, at);
                        if (holds == null || !holds) {
                            return false;
                        }
                    }
                    // That some element meets these, or every element does, which a step leaves as
                    // it was where it moves nothing they turn on. One that does may move an
                    // element they are about, and which elements those are is nothing an input's
                    // numbers say — nor is whether an element is still the value it was compared
                    // with, once a number of either moved.
                    case OnTheWay.TakenIn(var _, RowDemand.Exists exists) -> {
                        if (movesAnyOf(exists.positions())) {
                            return false;
                        }
                    }
                    case OnTheWay.TakenIn(var _, RowDemand.ForAll every) -> {
                        if (movesAnyOf(every.positions())) {
                            return false;
                        }
                    }
                    // How many elements meet a statement, for the same reason: a step moving a
                    // number the statement reads may move which elements meet it.
                    case OnTheWay.TakenIn(var _, RowDemand.SoMany many) -> {
                        if (movesAnyOf(many.positions())) {
                            return false;
                        }
                    }
                    // Which of two values stands at a position, and a step moves numbers: what
                    // stands there is what the row had.
                    case OnTheWay.TakenIn(var _, RowDemand.ATruth truth) -> {
                        if (movesAnyOf(truth.positions())) {
                            return false;
                        }
                    }
                    // Whether two positions hold one value, which a step moving a number of
                    // either may change.
                    case OnTheWay.TakenIn(var _, RowDemand.OneValueAtBoth both) -> {
                        if (movesAnyOf(both.positions())) {
                            return false;
                        }
                    }
                    // A statement no composer writes toward, which a step moving any number may
                    // turn: which numbers it turns on is the run's to say.
                    case OnTheWay.TakenIn(var _, RowDemand.ForTheRun _) -> {
                        if (!moved.isEmpty()) {
                            return false;
                        }
                    }
                }
            }
            return true;
        }

        /** Whether the step moves a number at or under one of {@code positions}. */
        private boolean movesAnyOf(Set<TermPath> positions) {
            return moved.stream().anyMatch(term -> positions.stream()
                    .anyMatch(position -> term.subjectPath().isAtOrUnder(position)));
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
                // A model's own decimals can put this row's sum out of the exact arithmetic's reach,
                // which this method already has a word for: null, the same as any other condition
                // nothing here can say.
                case TakenConstraint.Affine(var form, var rel) -> {
                    ExactRatio total = OrderedAffineBoundary.at(form, at).orNull();
                    yield total == null ? null : rel.holds(total.signum());
                }
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

    /** What a step does to a form: the positions it moves, weighed as the form weighs them, or null
     *  where the exact arithmetic could not hold it. The rest are the same at both ends and cancel,
     *  which is why the numbers this does not have are not needed. */
    private static ExactRatio moves(Map<NumericTerm, ExactRatio> coefs,
                                    Map<NumericTerm, Place> from, Map<NumericTerm, Place> at) {
        ExactRatio by = ExactRatio.ZERO;
        for (Map.Entry<NumericTerm, ExactRatio> each : coefs.entrySet()) {
            Place was = from.get(each.getKey());
            Place now = at.get(each.getKey());
            if (was == null || now == null) {
                continue;   // not a position the step moves, so it is the same at both ends
            }
            ExactRatio moved = Count.number(now).exactly().minus(Count.number(was).exactly()).orNull();
            if (moved == null) {
                return null;
            }
            by = moved.times(each.getValue()).flatMap(by::plus).orNull();
            if (by == null) {
                return null;
            }
        }
        return by;
    }

    /** Whether a condition that held still holds once what it is over has moved by {@code by}, or
     *  null where the move could go either way, or where the exact arithmetic could not hold it. */
    private static Boolean whatAStepDoesTo(Rel rel, ExactRatio by) {
        if (by == null) {
            return null;
        }
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
    private static boolean keeps(Towards satisfiedOn, ExactRatio cut, ExactRatio at) {
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
    private static List<ExactRatio> stepsAround(BigInteger crossing) {
        List<ExactRatio> out = new ArrayList<>();
        for (int away = -2; away <= 2; away++) {
            ExactRatio steps = ExactRatio.of(crossing.add(BigInteger.valueOf(away)));
            if (steps.signum() != 0) {
                out.add(steps);
            }
        }
        out.sort(Comparator.comparing(ExactRatio::abs));
        return out;
    }

    /** What a direction weighs a step to, where a step names only the positions it moves, or null
     *  where the exact arithmetic could not hold it — a step whose own weights are scaled far
     *  enough apart that the running sum meets one it cannot add. */
    private static ExactRatio weighing(QuantityKey of, Map<NumericTerm, ExactRatio> step) {
        ExactRatio at = ExactRatio.ZERO;
        for (Map.Entry<NumericTerm, ExactRatio> each : step.entrySet()) {
            at = weight(of, each.getKey()).times(each.getValue()).flatMap(at::plus).orNull();
            if (at == null) {
                return null;
            }
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
    private static Map<NumericTerm, ExactRatio> alongTheLine(QuantityKey wrote, QuantityKey other) {
        List<NumericTerm> terms = new ArrayList<>(named(wrote, other));
        for (int i = 0; i < terms.size(); i++) {
            for (int j = i + 1; j < terms.size(); j++) {
                ExactRatio mine = weight(wrote, terms.get(i));
                ExactRatio ours = weight(wrote, terms.get(j));
                // Where the two products are too far apart in scale for the exact arithmetic to
                // hold their difference, this pair of positions is one this cannot turn a step from
                // — tried the same as a pair whose turned weight comes to nothing.
                ExactAnswer<ExactRatio> onFirst = weight(other, terms.get(i)).times(ours);
                ExactAnswer<ExactRatio> onSecond = weight(other, terms.get(j)).times(mine);
                ExactRatio turned = onFirst.flatMap(first -> onSecond.flatMap(first::minus)).orNull();
                if (turned == null || turned.signum() == 0 || !mine.isWhole() || !ours.isWhole()) {
                    continue;
                }
                Map<NumericTerm, ExactRatio> step = new LinkedHashMap<>();
                step.put(terms.get(i), ours);
                step.put(terms.get(j), mine.negated());
                return step;
            }
        }
        return null;
    }

    /** The row's positions moved {@code steps} steps along {@code step}, or null where one of them
     *  has no value where it lands. */
    private static Map<NumericTerm, Place> movedBy(OrderedAffineBoundary boundary,
                                                   Map<NumericTerm, Place> values,
                                                   Map<NumericTerm, ExactRatio> step,
                                                   ExactRatio steps) {
        Map<NumericTerm, Place> moved = new LinkedHashMap<>();
        for (Map.Entry<NumericTerm, Place> each : values.entrySet()) {
            ExactRatio by = step.getOrDefault(each.getKey(), ExactRatio.ZERO);
            // A model's own decimals can put this row value and the step out of the exact
            // arithmetic's reach, which is the same as a place the carrier has no count for: this
            // input was not composed.
            ExactRatio at = by.times(steps).flatMap(Count.number(each.getValue()).exactly()::plus).orNull();
            if (at == null) {
                return null;
            }
            Carrier carrier = boundary.of().carrierOf(each.getKey());
            // Where the step lands is a value of the position or it is nowhere, which is the same
            // edge a row is written at: a place the carrier has no count for is no place at all.
            // A count the host has no room to write out is the same: this input was not composed.
            Place there = switch (Count.written(at)) {
                case ExactAnswer.Held<Optional<Count>> written -> carrier == null
                        || written.value().isEmpty() ? null
                        : carrier.onTheGrid(written.value().get());
                case ExactAnswer.Unheld<Optional<Count>> _ -> null;
            };
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
        return NumericTerms.inOrder(terms);
    }

    private static ExactRatio weight(QuantityKey of, NumericTerm term) {
        return of.direction().getOrDefault(term, ExactRatio.ZERO);
    }

}
