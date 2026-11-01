package souther.compiler.partition;

import souther.compiler.check.TypeView;
import souther.compiler.coverage.AlignedObservation;
import souther.compiler.coverage.ConditionOutcomeSite;
import souther.compiler.coverage.SeenComparison;
import souther.compiler.inputs.Quantities;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionSubject;
import souther.compiler.meaning.Proposition;
import souther.compiler.observe.ElementsTaken;
import souther.compiler.observe.Figure;
import souther.compiler.observe.ObservedValue;
import souther.compiler.observe.WorkFigure;
import souther.compiler.partition.BorderQuantity.Lastness;
import souther.compiler.types.Type;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.function.Supplier;

/**
 * Whether a tuple of values stands at one point of a border.
 *
 * <p>One walk for every kind of line, and the one place this is asked. What a value put at the point
 * is is the quantity's to read — it is the one thing that knows what it is a quantity of — and what
 * this adds is what belongs to the rows: which reading of a row a point is tried against, and that a
 * line a fork drew is met by getting the comparison to answer as well as by writing the value.
 *
 * <p>Asked of a tuple and not of a row, so that what is already written and what a generation has
 * just composed are put the same question. Written against a row, the question could only be asked
 * of what is in the file — and the second answer somebody wrote for a candidate would be this rule
 * again, free to agree with it until one of them moved.
 *
 * <p>Nothing here concludes anything about coverage. It says what these values do at this point; who
 * may act on that, and what a point nothing was seen at means, is the caller's.
 */
public final class StandingAtAPoint {

    /**
     * What a walk over some tuples came to at one point.
     *
     * <p>Four answers because the two that are not found are not one fact. A tuple that could not be
     * read leaves the point undecided; a tuple that stands at the level and has no account of its
     * run is one nothing can say reached the comparison, which is not the same as one that ran and
     * did not reach it. Which of them a caller may treat as a miss is the caller's to say.
     *
     * <p><b>And the two that found the values are a case of their own.</b> A caller that wants to
     * know whether the values were seen where the line is asks {@link AtPoint}, and one that wants
     * to know whether anything watched the run tells its two arms apart — so which readers those
     * two answers are alike to is settled here, once, rather than by each of them writing the pair
     * into an arm of its own switch. A caller free to write its own pair is free to write any pair,
     * and the pair that costs something is a walk that could not look put beside a walk that looked
     * and found nothing.
     */
    public sealed interface Met {

        /** The values stand where the line is. */
        sealed interface AtPoint extends Met {}

        /** And something watched the run reach the comparison, where reaching it was asked. */
        record Reached() implements AtPoint {}

        /** And nothing watched it get there, which this found out rather than concluded. */
        record NotWatched() implements AtPoint {}

        /** The values were read, and they are not where the line is. */
        record NotAtPoint() implements Met {}

        /**
         * There was nothing at the point to compare, and this is what stopped there being one.
         *
         * <p>Carries every reason rather than the fact of there being some, and never one of them
         * over another. A reader handed the case alone can say only that something went unread —
         * which is {@code Observed} from {@code TruncatedByLimit} from {@code Absent} being lost one
         * layer before anybody needs it; handed the strongest, it is lost wherever a point met both.
         *
         * <p><b>And a reading that was never tried is not a reading that came to nothing.</b> The
         * readings of a row that could be looked at and the readings there are to look at are two
         * counts, and where the second runs past what one point is tried against, a point no tried
         * reading stands at is a point some untried one may. So {@code tried} is beside the reasons
         * rather than among them: what stopped a reading this made is the reading's own answer, and
         * what stopped this making the rest is an answer about the search. Both can be true of one
         * point, and a state holding one of them would have to choose.
         *
         * @param why   what the readings that were made came to nothing by, which is empty where
         *              every one of them was read and the search is what stopped
         * @param tried whether every reading the row's containers allow was one this tried
         */
        record CouldNotTell(Set<ReadingGap> why, ReadingsTried tried) implements Met {

            public CouldNotTell {
                if (why == null || tried == null) {
                    throw new IllegalArgumentException(
                            "a point nothing could be told about says what stopped the telling");
                }
                if (why.isEmpty() && tried instanceof ReadingsTried.EveryOne) {
                    throw new IllegalArgumentException("a reading that went without nothing and"
                            + " tried every reading there is told this point apart, and this says"
                            + " it could not");
                }
                // In the order they were met, for the reason a report keeps any order.
                why = Collections.unmodifiableSet(new LinkedHashSet<>(why));
            }
        }

        Met REACHED = new Reached();

        Met NOT_WATCHED = new NotWatched();

        Met NOT_AT_POINT = new NotAtPoint();
    }

    /**
     * Whether every reading a row's containers allow was one a point was tried against.
     *
     * <p>What a bounded search may conclude turns on this. A reading standing at the point settles
     * the point however few were tried — one is what the question asks for — and a point no reading
     * stands at is a point nothing stands at only where there were no others to try. So a walk that
     * stopped may say it found something and may not say it found nothing, and this is the fact that
     * tells the two apart.
     *
     * <p><b>Said by the walk that stopped.</b> Which figure a walk stopped at is the walk's own
     * answer and nothing downstream can work it out: a reading count short of the containers is
     * short for whatever reason, and a reader deriving the reason from the shortfall names a figure
     * wherever a walk fell short of one it never reached. So this is built where the readings are
     * and travels from there, the way a decision reading says it stopped at a figure rather than
     * leaving its length to be read.
     */
    public sealed interface ReadingsTried {

        /** Every reading the containers allow was tried, so what none of them stands at, none
         *  stands at. */
        record EveryOne() implements ReadingsTried {}

        /**
         * The readings ran past what one point is tried against, and the rest were not tried.
         *
         * @param limits how many readings of one row a point is tried against, as each stood where
         *               a walk stopped, each once and in {@link Figure#inOrder}: a figure of this
         *               compiler's, and what a run allowing more would raise. More than one where
         *               the rows of one point were walked under more than one
         */
        record StoppedAtTheLimit(List<Figure> limits) implements ReadingsTried {

            public StoppedAtTheLimit {
                limits = Figure.inOrder(limits);
                if (limits.isEmpty()) {
                    throw new IllegalArgumentException("a walk stopped at a limit says which");
                }
            }

            /** Stopped at one limit, which is how a walk meets it. */
            public StoppedAtTheLimit(Figure limit) {
                this(List.of(limit));
            }
        }

        ReadingsTried EVERY_ONE = new EveryOne();

        /**
         * What two walks over the rows of one point tried between them: every reading where both
         * tried every one, and otherwise every limit either stopped at — a row stopped at one is
         * not read past it because another row was not.
         */
        default ReadingsTried and(ReadingsTried other) {
            if (!(this instanceof StoppedAtTheLimit mine)) {
                return other;
            }
            if (!(other instanceof StoppedAtTheLimit theirs)) {
                return this;
            }
            List<Figure> both = new ArrayList<>(mine.limits());
            both.addAll(theirs.limits());
            return new StoppedAtTheLimit(both);
        }
    }

    /**
     * The first of {@code rows} that stands there, or why none was found.
     *
     * <p>Takes the line as one measurement's reading of it, so that the walk a row's values are
     * found by is the one the line was measured against. Handed the quantity beside a walk, a
     * caller could put a line drawn at one reading to the rows of a behavior read at another —
     * which two behaviors taking a parameter spelled the same way is all it takes.
     *
     * @param watched every place a run through the comparison a row has to have got an answer out
     *             of is recorded, for a rule that meeting takes more than standing at the level.
     *             Empty where standing there is the whole of it. The places a run is written down
     *             and not which comparison it is, because what this asks them of is a run's own
     *             record.
     *             <p>Several where one rule is written into the tree that runs more than once, and
     *             a run that got an answer out of any of them got one out of the rule: they are
     *             one comparison the author wrote, and which of its copies ran is the operation's
     *             business rather than the model's
     */
    public static Met met(MeasuredInput.BorderReading line,
                          List<ObservedInputs> observed, Criterion criterion,
                          List<ConditionOutcomeSite> watched) {
        return putToRows(line, watched).met(observed, criterion);
    }

    /** What a statement comes to at one row, read over the whole row. */
    enum AtTheRow { HOLDS, FAILS, COULD_NOT_TELL }

    /**
     * The order of the elements of one container that a map filed from them is read in: which of
     * the elements holding one value at {@code position} is the entry under it.
     *
     * <p>What a statement of the last to hold rests on, and the unit a row may be read the other
     * way round in ({@link #atTheRow}): one container's order and no other's.
     */
    record OrderOfAKey(TermPath container, TermPath position) {

        /** The order {@code last} rests on, or null where it is about a place no row writes. */
        static OrderOfAKey of(Proposition.LastToHold last) {
            return last.container() instanceof DecisionSubject.AnInput(TermPath container)
                    && last.position() instanceof DecisionSubject.AnInput(TermPath position)
                    ? new OrderOfAKey(container, position) : null;
        }
    }

    /**
     * What {@code stated} comes to at the row {@code observed} wrote, read over the whole row with
     * no element of any container chosen — a statement about elements asks them itself.
     *
     * @param readTheOtherWay the orders read with the first element of a key as its entry rather
     *                        than the last: what the statement would come to were those, and no
     *                        others, the other way round
     */
    static AtTheRow atTheRow(Proposition stated, String behavior, Quantities quantities,
                             BehaviorInputs where, ObservedInputs observed,
                             Set<OrderOfAKey> readTheOtherWay) {
        if (!AStatementAtARow.askable(stated)) {
            return AtTheRow.COULD_NOT_TELL;
        }
        AStatementAtARow asked = AStatementAtARow.of(stated, behavior, quantities);
        RowWalk walk = new RowWalk(where, observed, readTheOtherWay);
        DiscoveringRow discovering = new DiscoveringRow(walk);
        asked.lookAt(discovering);
        Map<TermPath, Integer> containers = discovering.containers();
        // Positions of the statement inside a container no quantifier of it ranges over stand for
        // an element of it, so the statement is about the row where some element of each is
        // chosen: it holds where a reading holds, as a line is met where a reading stands.
        if (containers.isEmpty()) {
            return atTheRow(asked.at(discovering));
        }
        boolean couldNotTell = false;
        for (Map<TermPath, Integer> choice : readingsOver(containers)) {
            switch (atTheRow(asked.at(new OneReadingOfARow(walk, choice)))) {
                case HOLDS -> {
                    return AtTheRow.HOLDS;
                }
                case COULD_NOT_TELL -> couldNotTell = true;
                case FAILS -> { }
            }
        }
        return couldNotTell || containersAllowMoreThan(containers, MOST_READINGS)
                ? AtTheRow.COULD_NOT_TELL : AtTheRow.FAILS;
    }

    private static AtTheRow atTheRow(AStatementAtARow.Answer answer) {
        return switch (answer) {
            case AStatementAtARow.Answer.Holds _ -> AtTheRow.HOLDS;
            case AStatementAtARow.Answer.Fails _ -> AtTheRow.FAILS;
            case AStatementAtARow.Answer.CouldNotTell _ -> AtTheRow.COULD_NOT_TELL;
        };
    }

    /**
     * {@code line} put to rows, for as many rows and points as a caller asks of it: where it
     * decides and which elements a run meets its rule on are read once, and not once for every
     * point a row is tried against.
     *
     * @param watched as {@link #met} takes it
     */
    public static AtALine putToRows(MeasuredInput.BorderReading line,
                                    List<ConditionOutcomeSite> watched) {
        return new AtALine(line, watched, whereItDecides(line), metOn(line), Optional.empty());
    }

    /** One line put to rows ({@link #putToRows}). */
    public static final class AtALine {

        private final MeasuredInput.BorderReading line;
        private final List<ConditionOutcomeSite> watched;
        /** Where the line decides, put to rows, or empty where it is a whole comparison's or no
         *  comparison's. */
        private final Optional<WhereAPartDecides.AskedOfRows> decides;
        /** Which elements of the input a run gets an answer out of the line's rule on. */
        private final MetOnARow reached;
        /** For a point of a class the line cuts: what a row has to be for it. Empty for a point
         *  against the line. */
        private final Optional<AsAClass> asAClass;

        private AtALine(MeasuredInput.BorderReading line, List<ConditionOutcomeSite> watched,
                        Optional<WhereAPartDecides.AskedOfRows> decides, MetOnARow reached,
                        Optional<AsAClass> asAClass) {
            this.line = line;
            this.watched = List.copyOf(watched);
            this.decides = decides;
            this.reached = reached;
            this.asAClass = asAClass;
        }

        /**
         * This line put to rows for a point of a class it cuts, the class where the rule
         * {@code holds} or the one where it does not.
         *
         * <p>A row is at such a point by being in the class, by the run having had the rule come
         * out as the class says on every application of it, and by lying in no case that another
         * reading of the same comparison decides in. Where this line decides is no part of it: that
         * says where this line falls, and a class lies over the whole of the quantity. A row in the
         * case of another reading is a row of that reading's classes, and a row the rule comes out
         * the other way for is at the other class or at none.
         *
         * <p>The same line where nothing records a run through the rule, which an invariant's is:
         * there writing the value is the whole of reaching it.
         *
         * @param otherReadings the other readings of the comparison this line is a reading of
         */
        public AtALine forAClass(boolean holds, OtherReadings otherReadings) {
            return watched.isEmpty() ? this
                    : new AtALine(line, watched, Optional.empty(), reached,
                            Optional.of(new AsAClass(holds, otherReadings)));
        }

        /** {@link StandingAtAPoint#met}, of this line. */
        public Met met(List<ObservedInputs> observed, Criterion criterion) {
            return StandingAtAPoint.met(line, decides, reached, observed, criterion,
                    new Arrival(watched, asAClass));
        }

        /** {@link StandingAtAPoint#valuesOf}, of this line. */
        public RowsRead valuesOf(List<ObservedInputs> observed) {
            return StandingAtAPoint.valuesOf(line, decides, reached, observed,
                    new Arrival(watched, asAClass), Optional.empty());
        }

        /**
         * What the readings of the rows that stand at {@code criterion}'s point read as, and
         * nothing of the readings that do not.
         *
         * <p>For a caller that holds the numbers of the rows at a point to the line: a row stands
         * there by one of its readings, and the numbers of its other readings are not numbers at
         * the point. {@link #valuesOf} reads every reading of the row that reached the rule and
         * leaves it to the caller to know which of them stood, which is the same question asked a
         * second time and answered by whatever the caller made of it.
         */
        public RowsRead valuesAt(List<ObservedInputs> observed, Criterion criterion) {
            return StandingAtAPoint.valuesOf(line, decides, reached, observed,
                    new Arrival(watched, asAClass), Optional.of(criterion));
        }
    }

    /**
     * The other readings of the comparison a line is a reading of, and where each decides, put to
     * rows: a row in one of those cases is a row of that reading.
     *
     * <p>Put to rows once, when a point of a class first asks, and shared by every point and every
     * row asked after: a border none of whose classes lies outside its case never pays for it.
     */
    public static final class OtherReadings {

        private final Supplier<List<MeasuredInput.BorderReading>> making;
        private List<WhereAPartDecides.AskedOfRows> asked;

        private OtherReadings(Supplier<List<MeasuredInput.BorderReading>> making) {
            this.making = making;
        }

        /** The readings {@code making} names, worked out when first asked. */
        public static OtherReadings of(Supplier<List<MeasuredInput.BorderReading>> making) {
            return new OtherReadings(making);
        }

        /**
         * Where each of these readings decides, as the propositions {@link #askedOfRows} asks of a
         * row: a row at one of them is a row of that reading and at no class of this one.
         */
        public List<Proposition> cases() {
            return making.get().stream()
                    .map(each -> each.border().origin())
                    .filter(LineOrigin.ComparisonOrigin.class::isInstance)
                    .map(LineOrigin.ComparisonOrigin.class::cast)
                    .flatMap(each -> each.part().stream())
                    .map(WhereAPartDecides::decides)
                    .toList();
        }

        private List<WhereAPartDecides.AskedOfRows> askedOfRows() {
            if (asked == null) {
                asked = making.get().stream()
                        .flatMap(each -> whereItDecides(each).stream()).toList();
            }
            return asked;
        }
    }

    /**
     * What a row has to be, beside lying in the class, to be at a point of a class a line cuts.
     *
     * @param holds  whether the class is the one where the rule holds
     * @param others the other readings of the same comparison
     */
    private record AsAClass(boolean holds, OtherReadings others) {}

    /**
     * What a run has to have done at the places it is recorded at for a row to have reached the
     * rule.
     *
     * @param watched  every place a run through the rule is recorded; empty where writing the
     *                 value is the whole of reaching it
     * @param asAClass for a point of a class the line cuts, what else a row is held to; empty
     *                 where any answer reaches it
     */
    private record Arrival(List<ConditionOutcomeSite> watched, Optional<AsAClass> asAClass) {

        /**
         * Whether the run got to the rule, and for a point of a class whether it got the answer the
         * class says out of it.
         *
         * <p>The run's record is of the places the comparison is made at, which are the copies of
         * it, and not of the element a reading chose. All of them are read before any answer is:
         * an answer at one place says nothing of which application belongs to the element while
         * another place answered the other way. Where every application anywhere came out as the
         * class says, the answer is that. Where all came out the other way, or none was made, it
         * is no. Where applications came out both ways ({@link
         * RulesTaken.ExecutionEvidence#BOTH_WAYS}), at one place or between places, or the visits
         * to a place were not all kept, the record does not say which application belongs to the
         * element: that is not told, and is neither of the others.
         */
        Arrived by(AlignedObservation account) {
            return arrivedAt(watched, asAClass.map(AsAClass::holds), account);
        }

        List<WhereAPartDecides.AskedOfRows> elsewhere() {
            return asAClass.map(as -> as.others().askedOfRows()).orElse(List.of());
        }
    }

    /**
     * What {@code account} says of a comparison recorded at {@code watched}: whether it was made,
     * and where {@code holds} is given, whether every application of it came out that way.
     *
     * <p>Every place is read before an answer is given. The places are the copies of one
     * comparison, and a record of any one says nothing of which application belongs to the
     * element a reading chose while another place answered the other way.
     */
    static Arrived arrivedAt(List<ConditionOutcomeSite> watched, Optional<Boolean> holds,
                             AlignedObservation account) {
        if (holds.isEmpty()) {
            return gotAnAnswerOutOfTheRule(watched, account) ? Arrived.MATCHED : Arrived.MISSED;
        }
        boolean asTheClassSays = false;
        boolean theOtherWay = false;
        boolean untold = false;
        for (ConditionOutcomeSite site : watched) {
            RulesTaken.ExecutionEvidence seen = RulesTaken.ExecutionEvidence.of(
                    account.saw(site, holds.get()), account.saw(site, !holds.get()));
            asTheClassSays |= seen == RulesTaken.ExecutionEvidence.AS_THE_RULE_SAYS;
            theOtherWay |= seen == RulesTaken.ExecutionEvidence.THE_OTHER_WAY;
            untold |= seen == RulesTaken.ExecutionEvidence.BOTH_WAYS
                    || (seen != RulesTaken.ExecutionEvidence.UNOBSERVED
                            && !account.keptEveryVisit(site));
        }
        if (untold || (asTheClassSays && theOtherWay)) {
            return new Arrived.Untold(Set.of(new ReadingGap.ReachNotRead(
                    ReadingGap.ReachNotRead.Why.APPLICATIONS_NOT_TOLD_APART)));
        }
        return asTheClassSays ? Arrived.MATCHED : Arrived.MISSED;
    }

    /**
     * What a run's record says of the comparison a point is read at, in the three answers it can
     * give.
     *
     * <p>Named for the record and not for the point: whether a row stands at a point is {@link Met},
     * and this is one thing it is made of. Reading one for the other is what these names keep apart.
     */
    sealed interface Arrived {

        Arrived MATCHED = new Matched();

        Arrived MISSED = new Missed();

        /** The run made the comparison, and for a point of a class every time as the class says. */
        record Matched() implements Arrived {}

        /** It did not make it, or it came out another way every time. */
        record Missed() implements Arrived {}

        /** The record does not say which application belongs to the element a reading chose. */
        record Untold(Set<ReadingGap> why) implements Arrived {}
    }

    private static Met met(MeasuredInput.BorderReading line,
                           Optional<WhereAPartDecides.AskedOfRows> decides, MetOnARow reached,
                           List<ObservedInputs> observed, Criterion criterion,
                           Arrival arrival) {
        List<ConditionOutcomeSite> watched = arrival.watched();
        BorderQuantity quantity = line.quantity();
        BehaviorInputs where = line.subject().inputs();
        Set<ReadingGap> unreadable = new LinkedHashSet<>();
        boolean unwatched = false;
        ReadingsTried readTo = ReadingsTried.EVERY_ONE;
        for (ObservedInputs one : observed) {
            // A row has more than one value at a position inside a container, and standing at a point
            // is one element standing there. Asked for one value, such a row answered with none and
            // every point on such a line came back undecided — a measurement that could not look,
            // said of a row that wrote the values plainly.
            // The first run of the row says which containers the line's positions are inside, and
            // the readings are tried under each choice of an element of each.
            boolean stands = false;
            Set<ReadingGap> stopped = new LinkedHashSet<>();
            Readings readings =
                    readings(where, one, quantity, decides, arrival.elsewhere(), watched);
            List<BorderQuantity.Observation> tried = readings.tried();
            for (int which = 0; which < tried.size(); which++) {
                switch (stoodAt(quantity, criterion, tried.get(which), decides, reached,
                        arrival.elsewhere())) {
                    case Stood.Yes _ -> stands = true;
                    case Stood.No _ -> { }
                    case Stood.CouldNotTell it -> stopped.addAll(it.why());
                }
                if (stands) {
                    break;
                }
            }
            if (stands) {
                if (watched.isEmpty()) {
                    return Met.REACHED;   // writing the value is the whole of what there is to reach
                }
                switch (one.watched()) {
                    case Generator.Watched.Ran(var account) -> {
                        switch (arrival.by(account)) {
                            case Arrived.Matched _ -> {
                                return Met.REACHED;
                            }
                            case Arrived.Untold it -> unreadable.addAll(it.why());
                            case Arrived.Missed _ -> { }
                        }
                    }
                    // It stands where the line is and nothing watched it get there. Said rather
                    // than counted as a row that did not reach the comparison: a run that reached
                    // nothing is something this found out, and a run nobody watched is not.
                    case Generator.Watched.NoAccount _, Generator.Watched.NotRun _ ->
                            unwatched = true;
                }
            }
            // And where none of them stood there, whether there were others to try. Asked of the
            // rows that came to nothing and of no others: a row that stood at the point was answered
            // by the reading that stood, and the readings after it are not ones this went without.
            if (!stands) {
                readTo = readTo.and(readings.whether());
            }
            unreadable.addAll(stopped);
        }
        // Every reason any row met, the way one reading collects every reason its terms met. A
        // point tried against several rows is one this could not tell about for whatever stopped
        // any of them, and taking the strongest would say which row this walk began with.
        if (!unreadable.isEmpty() || readTo instanceof ReadingsTried.StoppedAtTheLimit) {
            return new Met.CouldNotTell(unreadable, readTo);
        }
        return unwatched ? Met.NOT_WATCHED : Met.NOT_AT_POINT;
    }

    /**
     * Whether one reading of a row stands at a point, which is the one definition both
     * {@link #met} and {@link AtALine#valuesAt} ask: asked twice in two places, the reading that was found
     * to stand and the reading whose numbers were taken could be two.
     */
    private sealed interface Stood {

        /** The reading stands at the point, and the rule's comparison got an answer through it. */
        record Yes() implements Stood {}

        /** It does not. */
        record No() implements Stood {}

        /** Nothing could say, and why. */
        record CouldNotTell(Set<ReadingGap> why) implements Stood {}
    }

    /**
     * Whether a reading of a row stands at {@code criterion}'s point of the quantity and got an
     * answer out of the line's rule there.
     */
    private static Stood stoodAt(BorderQuantity quantity, Criterion criterion,
                                 BorderQuantity.Observation reading,
                                 Optional<WhereAPartDecides.AskedOfRows> decides,
                                 MetOnARow reached,
                                 List<WhereAPartDecides.AskedOfRows> elsewhere) {
        return switch (quantity.standsAt(criterion, reading)) {
            // A reading that could not look. What the row wrote nothing at is not among these: the
            // quantity answers for the row there, since it is the quantity that knows whether a
            // position it wrote nothing at leaves it a value.
            case BorderQuantity.Stands.CouldNotTell it -> new Stood.CouldNotTell(it.why());
            case BorderQuantity.Stands.No _ -> new Stood.No();
            case BorderQuantity.Stands.Yes _ -> answersHere(reading, decides, reached, elsewhere);
        };
    }

    /**
     * Whether a reading of a row is one the line's rule got an answer on.
     *
     * <p>For a line of a statement of several, only somewhere the statement turns on it: a row the
     * statement answers alike on both sides of the line stands at the line and says nothing about
     * it. And only through an element a run compared anything on: the run getting an answer out of
     * the rule on another element says nothing of this one.
     *
     * <p>For a point of a class, in no case another reading of the comparison decides in
     * ({@code elsewhere}): there the row belongs to that reading.
     */
    private static Stood answersHere(BorderQuantity.Observation reading,
                                     Optional<WhereAPartDecides.AskedOfRows> decides,
                                     MetOnARow reached,
                                     List<WhereAPartDecides.AskedOfRows> elsewhere) {
        for (WhereAPartDecides.AskedOfRows other : elsewhere) {
            switch (other.at(reading)) {
                case WhereAPartDecides.AtARow.Decides _ -> {
                    return new Stood.No();
                }
                case WhereAPartDecides.AtARow.CouldNotTell(var why) -> {
                    return new Stood.CouldNotTell(why);
                }
                case WhereAPartDecides.AtARow.DecidesNothing _ -> { }
            }
        }
        return answersHere(reading, decides, reached);
    }

    private static Stood answersHere(BorderQuantity.Observation reading,
                                     Optional<WhereAPartDecides.AskedOfRows> decides,
                                     MetOnARow reached) {
        return switch (decides.map(asked -> asked.at(reading))
                .orElse(WhereAPartDecides.AtARow.DECIDES)) {
            case WhereAPartDecides.AtARow.Decides _ -> switch (reached.at(reading)) {
                case AStatementAtARow.Answer.Holds _ -> new Stood.Yes();
                case AStatementAtARow.Answer.Fails _ -> new Stood.No();
                case AStatementAtARow.Answer.CouldNotTell(var why) -> new Stood.CouldNotTell(why);
            };
            case WhereAPartDecides.AtARow.DecidesNothing _ -> new Stood.No();
            case WhereAPartDecides.AtARow.CouldNotTell(var why) -> new Stood.CouldNotTell(why);
        };
    }

    /**
     * What every reading of every row reads as at one line's quantity.
     *
     * <p>The same walk as {@link #met} and a different question. That one asks whether some reading
     * of some row stands where the line is, and stops at the first that does; this asks what the
     * numbers are, of all of them, because what a caller does with them is hold the rows against a
     * line the model did not draw — and a line nobody wrote is told from the one that was written by
     * whichever row answers differently, so leaving a row out leaves out what would have told them
     * apart.
     *
     * <p><b>Which is why this says what it went without.</b> A row read is a constraint on the lines
     * the rows allow, so fewer rows read is never fewer lines allowed: a caller concluding that the
     * rows leave nothing else standing may do so from part of them, and one naming a line they do
     * leave standing may not. The same asymmetry {@link Met} has, the other way up, and for the same
     * reason — what a partial walk establishes is on the side its constraints push.
     *
     * <p><b>And of the rows that reached the rule, which is the same universe {@link #met} is over.</b>
     * A row that never got an answer out of the comparison says nothing about where its line falls:
     * its values are a point of the input and not an observation of this border, and holding a line
     * against it would rule out a line on the strength of a row that never met one. So the rule is
     * the one a point is met by — where meeting takes the comparison having run, a row is read only
     * where a run was watched getting an answer out of it, and where writing the value is the whole
     * of it, every row is read.
     *
     * <p>A row nothing watched is neither: it may have reached and it may not, and dropping it
     * quietly would leave more lines standing than the rows allow. It is gone without, and this says
     * so.
     *
     * @param watched every place a run through the comparison this line's rule was read from is
     *                recorded, empty where standing at the value is the whole of reaching it
     */
    public static RowsRead valuesOf(MeasuredInput.BorderReading line,
                                    List<ObservedInputs> observed,
                                    List<ConditionOutcomeSite> watched) {
        return putToRows(line, watched).valuesOf(observed);
    }

    private static RowsRead valuesOf(MeasuredInput.BorderReading line,
                                     Optional<WhereAPartDecides.AskedOfRows> decides,
                                     MetOnARow reached, List<ObservedInputs> observed,
                                     Arrival arrival, Optional<Criterion> at) {
        List<ConditionOutcomeSite> watched = arrival.watched();
        // A row's numbers are read position by position, and only a form has positions to read
        // them at. A line on any other quantity is not one another line is written beside, and
        // the reader that would hold one against the rows asks that first.
        if (!(line.quantity() instanceof LinearQuantity quantity)) {
            throw new IllegalArgumentException("a row's numbers are read at a form's positions,"
                    + " and this line is on " + line.quantity());
        }
        BehaviorInputs where = line.subject().inputs();
        List<Map<souther.compiler.inputs.NumericTerm, souther.compiler.numeric.Place>> read =
                new ArrayList<>();
        Set<ReadingGap> unreadable = new LinkedHashSet<>();
        ReadingsTried readTo = ReadingsTried.EVERY_ONE;
        boolean unwatched = false;
        for (ObservedInputs one : observed) {
            if (!watched.isEmpty()) {
                switch (one.watched()) {
                    case Generator.Watched.Ran(var account) -> {
                        switch (arrival.by(account)) {
                            case Arrived.Matched _ -> { }
                            case Arrived.Missed _ -> {
                                continue;   // it ran and never met this rule, so it says nothing
                            }
                            case Arrived.Untold it -> {
                                unreadable.addAll(it.why());
                                continue;
                            }
                        }
                    }
                    case Generator.Watched.NoAccount _, Generator.Watched.NotRun _ -> {
                        unwatched = true;
                        continue;
                    }
                }
            }
            Readings readings =
                    readings(where, one, quantity, decides, arrival.elsewhere(), watched);
            for (int which = 0; which < readings.tried().size(); which++) {
                // Only where the statement turns on the line, and only through an element the run
                // met the rule on: a reading somewhere it does not says nothing about where this
                // line falls, and its values there are no observation of this border. And, where
                // the caller asks about one point, only a reading that stands at it — decided by
                // the definition the walk for whether a row stands there uses.
                BorderQuantity.Observation reading = readings.tried().get(which);
                Stood stood = at.isPresent()
                        ? stoodAt(quantity, at.get(), reading, decides, reached,
                                arrival.elsewhere())
                        : answersHere(reading, decides, reached, arrival.elsewhere());
                switch (stood) {
                    case Stood.Yes _ -> { }
                    case Stood.No _ -> {
                        continue;
                    }
                    case Stood.CouldNotTell it -> {
                        unreadable.addAll(it.why());
                        continue;
                    }
                }
                switch (quantity.valuesOf(quantity.read(reading))) {
                    case ValuesAtARow.Read(Map<souther.compiler.inputs.NumericTerm,
                            souther.compiler.numeric.Place> values) -> read.add(values);
                    // The row has no value at this quantity, which is the row's own answer and
                    // constrains nothing. Left among the reasons, every row that writes nothing
                    // where a line is drawn would hold back a finding about lines it says nothing
                    // about.
                    case ValuesAtARow.NoneHere _ -> { }
                    case ValuesAtARow.CouldNotTell it -> unreadable.addAll(it.why());
                }
            }
            readTo = readTo.and(readings.whether());
        }
        return new RowsRead(read, unreadable, readTo, unwatched);
    }

    /**
     * Where the line {@code line} reads decides, put to rows — or empty where the line is a whole
     * comparison's or no comparison's, and a row standing at it is all there is to ask.
     */
    private static Optional<WhereAPartDecides.AskedOfRows> whereItDecides(
            MeasuredInput.BorderReading line) {
        return line.border().origin() instanceof LineOrigin.ComparisonOrigin comparison
                ? comparison.part().map(part -> part.askedOfRows(line.quantity().behavior(),
                        line.subject()))
                : Optional.empty();
    }

    /**
     * Which elements of the input a run gets an answer out of the rule {@code line} reads on, put to
     * rows: every element a reading can name, for a line no comparison of a body drew.
     */
    private static MetOnARow metOn(MeasuredInput.BorderReading line) {
        ElementsMetOn metOn = line.border().origin() instanceof LineOrigin.ComparisonOrigin drawn
                ? drawn.read().metOn() : ElementsMetOn.EVERY;
        return MetOnARow.of(metOn, line.quantity().behavior(), line.subject().quantities());
    }

    /**
     * What the rows came to at one quantity, and what the walk over them went without.
     *
     * @param each      one entry per reading of a row that read as numbers, in the order they were
     *                  walked. A row with no value at the quantity has no entry and is no absence:
     *                  it says nothing about where any line falls
     * @param why       whatever stopped a reading of a row that was not read
     * @param tried     whether the readings walked are all the readings there are
     * @param unwatched whether some row was left out for nothing having watched its run, so that
     *                  whether it reached the rule could not be told
     */
    public record RowsRead(
            List<Map<souther.compiler.inputs.NumericTerm, souther.compiler.numeric.Place>> each,
            Set<ReadingGap> why, ReadingsTried tried, boolean unwatched) {

        public RowsRead {
            each = List.copyOf(each);
            why = Collections.unmodifiableSet(new LinkedHashSet<>(why));
            if (tried == null) {
                throw new IllegalArgumentException(
                        "a walk over the rows says whether it walked all of them");
            }
        }

        /** Whether every reading of every row that reached the rule was read, which is what a
         *  caller naming a line the rows allow has to have. */
        public boolean everyOne() {
            return why.isEmpty() && !unwatched && tried instanceof ReadingsTried.EveryOne;
        }

        /**
         * These rows and {@code other}'s, which is what two readings of one line read between
         * them: every row of either, whatever either went without, and every reading where both
         * walked every one.
         */
        public RowsRead and(RowsRead other) {
            List<Map<souther.compiler.inputs.NumericTerm, souther.compiler.numeric.Place>> both =
                    new ArrayList<>(each);
            both.addAll(other.each);
            Set<ReadingGap> without = new LinkedHashSet<>(why);
            without.addAll(other.why);
            return new RowsRead(both, without, tried.and(other.tried),
                    unwatched || other.unwatched);
        }
    }

    /**
     * One walk over a row, for the walk that finds the readings of it and for a walk that is one
     * of them.
     *
     * <p>Where the row wrote something and what it wrote there is the same walk both times. What
     * differs is what is made of the answers at a position: the walk finding the readings records
     * what each position holds, and a walk reading the row under one of them takes the element
     * that reading names. So arriving is written once and the making of it is each one's own.
     *
     * <p>What a walk chose is asked only through the row, which hears every asking
     * ({@link RowWalk#consulted}): what is kept for every reading of a row is kept by the choices
     * reading it asked, and an asking it did not hear is a choice an answer turned on unseen.
     */
    abstract static sealed class WalkOfARow implements BorderQuantity.Observation
            permits DiscoveringRow, OneReadingOfARow {

        /** The row, as every walk over it has it. */
        private final RowWalk walk;

        /** What this walk found at each path it was asked about, so that a row read once is read
         *  once however many quantities and items ask it. */
        private final Map<TermPath, Found> found = new HashMap<>();

        /** What the row wrote at a path, and what this walk made of it. Kept together because
         *  both are asked at every asking, and each asking of a table by a path walks the path. */
        private record Found(Written written, WalkResult<ObservationAtPoint> answer) {}

        WalkOfARow(RowWalk walk) {
            this.walk = walk;
        }

        /** The walk over the row this is one of. */
        final RowWalk walk() {
            return walk;
        }

        @Override
        public final Optional<BorderQuantity.SidesOnARun> comparedOnTheRun() {
            return walk.comparedOnTheRun();
        }

        /**
         * The walk this one was made of, with an element of one container chosen: null for a walk
         * made of the row.
         */
        abstract WalkOfARow madeOf();

        /** The container whose element this walk chose and the one it was made of did not. */
        abstract TermPath choosing();

        /** What was being read for every reading of the row when this walk was made, or null. */
        abstract RowWalk.Keeping madeFor();

        @Override
        public final WalkResult<ObservationAtPoint> at(TermPath path) {
            Found had = found.get(path);
            if (had == null) {
                Written written = walk.at(path);
                had = new Found(written, walkedTo(written));
                found.put(path, had);
            }
            // Asked every time, found before or not: the value under this walk's elements is what
            // they are, and an answer read of it turns on them.
            had.written().consultedBy(this);
            return had.answer();
        }

        private WalkResult<ObservationAtPoint> walkedTo(Written written) {
            // Over the arms, so that a walk coming to answer a third way is one this has to be
            // taught about rather than one quietly read as a walk that could not be made.
            return switch (written.found()) {
                // The walk and the type disagree, which is the quantity's to report.
                case WalkResult.CouldNotWalk<List<BehaviorInputs.Occurrence>> _ ->
                        WalkResult.couldNotWalk();
                // The row wrote no element here, which is a row that was read and is the same
                // answer whichever walk asked. What that leaves a quantity is the quantity's to
                // say, and it says it where it knows what the position is worth to the number it
                // is reading.
                case WalkResult.Reached(List<BehaviorInputs.Occurrence> values) ->
                        WalkResult.reached(values.isEmpty()
                                ? ObservationAtPoint.WROTE_NOTHING : standingAmong(written));
            };
        }

        /**
         * What this walk makes of the elements the row wrote at a position it arrived at.
         *
         * @param written what the row wrote there, never none of it
         */
        abstract ObservationAtPoint standingAmong(Written written);

        /**
         * The element this walk chose in each container, none where it chose nothing.
         *
         * <p>Read by the row, which hears what is asked of it; a reader of the walk asks the row.
         */
        abstract Map<TermPath, Integer> chosen();

        /** The element this walk chose in {@code container}, or null, asked through the row. */
        private Integer chosenIn(TermPath container) {
            walk.consulted(this, List.of(container));
            return chosen().get(container);
        }

        /** Every element the row wrote in {@code container} under this walk's other choices,
         *  each read as this walk with that one chosen, made while what is read for every
         *  reading is read. */
        private List<OneReadingOfARow> eachChosen(TermPath container, Written elements) {
            List<OneReadingOfARow> out = new ArrayList<>();
            for (int element : elements.elementsBeside(container, this)) {
                Map<TermPath, Integer> choosing = new LinkedHashMap<>(chosen());
                choosing.put(container, element);
                out.add(new OneReadingOfARow(walk, choosing, this, container, walk.keeping()));
            }
            return out;
        }

        /**
         * Every element the row wrote in {@code container}, each read as this walk with that
         * element chosen too.
         *
         * <p>The container is asked first the way any position is, so a walk finding the readings
         * learns from it which containers the container itself stands inside — and not the
         * container counted, whose elements are read together and never one reading apiece.
         *
         * <p>Every element, whichever of them this walk chose: a statement about the elements is
         * about all of them, and the one a reading stands at is one of those.
         */
        @Override
        public final WalkResult<List<BorderQuantity.Observation>> eachElementOf(
                TermPath container) {
            if (at(container) instanceof WalkResult.CouldNotWalk<ObservationAtPoint>) {
                return WalkResult.couldNotWalk();
            }
            Written elements = walk.at(container.element());
            if (!elements.walked()) {
                return WalkResult.couldNotWalk();
            }
            return WalkResult.reached(List.copyOf(eachChosen(container, elements)));
        }

        /**
         * Whether the element this reading chose in {@code container} is the last of those that
         * hold the value it holds at {@code position}.
         *
         * <p>Asked of every occurrence of the position the reading is consistent with, so an
         * element of another container this reading chose against is not a later element of this
         * one's. A reading that chose no element of the container has none to be last.
         *
         * <p>A value any part of which could not be read, in this element or in one after it, is no
         * value to be equal or unequal to another: it shows that the element is not the last only
         * by another after it that was read whole and is equal, and shows that it is by nothing.
         * What stopped it is said ({@link ReadingGap#ofAComparisonOf}).
         *
         * <p>Worked out for every element of the occurrence at once, and kept for every reading
         * that chose alike where the working out asked.
         */
        @Override
        public final Lastness lastToHold(TermPath container, TermPath position) {
            Integer mine = chosenIn(container);
            if (mine == null) {
                return new Lastness.CouldNotTell(ReadingGap.COULD_NOT_WALK);
            }
            Map<Integer, Lastness> each = walk.kept(new OrderOfAKey(container, position), this,
                    () -> lastnessOfEach(container, position));
            Lastness answer = each.get(mine);
            return answer != null ? answer : new Lastness.CouldNotTell(ReadingGap.COULD_NOT_WALK);
        }

        /**
         * Whether each element of the occurrence of {@code container} this reading is in is the
         * last to hold the value it holds at {@code position}, by the element; none for an element
         * that holds nothing there, or for every element where the walk could not be made.
         *
         * <p>From the last element to the first, carrying what the elements after each hold: the
         * values read whole, and the first in order that was not. Where the walk reads this order
         * the other way, from the first to the last, so "after" is "before".
         */
        private Map<Integer, Lastness> lastnessOfEach(TermPath container, TermPath position) {
            Written written = walk.at(position);
            if (!written.walked()) {
                return Map.of();
            }
            TreeMap<Integer, List<ObservedValue>> byElement = new TreeMap<>();
            for (BehaviorInputs.Occurrence each : written.besideOf(container, this)) {
                Integer taken = each.at().elementAt(container);
                if (taken != null) {
                    byElement.computeIfAbsent(taken, _ -> new ArrayList<>()).add(each.value());
                }
            }
            Map<Integer, Lastness> out = new HashMap<>();
            Set<ObservedValue> readAfter = new HashSet<>();
            ReadingGap firstNotReadAfter = null;
            for (Map.Entry<Integer, List<ObservedValue>> element
                    : (walk.readsTheOtherWay(new OrderOfAKey(container, position)) ? byElement
                            : byElement.descendingMap()).entrySet()) {
                ObservedValue held = element.getValue().getLast();
                ReadingGap ownNotRead = ReadingGap.ofAComparisonOf(held);
                // One after it that was read and is equal settles it, whatever else was not.
                out.put(element.getKey(), ownNotRead != null ? new Lastness.CouldNotTell(ownNotRead)
                        : readAfter.contains(held) ? new Lastness.NotLast()
                        : firstNotReadAfter != null ? new Lastness.CouldNotTell(firstNotReadAfter)
                        : new Lastness.Last());
                ReadingGap firstNotReadHere = null;
                for (ObservedValue value : element.getValue()) {
                    ReadingGap notRead = ReadingGap.ofAComparisonOf(value);
                    if (notRead == null) {
                        readAfter.add(value);
                    } else if (firstNotReadHere == null) {
                        firstNotReadHere = notRead;
                    }
                }
                if (firstNotReadHere != null) {
                    firstNotReadAfter = firstNotReadHere;
                }
            }
            return out;
        }

        /**
         * The occurrence of {@code container} this reading is in — what it chose of every other
         * container, the items of the order a reading chose and no other order's — and which of
         * its elements it chose.
         */
        @Override
        public final WalkResult<BorderQuantity.Among> among(TermPath container) {
            if (at(container) instanceof WalkResult.CouldNotWalk<ObservationAtPoint>
                    || !walk.at(container.element()).walked()) {
                return WalkResult.couldNotWalk();
            }
            return WalkResult.reached(new BorderQuantity.Among(chosenIn(container)));
        }

        /** Asked through the row, as every other choice is. */
        @Override
        public final boolean choseAnElement() {
            walk.consultedWhetherAny(this);
            return !chosen().isEmpty();
        }

        /** The elements of {@code container} the row wrote under what this reading chose of
         *  every other container, each read with it chosen. */
        @Override
        public final WalkResult<List<BorderQuantity.AnElement>> elementsOf(TermPath container) {
            Written elements = walk.at(container.element());
            if (!elements.walked()) {
                return WalkResult.couldNotWalk();
            }
            List<BorderQuantity.AnElement> out = new ArrayList<>();
            for (OneReadingOfARow one : eachChosen(container, elements)) {
                out.add(new BorderQuantity.AnElement(one.chosen().get(container), one));
            }
            return WalkResult.reached(List.copyOf(out));
        }

        @Override
        public final <T> T keptOf(BorderQuantity.ReadAlike<T> asked) {
            return walk.kept(asked, this, () -> asked.readAt(this));
        }

        /**
         * Every value the row wrote at {@code path}, whichever elements a reading chose.
         *
         * <p>No choosing and nothing recorded to choose between. A number taken over a run is over
         * all of them, so there is no element for a reading to have picked and no second reading to
         * try — which is why this is one answer for both walks and names no container.
         *
         * <p>An empty run is a row that wrote no element, and a total over nothing is what the walk
         * starts from rather than a value nobody could read. So the row is not marked as having
         * written nothing here: it wrote a container, and what it holds is none.
         */
        @Override
        public final WalkResult<List<ObservedValue>> everyValueAt(TermPath path) {
            // The walk's own answer handed on, which is the quantity's to report where it could not
            // be taken, as it is for the one value a place holds.
            return switch (walk.at(path).found()) {
                case WalkResult.CouldNotWalk<List<BehaviorInputs.Occurrence>> _ ->
                        WalkResult.couldNotWalk();
                case WalkResult.Reached(List<BehaviorInputs.Occurrence> values) ->
                        WalkResult.reached(values.stream().map(BehaviorInputs.Occurrence::value)
                                .toList());
            };
        }
    }

    /**
     * The walk a row's readings are found by.
     *
     * <p>How many elements each container holds is what says how many readings of the row there
     * are, and only reading the row says it: which positions a line is over is the quantity's to
     * name as it asks. So the row is walked once choosing nothing, and what it met in each container
     * is this walk's answer — settled when the walk is over, and no reading made from it writes to
     * it.
     *
     * <p>Choosing nothing, the value it takes at a position is the first the row wrote there. That
     * makes it the reading of the row wherever the positions are inside no container; where they are
     * inside one it is a walk made to find them and none of the readings it finds.
     */
    static final class DiscoveringRow extends WalkOfARow {

        /** How many elements each container was found to hold, in the order the walk met them,
         *  which is the order the readings are taken in. */
        private final Map<TermPath, Integer> containers = new LinkedHashMap<>();

        DiscoveringRow(RowWalk walk) {
            super(walk);
        }

        @Override
        ObservationAtPoint standingAmong(Written written) {
            List<BehaviorInputs.Occurrence> values = written.values();
            // Each occurrence's containers outermost first, so that the order the containers are
            // first met in is the order they nest in and the readings built over them are tried in
            // one order.
            for (BehaviorInputs.Occurrence each : values) {
                for (ElementsTaken.Taken taken : each.at().outermostFirst()) {
                    containers.merge(taken.container(), taken.element() + 1, Math::max);
                }
            }
            // Nothing is chosen, so nothing here is ruled out and the first of them is the answer.
            // Where there is more than one the position is inside a container, the containers are
            // not empty, and this walk is no reading of the row: which of them it took is read by
            // nobody.
            return new ObservationAtPoint.Value(values.getFirst().value());
        }

        @Override
        Map<TermPath, Integer> chosen() {
            return Map.of();
        }

        @Override
        WalkOfARow madeOf() {
            return null;
        }

        @Override
        TermPath choosing() {
            return null;
        }

        @Override
        RowWalk.Keeping madeFor() {
            return null;
        }

        /** What the containers hold, as of a walk that is over. */
        Map<TermPath, Integer> containers() {
            return Collections.unmodifiableMap(new LinkedHashMap<>(containers));
        }
    }

    /**
     * One row's values under one reading of it: an element chosen in each container the line's
     * positions are inside.
     *
     * <p>A row standing at a point is one of its readings standing there, and a reading has to be
     * one: two positions under one person are that person's two values, and offering the first
     * person's age beside the second person's status would have a row stand at a point neither
     * element is at. So an element is chosen per container and every position takes the one chosen
     * for the containers it is inside — the same rule a pair of classes is read by, since it is the
     * same question. A map's key and its value are inside the same map, so they take one entry.
     *
     * <p>Which readings there are is not known before the quantity has asked, since which positions
     * a line is over is its to say. So {@link DiscoveringRow} asks it once and every choice the
     * containers it found allow is a reading made here, tried until one stands or they are used up.
     */
    static final class OneReadingOfARow extends WalkOfARow {

        /** The element chosen in each container, for this reading. */
        private final Map<TermPath, Integer> chosen;

        private final WalkOfARow madeOf;
        private final TermPath choosing;
        private final RowWalk.Keeping madeFor;

        /** A reading of the row itself. */
        OneReadingOfARow(RowWalk walk, Map<TermPath, Integer> chosen) {
            this(walk, chosen, null, null, null);
        }

        /**
         * A walk made of {@code madeOf} with an element of {@code choosing} chosen too, while
         * {@code madeFor} was being read for every reading of the row, or none was.
         */
        OneReadingOfARow(RowWalk walk, Map<TermPath, Integer> chosen, WalkOfARow madeOf,
                         TermPath choosing, RowWalk.Keeping madeFor) {
            super(walk);
            this.chosen = chosen;
            this.madeOf = madeOf;
            this.choosing = choosing;
            this.madeFor = madeFor;
        }

        @Override
        WalkOfARow madeOf() {
            return madeOf;
        }

        @Override
        TermPath choosing() {
            return choosing;
        }

        @Override
        RowWalk.Keeping madeFor() {
            return madeFor;
        }

        @Override
        ObservationAtPoint standingAmong(Written written) {
            ObservedValue value = written.under(this);
            // None here under this reading is not a stop: the reading names an element this
            // position does not have, and another reading is where its values are.
            return value != null ? new ObservationAtPoint.Value(value)
                    : ObservationAtPoint.ANOTHER_READING;
        }

        @Override
        Map<TermPath, Integer> chosen() {
            return chosen;
        }
    }

    /**
     * One row, as every walk over it reads it: what it wrote at each path, walked once, and what
     * was read of its elements together, for every reading of it.
     *
     * <p>Shared by the walk that finds the readings and every reading made of it, since what a row
     * wrote does not turn on which element a reading chose. Made for one row and dropped with it:
     * nothing here is asked of another row, and what a line is read with lives longer than any one
     * of the rows it is read on.
     */
    static final class RowWalk {

        private final BehaviorInputs where;
        private final ObservedInputs observed;

        /** What each type is under the declarations, for every walk into the row. */
        private final Map<Type, TypeView> views = new HashMap<>();

        private final Map<TermPath, Written> written = new HashMap<>();

        /**
         * What was read of the row together: by the question; then by what reading it asked of
         * the asking walk's choices; then by what those were.
         */
        private final Map<Object, Map<Asking, Map<Choosing, Object>>> kept = new HashMap<>();

        /** What is being read for every reading of the row, the latest first. */
        private final Deque<Keeping> keeping = new ArrayDeque<>();

        /** How many times a value the row wrote was looked at or looked up, over every walk. */
        private long lookedAt;

        /** How many answers were read rather than taken from those kept. */
        private long read;

        /**
         * The orders read with the first element of a key as its entry rather than the last: the
         * row as a map filed the other way round would hold it. None for a row read as it is.
         */
        private final Set<OrderOfAKey> readTheOtherWay;

        /** Where a run through the comparison the line being read was drawn from is recorded,
         *  none for a line on no comparison a run records. */
        private final List<ConditionOutcomeSite> recordedAt;

        /** What {@link #comparedOnTheRun} answered, once it was asked; null before. */
        private Optional<BorderQuantity.SidesOnARun> comparedOnTheRun;

        RowWalk(BehaviorInputs where, ObservedInputs observed) {
            this(where, observed, Set.of());
        }

        RowWalk(BehaviorInputs where, ObservedInputs observed, Set<OrderOfAKey> readTheOtherWay) {
            this(where, observed, readTheOtherWay, List.of());
        }

        RowWalk(BehaviorInputs where, ObservedInputs observed, Set<OrderOfAKey> readTheOtherWay,
                List<ConditionOutcomeSite> recordedAt) {
            this.where = where;
            this.observed = observed;
            this.readTheOtherWay = Set.copyOf(readTheOtherWay);
            this.recordedAt = List.copyOf(recordedAt);
        }

        /**
         * What the sides of the comparison came to on the row's run, every visit kept at every
         * place it is recorded — or empty where the row's run was not watched.
         */
        Optional<BorderQuantity.SidesOnARun> comparedOnTheRun() {
            // Every reading of the row asks, and the run is the row's: put together once.
            if (comparedOnTheRun == null) {
                if (observed.watched() instanceof Generator.Watched.Ran(AlignedObservation run)) {
                    List<SeenComparison> out = new ArrayList<>();
                    recordedAt.forEach(site -> out.addAll(run.comparedAt(site)));
                    // Every place on its own word: one place visited past the kept leaves the
                    // comparison's visits short, whatever the others kept between them.
                    comparedOnTheRun = Optional.of(new BorderQuantity.SidesOnARun(out,
                            recordedAt.stream().allMatch(run::keptEveryVisit)));
                } else {
                    comparedOnTheRun = Optional.empty();
                }
            }
            return comparedOnTheRun;
        }

        /** Whether this walk reads {@code order} the other way round. */
        boolean readsTheOtherWay(OrderOfAKey order) {
            return readTheOtherWay.contains(order);
        }

        /** What the row wrote at {@code path}. */
        Written at(TermPath path) {
            Written known = written.get(path);
            if (known == null) {
                known = new Written(this, where.occurrencesAt(observed.inputs(), path, views));
                written.put(path, known);
            }
            return known;
        }

        /**
         * What {@code read} answers for {@code asker}, read once for every walk of the row that
         * chose alike wherever reading it asked what was chosen.
         *
         * <p>Which choices an answer turns on is not said beside it: reading it is what asks them,
         * through the row ({@link #consulted}), so what it is kept by is what it asked. A walk
         * that chose alike in all of those reads it the same way and comes to the same answer, so
         * it is handed this one. What it asked is asked again of whatever is being read around it,
         * which turns on it too.
         *
         * <p>{@code question} is what the answer is of: two equal questions are asked alike, and
         * what one answers is never taken for another's, so a question names one kind of answer.
         */
        @SuppressWarnings("unchecked")
        <T> T kept(Object question, WalkOfARow asker, Supplier<T> read) {
            Map<Asking, Map<Choosing, Object>> known = kept.get(question);
            if (known != null) {
                for (Map.Entry<Asking, Map<Choosing, Object>> each : known.entrySet()) {
                    Object answer = each.getValue().get(each.getKey().of(asker));
                    if (answer != null) {
                        each.getKey().askedOf(asker, this);
                        return answer == NONE ? null : (T) answer;
                    }
                }
            }
            // Read and then put, never computed in place: reading the answer may ask the row for
            // another one kept beside it.
            Keeping reading = new Keeping(asker);
            keeping.push(reading);
            T answer;
            try {
                answer = read.get();
            } finally {
                keeping.pop();
                reading.done = true;
            }
            this.read++;
            Asking asking = new Asking(Set.copyOf(reading.asked), reading.whetherAny);
            kept.computeIfAbsent(question, _ -> new HashMap<>())
                    .computeIfAbsent(asking, _ -> new HashMap<>())
                    .put(asking.of(asker), answer == null ? NONE : answer);
            asking.askedOf(asker, this);
            return answer;
        }

        /**
         * That {@code by} asked whether it chose an element of any container: heard by everything
         * being read for a walk it has its choices from, which then turns on that too.
         */
        void consultedWhetherAny(WalkOfARow by) {
            for (Keeping each : keeping) {
                if (madeFrom(by, each.asker)) {
                    each.whetherAny = true;
                }
            }
            for (WalkOfARow link = by; link != null; link = link.madeOf()) {
                Keeping madeFor = link.madeFor();
                if (madeFor != null && madeFor.done && madeFrom(by, madeFor.asker)
                        && !madeFor.whetherAny) {
                    throw new IllegalStateException("an answer kept for every reading of a row"
                            + " asked whether an element was chosen after it was kept");
                }
            }
        }

        /** Whether {@code by} is {@code from} or was made of it. */
        private static boolean madeFrom(WalkOfARow by, WalkOfARow from) {
            for (WalkOfARow link = by; link != null; link = link.madeOf()) {
                if (link == from) {
                    return true;
                }
            }
            return false;
        }

        /**
         * What reading an answer asked of the asking walk's choices: what it chose in each of
         * {@code containers}, and whether it chose any.
         */
        private record Asking(Set<TermPath> containers, boolean whetherAny) {

            /** What {@code walk} chose where this asks; a container it chose nothing in is in
             *  none of what it chose. */
            Choosing of(WalkOfARow walk) {
                Map<TermPath, Integer> elements = new HashMap<>();
                for (TermPath container : containers) {
                    Integer element = walk.chosen().get(container);
                    if (element != null) {
                        elements.put(container, element);
                    }
                }
                return new Choosing(elements, whetherAny ? !walk.chosen().isEmpty() : null);
            }

            /** The same asked of {@code walk} again, for whatever is being read around it. */
            void askedOf(WalkOfARow walk, RowWalk row) {
                row.consulted(walk, containers);
                if (whetherAny) {
                    row.consultedWhetherAny(walk);
                }
            }
        }

        /**
         * What a walk chose where an answer asked: the element in each container, and whether it
         * chose any where that was asked, or null where it was not.
         */
        private record Choosing(Map<TermPath, Integer> elements, Boolean any) {

            Choosing {
                elements = Map.copyOf(elements);
            }
        }

        /**
         * That {@code by} asked what it chose in each of {@code containers}: heard by everything
         * being read for a walk {@code by} has that choice from.
         *
         * <p>And refused where it is asked after an answer was kept, by a walk made while it was
         * read, of a choice that answer was not kept by — an answer handing over something that
         * reads the row later. What it reads then is the walk's it was read for, and a walk handed
         * the answer for choosing alike elsewhere would be told of a choice it did not make.
         */
        void consulted(WalkOfARow by, Collection<TermPath> containers) {
            for (TermPath container : containers) {
                for (Keeping each : keeping) {
                    if (chosenFrom(by, container, each.asker)) {
                        each.asked.add(container);
                    }
                }
                for (WalkOfARow link = by; link != null; link = link.madeOf()) {
                    Keeping madeFor = link.madeFor();
                    if (madeFor != null && madeFor.done && chosenFrom(by, container, madeFor.asker)
                            && !madeFor.asked.contains(container)) {
                        throw new IllegalStateException("an answer kept for every reading of a"
                                + " row read what was chosen in " + container + " after it was"
                                + " kept, by " + madeFor.asked);
                    }
                }
            }
        }

        /** What is being read for every reading now, the latest, or null. */
        Keeping keeping() {
            return keeping.peek();
        }

        /**
         * Whether what {@code by} chose in {@code container} is what {@code from} chose: it is
         * {@code from} or was made of it, and nothing between chose that container afresh.
         */
        private static boolean chosenFrom(WalkOfARow by, TermPath container, WalkOfARow from) {
            for (WalkOfARow link = by; link != null; link = link.madeOf()) {
                if (link == from) {
                    return true;
                }
                if (container.equals(link.choosing())) {
                    return false;
                }
            }
            return false;
        }

        /** What is kept for a question answered with nothing, which a map cannot hold. */
        private static final Object NONE = new Object();

        /**
         * What is being read for every reading of the row, for the walk that asked it, and what
         * was asked of that walk's choices while it was.
         */
        static final class Keeping {

            private final WalkOfARow asker;
            private final Set<TermPath> asked = new HashSet<>();
            private boolean whetherAny;
            private boolean done;

            Keeping(WalkOfARow asker) {
                this.asker = asker;
            }
        }

        /** How many times a value the row wrote was looked at or looked up, over every walk. */
        long occurrencesLookedAt() {
            return lookedAt;
        }

        /** How many answers kept for every reading of the row were read. */
        long answersRead() {
            return read;
        }
    }

    /**
     * What a row wrote at one path, and the same found by the elements taken to reach each value.
     *
     * <p>A reading takes the value under the elements it chose, and a reader of an occurrence
     * takes every value under what was chosen beside one container. Looked up rather than looked
     * for, each is an index made once of every occurrence, so a row read once per element of a
     * container does not look at every element for each.
     *
     * <p>By which of the containers a walk chose an element in, since a walk that chose none in
     * one takes a value under any of its elements: the walk finding a row's readings chooses
     * nothing, and an element it reads chooses only its own container.
     *
     * <p>And by how deep each value was reached. A value that was not read whole stands at every
     * path below it, reached through the containers it was taken from and none further, and is
     * under every element of the containers it never entered
     * ({@link BehaviorInputs#occurrencesAt}).
     * So the values at one path were reached through the first so many of the same containers,
     * and a choice is looked up at each depth there is. Which of those it takes is the first in the
     * order the row wrote them, whatever its depth, as a walk looking through them would.
     */
    static final class Written {

        private final RowWalk walk;
        private final WalkResult<List<BehaviorInputs.Occurrence>> found;

        /** The containers the deepest value here was reached through, outermost first, and how
         *  many of them each depth there is enters; worked out when first asked. */
        private List<TermPath> containers;
        private List<Integer> depths;

        /** Where each value stands in the order the row wrote them, by how deep it was reached and
         *  the elements it was taken from in the containers a walk named, by those containers. */
        private final Map<List<Boolean>, Map<ReachedAtDepth, List<Integer>>> byElements =
                new HashMap<>();

        Written(RowWalk walk, WalkResult<List<BehaviorInputs.Occurrence>> found) {
            this.walk = walk;
            this.found = found;
        }

        /** What the walk to the path came to. */
        WalkResult<List<BehaviorInputs.Occurrence>> found() {
            return found;
        }

        /** Whether the walk reached the path. */
        boolean walked() {
            return found instanceof WalkResult.Reached<List<BehaviorInputs.Occurrence>>;
        }

        /** The values found, for a walk that reached the path. */
        List<BehaviorInputs.Occurrence> values() {
            return ((WalkResult.Reached<List<BehaviorInputs.Occurrence>>) found).value();
        }

        /**
         * That {@code by} asked what it chose in the containers the values here were reached
         * through, where there are values: which value stands under it turns on those and on
         * nothing else.
         */
        void consultedBy(WalkOfARow by) {
            if (walked() && !values().isEmpty()) {
                walk.consulted(by, containers());
            }
        }

        /** The first value reached through the elements {@code by} chose, or null. */
        ObservedValue under(WalkOfARow by) {
            int first = Integer.MAX_VALUE;
            for (List<Integer> each : atEachDepth(choice(by, null))) {
                walk.lookedAt++;
                first = Math.min(first, each.getFirst());
            }
            return first == Integer.MAX_VALUE ? null : values().get(first).value();
        }

        /**
         * Every value reached under what {@code by} chose in every container but
         * {@code container}, in the order the row wrote them.
         *
         * <p>The values at each depth are in that order already, so they are put together by
         * taking the first of them at whichever depth stands first, as many times as there are
         * values, each time over the depths.
         */
        List<BehaviorInputs.Occurrence> besideOf(TermPath container, WalkOfARow by) {
            List<List<Integer>> each = atEachDepth(choice(by, container));
            int[] next = new int[each.size()];
            List<BehaviorInputs.Occurrence> out = new ArrayList<>();
            while (true) {
                int depth = -1;
                for (int at = 0; at < each.size(); at++) {
                    if (next[at] < each.get(at).size() && (depth < 0
                            || each.get(at).get(next[at]) < each.get(depth).get(next[depth]))) {
                        depth = at;
                    }
                }
                if (depth < 0) {
                    return out;
                }
                walk.lookedAt++;
                out.add(values().get(each.get(depth).get(next[depth]++)));
            }
        }

        /** Where the values {@code choice} is under stand, at each depth some value is under it. */
        private List<List<Integer>> atEachDepth(Choice choice) {
            Map<ReachedAtDepth, List<Integer>> index = indexed(choice.named());
            List<List<Integer>> out = new ArrayList<>(depths.size());
            for (int depth : depths) {
                List<Integer> found = index.get(new ReachedAtDepth(depth, choice.within(depth)));
                if (found != null) {
                    out.add(found);
                }
            }
            return out;
        }

        /** The elements of {@code container} reached under what {@code by} chose in every other
         *  container, in order. */
        Set<Integer> elementsBeside(TermPath container, WalkOfARow by) {
            Set<Integer> elements = new TreeSet<>();
            for (BehaviorInputs.Occurrence each : besideOf(container, by)) {
                Integer taken = each.at().elementAt(container);
                if (taken != null) {
                    elements.add(taken);
                }
            }
            return elements;
        }

        /** Where every value stands, by how deep it was reached and the elements it was taken
         *  from in the containers {@code named} marks; made the first time a walk names those. */
        private Map<ReachedAtDepth, List<Integer>> indexed(List<Boolean> named) {
            Map<ReachedAtDepth, List<Integer>> known = byElements.get(named);
            if (known == null) {
                known = new HashMap<>();
                List<BehaviorInputs.Occurrence> values = values();
                for (int at = 0; at < values.size(); at++) {
                    walk.lookedAt++;
                    List<ElementsTaken.Taken> taken = values.get(at).at().outermostFirst();
                    List<Integer> elements = new ArrayList<>();
                    for (int container = 0; container < taken.size(); container++) {
                        if (named.get(container)) {
                            elements.add(taken.get(container).element());
                        }
                    }
                    known.computeIfAbsent(new ReachedAtDepth(taken.size(), elements),
                            _ -> new ArrayList<>()).add(at);
                }
                byElements.put(named, known);
            }
            return known;
        }

        /**
         * Which of the containers the values here were reached through {@code by} chose an
         * element of, {@code apart} never, and the elements it chose — asked of it through the
         * row, whichever it chose in.
         */
        private Choice choice(WalkOfARow by, TermPath apart) {
            List<TermPath> through = containers();
            List<TermPath> asked = new ArrayList<>(through);
            asked.remove(apart);
            walk.consulted(by, asked);
            Map<TermPath, Integer> chosen = by.chosen();
            List<Boolean> named = new ArrayList<>(through.size());
            List<Integer> elements = new ArrayList<>(through.size());
            for (TermPath container : through) {
                Integer element = container.equals(apart) ? null : chosen.get(container);
                named.add(element != null);
                if (element != null) {
                    elements.add(element);
                }
            }
            return new Choice(named, elements);
        }

        /**
         * What a walk names of the containers a path is inside.
         *
         * @param named    whether it names an element of each, in the containers' order
         * @param elements the elements it names, in the same order
         */
        private record Choice(List<Boolean> named, List<Integer> elements) {

            /** The elements it names in the first {@code depth} of the containers. */
            List<Integer> within(int depth) {
                int named = 0;
                for (int container = 0; container < depth; container++) {
                    if (named().get(container)) {
                        named++;
                    }
                }
                return elements.subList(0, named);
            }
        }

        /**
         * A value as the index has it: how many of the containers it was reached through, and
         * the elements it was taken from in those a walk named.
         */
        private record ReachedAtDepth(int depth, List<Integer> elements) {}

        /**
         * The containers the deepest value was reached through, each value's being the first so
         * many of them — which the walk to a path holds to, and which is refused here rather than
         * read as some other choice of elements.
         */
        private List<TermPath> containers() {
            if (containers == null) {
                List<TermPath> deepest = List.of();
                Set<Integer> reached = new TreeSet<>();
                List<List<TermPath>> each = new ArrayList<>();
                for (BehaviorInputs.Occurrence one : values()) {
                    walk.lookedAt++;
                    List<TermPath> these = new ArrayList<>();
                    for (ElementsTaken.Taken taken : one.at().outermostFirst()) {
                        these.add(taken.container());
                    }
                    each.add(these);
                    reached.add(these.size());
                    if (these.size() > deepest.size()) {
                        deepest = these;
                    }
                }
                for (List<TermPath> these : each) {
                    if (!these.equals(deepest.subList(0, these.size()))) {
                        throw new IllegalStateException("a value at one path was reached through "
                                + these + ", which is not where another was: " + deepest);
                    }
                }
                containers = List.copyOf(deepest);
                depths = List.copyOf(reached);
            }
            return containers;
        }
    }

    /**
     * The readings of one row a point is tried against.
     *
     * <p>The row is read before the readings of it are known: which containers the line's positions
     * are inside is the quantity's to say as it reads them, so it says so by reading the row once.
     * Every choice those containers allow follows, and the containers are spent here: what a caller
     * has after this is the readings and what the walk that built them says, neither of which is the
     * containers again.
     *
     * <p>Read and asked nothing, because reading the row is the whole of what that run is for. What
     * it read is kept and handed back with the readings: a reading of a row answers both what its
     * numbers are and whether they stand where a line is, so the walk made to find the containers is
     * a walk neither question has to make again.
     */
    static Readings readings(BehaviorInputs where, ObservedInputs observed,
                             BorderQuantity quantity) {
        return readings(where, observed, quantity, Optional.empty(), List.of(), List.of());
    }

    /**
     * The same, with the containers where the line decides is read at chosen in each reading too:
     * a reading is one choice of an element in every container either is read at, so what the line
     * reads and what is asked beside it are read of the same elements. {@code recordedAt} is where
     * a run through the comparison the line was drawn from is recorded, which a number only a run
     * works out is read at. {@code elsewhere} is where the other readings of the comparison
     * decide, which a reading is asked of the same way.
     */
    private static Readings readings(BehaviorInputs where, ObservedInputs observed,
                                     BorderQuantity quantity,
                                     Optional<WhereAPartDecides.AskedOfRows> decides,
                                     List<WhereAPartDecides.AskedOfRows> elsewhere,
                                     List<ConditionOutcomeSite> recordedAt) {
        RowWalk walk = new RowWalk(where, observed, Set.of(), recordedAt);
        DiscoveringRow discovering = new DiscoveringRow(walk);
        quantity.lookAt(discovering);
        decides.ifPresent(asked -> asked.lookAt(discovering));
        elsewhere.forEach(asked -> asked.lookAt(discovering));
        Map<TermPath, Integer> containers = discovering.containers();
        // The walk the containers were found by, where it is also a reading the point is tried
        // against. Where the row's positions are inside no container there is one choice and it is
        // the empty one, which is the choice this was read under — the same row, the same quantity,
        // the same elements chosen — so it is the reading of it, and what it found is not walked
        // again. Where they are inside one, every choice names an element and a reading that names
        // one is not the reading that names none.
        List<BorderQuantity.Observation> out = new ArrayList<>();
        if (containers.isEmpty()) {
            out.add(discovering);
        } else {
            for (Map<TermPath, Integer> choice : readingsOver(containers)) {
                out.add(new OneReadingOfARow(walk, choice));
            }
        }
        // Said by the walk that stopped, which is the only thing that knows it stopped. Worked out
        // afterwards from how many readings came back, a walk that was cut short and one the
        // containers never had more than are one answer, and whichever word is chosen for the pair
        // is wrong about the other.
        return new Readings(out, containersAllowMoreThan(containers, MOST_READINGS)
                ? new ReadingsTried.StoppedAtTheLimit(
                        WorkFigure.READINGS_OF_A_ROW_AT_A_POINT.at(MOST_READINGS))
                : ReadingsTried.EVERY_ONE);
    }

    /**
     * The readings of one row that were made, and whether they are all of them.
     *
     * @param tried   the readings, in the order the choices were taken
     * @param whether what the walk that built them says about itself
     */
    record Readings(List<BorderQuantity.Observation> tried, ReadingsTried whether) {}

    /**
     * Every reading of a row over the containers its positions were found to be inside.
     *
     * <p>One choice per container, in every combination — which is a product and not a zip, because
     * two containers a row's positions are not inside together are two independent choices.
     * Bounded, since a row holding several long lists has more readings than a measure is worth.
     */
    private static List<Map<TermPath, Integer>> readingsOver(Map<TermPath, Integer> containers) {
        List<Map<TermPath, Integer>> out = new ArrayList<>();
        out.add(Map.of());
        for (Map.Entry<TermPath, Integer> container : containers.entrySet()) {
            List<Map<TermPath, Integer>> wider = new ArrayList<>();
            for (Map<TermPath, Integer> each : out) {
                for (int i = 0; i < container.getValue() && wider.size() < MOST_READINGS; i++) {
                    Map<TermPath, Integer> deeper = new LinkedHashMap<>(each);
                    deeper.put(container.getKey(), i);
                    wider.add(deeper);
                }
            }
            out = wider;
        }
        return out;
    }

    /**
     * Whether the containers a row's positions are inside allow more readings of it than
     * {@code howMany}.
     *
     * <p>Asked with the figure one point is tried against, so that whether a walk over the
     * containers will be cut short is the walk's own answer and not something read off how many
     * readings came back. A product coming to exactly the number asked about is not more than it: a
     * walk that built as many readings as it is allowed to built either all of them or all it could,
     * and nothing it holds tells those apart; the containers are what know how many there are.
     */
    private static boolean containersAllowMoreThan(Map<TermPath, Integer> containers,
                                                   int howMany) {
        long there = 1;
        for (int cardinality : containers.values()) {
            // Asked before the multiplication rather than after it. A product that runs past what a
            // long holds answers this by wrapping round to a number that says the opposite.
            if (cardinality != 0 && there > howMany / cardinality) {
                return true;
            }
            there *= cardinality;
        }
        return there > howMany;
    }

    /** How many readings of one row a point is tried against. */
    private static final int MOST_READINGS = 256;

    private StandingAtAPoint() {}

    /**
     * Whether a run got an answer out of the rule, given every place the rule is watched at.
     *
     * <p><b>Any of them, because they are one rule.</b> A library operation may evaluate a closure
     * it was handed more than once — {@code List.distinctBy} asks its key twice — so a comparison
     * the author wrote once is written into the tree that runs more than once and each copy is
     * watched. Which of them ran is the operation's business; what the model states is the one rule,
     * and a run that got an answer out of any copy got one out of it.
     *
     * <p>Asked for all of them, a row would owe a run through every copy an operation happens to
     * make — a debt against how the library is written rather than against anything the model says.
     */
    static boolean gotAnAnswerOutOfTheRule(List<ConditionOutcomeSite> watched,
                                           AlignedObservation account) {
        return watched.stream().anyMatch(account::reached);
    }
}
