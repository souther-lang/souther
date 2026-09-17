package souther.compiler.partition;

import souther.compiler.coverage.AlignedObservation;
import souther.compiler.coverage.ComparisonEmissionSite;
import souther.compiler.inputs.TermPath;
import souther.compiler.observe.ObservedValue;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

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
         * @param tried whether every reading the row's steps allow was one this tried
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
                why = java.util.Collections.unmodifiableSet(new java.util.LinkedHashSet<>(why));
            }
        }

        Met REACHED = new Reached();

        Met NOT_WATCHED = new NotWatched();

        Met NOT_AT_POINT = new NotAtPoint();
    }

    /**
     * Whether every reading a row's steps allow was one a point was tried against.
     *
     * <p>What a bounded search may conclude turns on this. A reading standing at the point settles
     * the point however few were tried — one is what the question asks for — and a point no reading
     * stands at is a point nothing stands at only where there were no others to try. So a walk that
     * stopped may say it found something and may not say it found nothing, and this is the fact that
     * tells the two apart.
     *
     * <p><b>Said by the walk that stopped.</b> Which figure a walk stopped at is the walk's own
     * answer and nothing downstream can work it out: a reading count short of the steps is short
     * for whatever reason, and a reader deriving the reason from the shortfall names a figure
     * wherever a walk fell short of one it never reached. So this is built where the readings are
     * and travels from there, the way a decision reading says it stopped at a figure rather than
     * leaving its length to be read.
     */
    public sealed interface ReadingsTried {

        /** Every reading the steps allow was tried, so what none of them stands at, none stands
         *  at. */
        record EveryOne() implements ReadingsTried {}

        /**
         * The readings ran past what one point is tried against, and the rest were not tried.
         *
         * @param limit how many readings of one row a point is tried against, which is a figure of
         *              this compiler's and is what a run allowing more would raise
         */
        record StoppedAtTheLimit(int limit) implements ReadingsTried {}

        ReadingsTried EVERY_ONE = new EveryOne();
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
                          List<ComparisonEmissionSite> watched) {
        BorderQuantity quantity = line.quantity();
        BehaviorInputs where = line.subject().inputs();
        Set<ReadingGap> unreadable = new java.util.LinkedHashSet<>();
        boolean unwatched = false;
        boolean stoppedShort = false;
        for (ObservedInputs one : observed) {
            // A row has more than one value at a position inside a sequence, and standing at a point
            // is one element standing there. Asked for one value, such a row answered with none and
            // every point on such a line came back undecided — a measurement that could not look,
            // said of a row that wrote the values plainly.
            // The first run of the row says which steps the line's positions take, and the readings
            // are tried under each choice those steps allow.
            Map<TermPath, Integer> held = new LinkedHashMap<>();
            boolean stands = false;
            Set<ReadingGap> stopped = new java.util.LinkedHashSet<>();
            Readings readings = readings(where, one, quantity, held);
            List<OneReadingOfARow> tried = readings.tried();
            for (int which = 0; which < tried.size(); which++) {
                switch (quantity.standsAt(criterion, readings.readAt(which, quantity))) {
                    // A reading that could not look. What the row wrote nothing at is not among
                    // these: the quantity answers for the row there, since it is the quantity that
                    // knows whether a position it wrote nothing at leaves it a value.
                    case BorderQuantity.Stands.CouldNotTell it -> stopped.addAll(it.why());
                    case BorderQuantity.Stands.No _ -> { }
                    case BorderQuantity.Stands.Yes _ -> stands = true;
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
                        if (gotAnAnswerOutOfTheRule(watched, account)) {
                            return Met.REACHED;
                        }
                    }
                    // It stands where the line is and nothing watched it get there. Said rather
                    // than counted as a row that did not reach the comparison: a run that reached
                    // nothing is something this found out, and a run nobody watched is not.
                    case Generator.Watched.NoAccount _ -> unwatched = true;
                }
            }
            // And where none of them stood there, whether there were others to try. Asked of the
            // rows that came to nothing and of no others: a row that stood at the point was answered
            // by the reading that stood, and the readings after it are not ones this went without.
            if (!stands) {
                if (readings.whether() instanceof ReadingsTried.StoppedAtTheLimit) {
                    stoppedShort = true;
                } else if (stepsAllowMoreThan(held, tried.size())) {
                    // The steps the readings were built from are not the steps the readings found,
                    // which the quantity's contract does not allow: it reads every term before it
                    // concludes anything, and that is how many elements each position holds is
                    // known before there is anything to choose between. A walk short of the
                    // readings for any other reason than its own figure is this compiler's two
                    // answers about one row disagreeing, and neither of them is news about the
                    // model.
                    throw new IllegalStateException("the steps a row's positions take grew after"
                            + " the readings of it were built, and the readings that were tried"
                            + " are not all of them: " + held + " over " + tried.size());
                }
            }
            unreadable.addAll(stopped);
        }
        // Every reason any row met, the way one reading collects every reason its terms met. A
        // point tried against several rows is one this could not tell about for whatever stopped
        // any of them, and taking the strongest would say which row this walk began with.
        if (!unreadable.isEmpty() || stoppedShort) {
            return new Met.CouldNotTell(unreadable, stoppedShort
                    ? new ReadingsTried.StoppedAtTheLimit(MOST_READINGS)
                    : ReadingsTried.EVERY_ONE);
        }
        return unwatched ? Met.NOT_WATCHED : Met.NOT_AT_POINT;
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
                                    List<ComparisonEmissionSite> watched) {
        BorderQuantity quantity = line.quantity();
        BehaviorInputs where = line.subject().inputs();
        List<Map<souther.compiler.inputs.NumericTerm, souther.compiler.numeric.Place>> read =
                new ArrayList<>();
        Set<ReadingGap> unreadable = new java.util.LinkedHashSet<>();
        boolean stoppedShort = false;
        boolean unwatched = false;
        for (ObservedInputs one : observed) {
            if (!watched.isEmpty()) {
                switch (one.watched()) {
                    case Generator.Watched.Ran(var account) -> {
                        if (!gotAnAnswerOutOfTheRule(watched, account)) {
                            continue;   // it ran and never met this rule, so it says nothing here
                        }
                    }
                    case Generator.Watched.NoAccount _ -> {
                        unwatched = true;
                        continue;
                    }
                }
            }
            Map<TermPath, Integer> held = new LinkedHashMap<>();
            Readings readings = readings(where, one, quantity, held);
            for (int which = 0; which < readings.tried().size(); which++) {
                switch (quantity.valuesOf(readings.readAt(which, quantity))) {
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
            if (readings.whether() instanceof ReadingsTried.StoppedAtTheLimit) {
                stoppedShort = true;
            }
        }
        return new RowsRead(read, unreadable, stoppedShort
                ? new ReadingsTried.StoppedAtTheLimit(MOST_READINGS) : ReadingsTried.EVERY_ONE,
                unwatched);
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
            why = java.util.Collections.unmodifiableSet(new java.util.LinkedHashSet<>(why));
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
    }

    /**
     * One row's values under one reading of it: an element chosen at each step inside a sequence
     * the line's positions take.
     *
     * <p>A row standing at a point is one of its readings standing there, and a reading has to be
     * one: two positions under one person are that person's two values, and offering the first
     * person's age beside the second person's status would have a row stand at a point neither
     * element is at. So an element is chosen per step and every position takes the one chosen for
     * the steps it shares — the same rule a pair of classes is read by, since it is the same
     * question.
     *
     * <p>Which readings there are is not known before the quantity has asked, since which positions
     * a line is over is its to say. So the choices are collected as it asks and the reading is run
     * again under each, until one stands or they are used up.
     */
    private static final class OneReadingOfARow implements BorderQuantity.Observation {

        private final BehaviorInputs where;
        private final ObservedInputs observedInputs;
        /** The element chosen at each step, for this reading. */
        private final Map<TermPath, Integer> chosen;
        /** How many elements each step was found to have, over every reading so far. */
        private final Map<TermPath, Integer> held;

        OneReadingOfARow(BehaviorInputs where, ObservedInputs observedInputs,
                         Map<TermPath, Integer> chosen,
                         Map<TermPath, Integer> held) {
            this.where = where;
            this.observedInputs = observedInputs;
            this.chosen = chosen;
            this.held = held;
        }

        @Override
        public WalkResult<ObservationAtPoint> at(TermPath path) {
            // Over the arms, so that a walk coming to answer a third way is one this has to be
            // taught about rather than one quietly read as a walk that could not be made.
            return switch (where.occurrencesAt(observedInputs.inputs(), path)) {
                // The walk and the type disagree, which is the quantity's to report.
                case WalkResult.CouldNotWalk<List<BehaviorInputs.Occurrence>> _ ->
                        WalkResult.couldNotWalk();
                case WalkResult.Reached(List<BehaviorInputs.Occurrence> values) ->
                        WalkResult.reached(standingAmong(values));
            };
        }

        /** Which of the row's answers this reading gets at a position the walk arrived at. */
        private ObservationAtPoint standingAmong(List<BehaviorInputs.Occurrence> values) {
            if (values.isEmpty()) {
                // The row wrote no element here, which is a row that was read. What that leaves a
                // quantity is the quantity's to say, and it says it where it knows what the
                // position is worth to the number it is reading.
                return ObservationAtPoint.WROTE_NOTHING;
            }
            for (BehaviorInputs.Occurrence each : values) {
                each.at().forEach((step, ordinal) -> held.merge(step, ordinal + 1, Math::max));
            }
            for (BehaviorInputs.Occurrence each : values) {
                if (agrees(each)) {
                    return new ObservationAtPoint.Value(each.value());
                }
            }
            // No value here under this reading. Not a stop: the reading names an element this
            // position does not have, and another reading is where its values are.
            return ObservationAtPoint.ANOTHER_READING;
        }

        /**
         * Every value the row wrote at {@code path}, whichever elements this reading chose.
         *
         * <p>No choosing and nothing recorded to choose between. A number taken over a run is over
         * all of them, so there is no element for a reading to have picked and no second reading to
         * try — which is why this neither reads {@code chosen} nor adds to {@code held}.
         *
         * <p>An empty run is a row that wrote no element, and a total over nothing is what the walk
         * starts from rather than a value nobody could read. So the row is not marked as having
         * written nothing here: it wrote a container, and what it holds is none.
         */
        @Override
        public WalkResult<List<ObservedValue>> everyValueAt(TermPath path) {
            // The walk's own answer handed on, which is the quantity's to report where it could not
            // be taken, as it is for the one value a place holds.
            return where.valuesAt(observedInputs.inputs(), path);
        }

        /** Whether {@code each} was reached through the elements this reading chose. */
        private boolean agrees(BehaviorInputs.Occurrence each) {
            for (Map.Entry<TermPath, Integer> step : each.at().entrySet()) {
                Integer picked = chosen.get(step.getKey());
                if (picked != null && !picked.equals(step.getValue())) {
                    return false;
                }
            }
            return true;
        }
    }

    /**
     * The readings of one row a point is tried against.
     *
     * <p>The first is run before the rest are known: which steps the line's positions take is the
     * quantity's to say as it reads them, so it says so by being asked once. Every choice those
     * steps allow follows it.
     *
     * <p>Read and not asked anything, because reading the row is the whole of what the first run is
     * for. What is read is kept and handed back with the readings: a reading of a row answers both
     * what its numbers are and whether they stand where a line is, so the walk made to find the
     * steps is a walk neither question has to make again.
     */
    static Readings readings(BehaviorInputs where, ObservedInputs observed,
                             BorderQuantity quantity, Map<TermPath, Integer> held) {
        QuantityReading discovery =
                quantity.read(new OneReadingOfARow(where, observed, Map.of(), held));
        List<OneReadingOfARow> out = new ArrayList<>();
        for (Map<TermPath, Integer> choice : readingsOver(held)) {
            out.add(new OneReadingOfARow(where, observed, choice, held));
        }
        // The reading the steps were found by, where it is also a reading the point is tried
        // against. Where the row's positions take no steps there is one choice and it is the empty
        // one, which is the choice this was read under — the same row, the same quantity, the same
        // elements chosen — so it is the reading of it. Where they take steps, every choice names an
        // element and a reading that names one is not the reading that names none.
        List<QuantityReading> made = held.isEmpty() ? List.of(discovery) : List.of();
        // Said by the walk that stopped, which is the only thing that knows it stopped. Worked out
        // afterwards from how many readings came back, a walk that was cut short and one the steps
        // never had more than are one answer, and whichever word is chosen for the pair is wrong
        // about the other.
        return new Readings(out, made, stepsAllowMoreThan(held, MOST_READINGS)
                ? new ReadingsTried.StoppedAtTheLimit(MOST_READINGS)
                : ReadingsTried.EVERY_ONE);
    }

    /**
     * The readings of one row that were made, and whether they are all of them.
     *
     * @param tried   the readings, in the order the choices were taken
     * @param made    what has already been read, for the first of {@code tried} and in its order,
     *                and empty where the reading the steps were found by is not one of them
     * @param whether what the walk that built them says about itself
     */
    record Readings(List<OneReadingOfARow> tried, List<QuantityReading> made,
                    ReadingsTried whether) {

        /** What the quantity reads at the reading {@code which}, read here where it has not been
         *  read already. */
        QuantityReading readAt(int which, BorderQuantity quantity) {
            return which < made.size() ? made.get(which) : quantity.read(tried.get(which));
        }
    }

    /**
     * Every reading of a row over the steps {@code held} says its positions take.
     *
     * <p>One choice per step, in every combination — which is a product and not a zip, because two
     * steps a row's positions do not take together are two independent choices. Bounded, since a
     * row holding several long lists has more readings than a measure is worth.
     */
    private static List<Map<TermPath, Integer>> readingsOver(Map<TermPath, Integer> held) {
        List<Map<TermPath, Integer>> out = new ArrayList<>();
        out.add(Map.of());
        for (Map.Entry<TermPath, Integer> step : held.entrySet()) {
            List<Map<TermPath, Integer>> wider = new ArrayList<>();
            for (Map<TermPath, Integer> each : out) {
                for (int i = 0; i < step.getValue() && wider.size() < MOST_READINGS; i++) {
                    Map<TermPath, Integer> deeper = new LinkedHashMap<>(each);
                    deeper.put(step.getKey(), i);
                    wider.add(deeper);
                }
            }
            out = wider;
        }
        return out;
    }

    /**
     * Whether the steps a row's positions take allow more readings of it than {@code howMany}.
     *
     * <p>One question, and what it is about is the number it is asked with. Against the figure one
     * point is tried against, it is whether a walk over the steps will be cut short — which is what
     * the walk that does the cutting asks. Against the readings that came back, it is whether the
     * steps the walk found are the steps it was built from, which is a fact about this compiler and
     * not about the row.
     *
     * <p>A product coming to exactly the number asked about is not more than it. A walk that built
     * as many readings as it is allowed to built either all of them or all it could, and nothing it
     * holds tells those apart; the steps are what know how many there are.
     */
    private static boolean stepsAllowMoreThan(Map<TermPath, Integer> held, int howMany) {
        long there = 1;
        for (int cardinality : held.values()) {
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
    static boolean gotAnAnswerOutOfTheRule(List<ComparisonEmissionSite> watched,
                                           AlignedObservation account) {
        return watched.stream().anyMatch(account::reached);
    }
}
