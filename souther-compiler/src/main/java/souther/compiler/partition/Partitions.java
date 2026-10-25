package souther.compiler.partition;

import souther.compiler.check.DeclarationReadings;
import souther.compiler.check.ClassMembers;
import souther.compiler.check.HeldClass;
import souther.compiler.check.DefaultBoundOperationFacts;
import souther.compiler.check.ReadingPolicy;
import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.Carrier;
import souther.compiler.check.RuleKey;
import souther.compiler.check.DeclaredBounds;
import souther.compiler.check.EntryHeld;
import souther.compiler.check.PartId;
import souther.compiler.check.SidesBalanced;
import souther.compiler.check.RuleRef;
import souther.compiler.check.StringPredicates;
import souther.compiler.check.DeclaredClauses;
import souther.compiler.inputs.Distinctions;
import souther.compiler.check.PlacesTheRulesRead;
import souther.compiler.check.Shape;
import souther.compiler.check.TypeOps;
import souther.compiler.check.TypeView;
import souther.compiler.check.FieldDomains;
import souther.compiler.check.NarrowedBounds;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.NameReach;
import souther.compiler.inputs.Quantities;
import souther.compiler.inputs.Position;
import souther.compiler.inputs.StructuralInspection;
import souther.compiler.inputs.TypeBounds;
import souther.compiler.inputs.BlockReason;
import souther.compiler.values.AdmissibleSet;
import souther.compiler.values.Allowance;
import souther.compiler.values.Value;
import souther.compiler.values.ValueSet;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.FilingCoordinate;
import souther.compiler.inputs.RuleWithoutALine;
import souther.compiler.inputs.RulesWithNoLine;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.inputs.StandingQuestion;
import souther.compiler.inputs.TermOrders;
import souther.compiler.inputs.RuleAddress;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.Granularity;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Place;
import souther.compiler.numeric.Today;
import souther.compiler.numeric.Towards;
import souther.compiler.numeric.UnheldNumber;
import souther.compiler.numeric.UsualPlace;
import souther.compiler.regex.Language;
import net.unit8.notation199x.pattern.CodePoints;
import souther.compiler.observe.Figure;
import souther.compiler.observe.WorkFigure;
import souther.compiler.semantics.CaseMapping;
import net.unit8.notation199x.pattern.Meter;
import souther.compiler.regex.PatternPlan;
import souther.compiler.revision.RevisionKnowledge;
import souther.compiler.revision.RevisionWork;
import net.unit8.notation199x.pattern.PatternMeaning;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeReachName;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Comparator;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Arrays;
import java.util.List;
import java.util.function.BiPredicate;
import java.util.function.Consumer;
import java.util.function.Function;
import java.util.function.IntFunction;
import java.util.function.IntPredicate;
import java.util.function.IntUnaryOperator;
import java.util.function.Supplier;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.SequencedMap;
import java.util.Set;

/**
 * The equivalence classes a model already states, read off the types a behavior takes.
 *
 * <p>A type's cases are the classes; a threshold in an invariant is where one class ends and the next
 * begins. Nothing is invented: a position the model draws no line through has no classes, and is
 * reported as not derivable. An {@code Int} with no invariant is not silently split at zero, because
 * that would measure coverage of a rule the model never stated and report a gap for failing to test it.
 */
public final class Partitions {

    /**
     * What the model divides one behavior into: every position, every line, and what the reading
     * that produced them could not settle.
     *
     * <p><b>What it is, and nothing about who read it.</b> The reading of the declarations is what
     * this is worked out from, and it used to be carried here as well — so the geometry compared by
     * which reading had built it, and could not be an answer this compiler keeps. It is one now, and
     * the reading is handed to the few places that go on asking it further questions.
     *
     * <p><b>Every line, and not the makings of some of them.</b> A line between two positions was
     * held here as a {@link Border} while a line on one position was held as the cuts it would be
     * assembled from — so what borders a behavior has was settled by whoever assembled them, from a
     * reading of the declarations made where the assembling happened. Two readers therefore had two
     * chances to disagree about which lines exist, which is the thing this being one answer is for.
     *
     * @param unanswered the questions the rules of this behavior's inputs raise that nothing
     *                answered. Beside the axes and not inside one: the model raises them and an
     *                axis is one reader of them, so a position no axis came back for still has
     *                whatever was written about it — and an axis is re-pointed at another number as
     *                a body's rules are read, which would carry a question about one number onto
     *                another
     * @param measurements the locations of this behavior's input this phase answers for, in the
     *                order the reading found them, each holding the numbers it is measured at. A
     *                location is measured at as many numbers as the rules name of it — {@code
     *                Time.hour(slot.at)} and {@code Time.minute(slot.at)} are two measures at one
     *                location — and none is as much an answer as one. What a behavior is measured
     *                at is settled by what its types say and by what its body compares, and a count
     *                of either is not a measure of what any of that costs (see this package's
     *                documentation). Both {@link #positions()} and {@link #axes()} are read off
     *                this, so which measure answers for which location is what the model said and
     *                not a rule a reader invented
     * @param between the lines drawn between two positions, which divide neither of them
     * @param along   the lines drawn on one position, by the measure they are on. Every measure a
     *                row can be written against has an entry, and one that parts a number where
     *                the position holds no value has no line to have one for
     * @param inputIsEmpty the proof that the rules reaching this input leave no value at all, or
     *                null where no such proof was found. One fact about the behavior and not one per
     *                rule or per position: two clauses each admitting values are empty together, so
     *                neither of them is the one at fault and there is no position for it to be
     *                about. Null is "not proved empty" and never "there is a value" — what a proof
     *                of emptiness has no proof of is not the opposite claim
     * @param operationsStanding what the tree the language's operations stand in says of the forks
     *                of the body ({@link WhereTheOperationsStand}). Beside the lines and not a line:
     *                an arm is a case, which the type divides already, and what this adds is which
     *                position an arm the reading of the runs could not name is about, what a fork
     *                it could name no subject for may tell apart, and which ways it read inside a
     *                closure say all a run decided within one application of it
     */
    public record Partitioning(List<PositionMeasurements> measurements,
                               List<StandingQuestion> unanswered,
                               java.util.Set<NumericTerm> uncertain,
                               List<RuleWithoutALine> rulesWithoutALine,
                               List<souther.compiler.inputs.RuleWhereARunMayStop> rulesWhereARunMayStop,
                               List<souther.compiler.inputs.PositionValuesNotSeparated> notSeparated,
                               List<Border> between,
                               java.util.Map<AxisId, List<Border>> along,
                               ReachingCuts reaching,
                               MeasureClosure.OfThePartition partitionClosure,
                               MeasureClosure.OfTheBorder borderClosure,
                               souther.compiler.inputs.EmptyInput inputIsEmpty,
                               WhereTheOperationsStand operationsStanding) {
        public Partitioning {
            measurements = List.copyOf(measurements);
            unanswered = List.copyOf(unanswered);
            uncertain = java.util.Set.copyOf(uncertain);
            rulesWithoutALine = List.copyOf(rulesWithoutALine);
            rulesWhereARunMayStop = List.copyOf(rulesWhereARunMayStop);
            notSeparated = List.copyOf(notSeparated);
            between = List.copyOf(between);
            java.util.Map<AxisId, List<Border>> lines = new LinkedHashMap<>();
            along.forEach((at, drawn) -> lines.put(at, List.copyOf(drawn)));
            along = java.util.Collections.unmodifiableMap(lines);
            // Made where the reading is, never here. A closure this constructor could compute would
            // be one a caller assembling a `Partitioning` by hand could also have written, and
            // `Closed` is a conclusion about a reading rather than a shape of the lists beside it.
            if (partitionClosure == null || borderClosure == null) {
                throw new IllegalArgumentException(
                        "a partitioning with no account of what each measure's reading came to");
            }
        }

        /**
         * The locations this phase answers for, in the order the reading found them.
         *
         * <p>Read off the measurements rather than kept beside them. What a reading of a location
         * came to, where the walk stopped and what the location is left with are true of it once
         * however many numbers measure it, and a second list of them would be the same locations
         * answering to two lists that nothing holds in step.
         */
        public List<PositionAccount> positions() {
            return measurements.stream().map(PositionMeasurements::position).toList();
        }

        /**
         * The measures made of those locations, location by location and in the order each of them
         * settled.
         *
         * <p>For a reader whose question is about a number. Which location a measure is of is
         * where the measure sits, so a reader that needs the location asks {@link #measurements()}
         * and does not put the two back together from how a path is spelled.
         */
        public List<Axis> axes() {
            return measurements.stream().flatMap(each -> each.axes().stream()).toList();
        }

        /**
         * The positions no measure of them came back with anything to divide them by, each saying
         * which kind of nothing that is.
         *
         * <p>Read off the measurements, where both halves of the answer already are: whether
         * anything measures the location is what it holds, and what the rules written about it came
         * to is folded there over every number it is measured at. Kept beside them, the two would
         * be one reading of the positions and one list built from it, in step for as long as
         * whoever wrote the second remembered the first.
         *
         * <p>The structural reason outranks the rules': where the walk could not reach into what
         * the position holds, a rule naming something inside it is a second description of that
         * same stop and the first is the cause.
         */
        public List<UndividedPosition> undivided() {
            List<UndividedPosition> out = new ArrayList<>();
            for (PositionMeasurements at : measurements) {
                PendingPosition pending = PendingPosition.of(at.position(), at.hasMeasures());
                if (pending != null) {
                    out.add(withheldWhereNothingRead(pending.complete(at.inspection())));
                }
            }
            return List.copyOf(out);
        }

        /**
         * The same answer, less the one conclusion a reading nobody made cannot support.
         *
         * <p>{@link UndividedPosition.Why.Absent} says the model divides the position no way at
         * all, and what proves it is every rule about the position having been read and none of
         * them dividing it. Where nothing read the body, the rules it writes were not among them —
         * so the phases that did run answered for what they saw and the conclusion is one nobody
         * is entitled to draw.
         *
         * <p>Only that one. A position the walk could not enter and one a rule was filed at say
         * what they say whether or not a body was read, and taking them out here would lose a
         * finding an author can act on to a fact about a different part of the reading.
         *
         * <p>And it becomes the answer for that, rather than the one for a reading that did not
         * get far enough. That one promises a reader something standing at the position and a
         * finding published at it, and a body this image has none of is true of every position of
         * the behavior at once and stands at none of them.
         *
         * <p>Withheld here rather than concluded elsewhere: {@code Absent} has one producer, and
         * this is the reader that holds both the position's answer and what the measure's reading
         * came to.
         */
        private UndividedPosition withheldWhereNothingRead(UndividedPosition said) {
            return partitionClosure instanceof MeasureClosure.OfThePartition.BodyNotRead
                    && said.why() instanceof UndividedPosition.Why.Absent
                    ? UndividedPosition.bodyNotInEvaluation(said.at())
                    : said;
        }

        /**
         * The positions this reading did not get to the rules of.
         *
         * <p>Off the same two answers the verdict above is, and neither is read from the other.
         * Both phases have spoken by the time a measurement exists — what the position's own
         * declarations answered and what a body's rules drew — and a candidate that neither of them
         * answered is what an author is waiting on.
         */
        public List<souther.compiler.inputs.PositionReadingBlocked> blocked() {
            List<souther.compiler.inputs.PositionReadingBlocked> out = new ArrayList<>();
            for (PositionMeasurements at : measurements) {
                PendingPosition pending = PendingPosition.of(at.position(), at.hasMeasures());
                souther.compiler.inputs.PositionReadingBlocked stopped =
                        pending == null ? null : pending.reportable();
                if (stopped != null && !out.contains(stopped)) {
                    out.add(stopped);
                }
            }
            return List.copyOf(out);
        }

        /**
         * The lines drawn on one position, which is what a measure of them is over.
         *
         * <p>Empty where the position has none, which is an answer: a position the rules part
         * nowhere is measured at no line. Read here rather than assembled by the reader, so that
         * what lines a behavior has is settled once by what the model says.
         */
        public List<Border> along(Axis axis) {
            return along.getOrDefault(axis.id(), List.of());
        }

        /** Whether an edge of this term is a value some row could carry.
         *
         * <p>False where a rule reaching the value the term is taken of was not read in full. Every
         * edge here is then where the rules this could read stop, and a rule it could not read can
         * refuse that value as easily as the one beyond it — so the edge is not known to be writable
         * and asking for a row at it is asking for work nobody may be able to do.
         *
         * <p>And false at a count, unless every count that measure could give is one some value has
         * (the operation's own {@code EveryAnswerItCanGiveHasASourceValue}). What the projection
         * settles is which numbers
         * the rules leave, and three is a number they leave whether or not three of the thing exist:
         * a `Set<Bool>` is capped at two, and a `List<T>` of one needs a `T` that something inhabits.
         * The domain has no term for either, so such an edge is settled by a value rather than by an
         * argument — a row at it, or one this built — which is the account an edge nothing has
         * settled already gets. Read as a proof, a floor no value reaches became a row an author was
         * told to write.
         *
         * <p>A string's length is the one that stays proven, because a string of any length is
         * written by repeating a character. Declining the proof there too would take away every
         * `String.length` edge in the corpus over collections that have no values. */
        public boolean edgeIsKnownWritable(NumericTerm term) {
            return !uncertain.contains(term) && switch (term) {
                // What a location holds is what its type holds, so an edge on it is an edge some
                // value stands at by the type having been declared.
                case NumericTerm.ValueOf _ -> true;
                // And what an operation answered is the operation's to say. Asked of the arm it is
                // taken as instead, every operation sharing an arm would carry one answer: a string
                // of any length exists and a `Set<Bool>` of three does not, and both are counts.
                // The same for a number taken of a moved value: what it can answer is the run of
                // numbers the moved values come to ({@link NumericTerm#intrinsicBounds}), and
                // every one of them has a date, so the operation's answer holds of them.
                case NumericTerm.TakenOf taken -> DefaultBoundOperationFacts.get()
                        .everyAnswerItCanGiveHasASourceValue(taken.operation());
                // A string holding any number of the code points of a class is written by
                // repeating one of them, as a string of any length is — and, counted in what a
                // conversion makes of it, by repeating one the conversion leaves as it is.
                case NumericTerm.CodePointClassCount count ->
                        TermRealizations.writesEveryCountOf(count.counted(), count.through());
                // Every whole number from nought up is what the code points of some string come
                // to: none for nought, and for any larger number code points that are no
                // surrogates, chosen to add up to it.
                case NumericTerm.CodePointValueSum _ -> true;
                // Not every number up to the last code point is one: a surrogate is half of a pair
                // and no code point a string holds, so an edge at one is no edge any value stands
                // at, and nothing here tells the two apart before a row is written.
                case NumericTerm.CodePointAt _ -> false;
                // A number of an element read off the elements beside it is written by a container
                // holding elements beside it, and which containers there are is the type's and its
                // rules': a set never holds one value twice, and rules may keep elements apart or
                // bound how many there are. What the number's values can be (the place's, for the
                // end of a key's values) says nothing of whether such a container exists, and
                // nothing here shows one does, so no edge is known writable until a row stands at
                // it — which is not the edge being unwritable.
                case NumericTerm.OfAnElementsNeighbours _ -> false;
                // How often a value occurs among every occurrence is written by containers inside
                // the elements of another, which is no more shown to exist than the above.
                case NumericTerm.OccurrencesOfItsValue _, NumericTerm.OccurrencesOfAKey _ -> false;
                // Nor is what the elements of a key come to: elements holding it are written by a
                // container that holds them.
                case NumericTerm.GatheredUnderItsKey _, NumericTerm.GatheredUnderAKey _ -> false;
                // A run has as many values as a row wrote and each of them is chosen, so whether
                // some run adds up to a given total is a question about what the elements may hold
                // and how many there may be — not one the operation answers about itself. Nothing
                // here has walked that, so no edge on such a number is known writable, and the
                // point says as much rather than promising a row.
                case NumericTerm.TakenOver _ -> false;
            };
        }

        /**
         * The measures that divide their number into classes, which is what a partition is over.
         *
         * <p>Named here so that a reader wanting them asks for them. A measure may be a boundary
         * and no partition — a bound refuses everything outside it, so there is no class on the far
         * side and what such a number gets is an edge worth a row — and every reader that answered
         * this with a filter of its own was one that could be written without it.
         */
        public List<Axis> partitionAxes() {
            return measurements.stream().flatMap(each -> each.partitionAxes().stream()).toList();
        }

        /**
         * This reading's own line where it read {@code asked}, or null where it read none.
         *
         * <p><b>The line back, and not whether there is one.</b> A caller holding a border holds
         * whatever was written beside it wherever it came from, and what the readers of a line go
         * on to ask — what it demands of a row, where a run below it stops — is answered off the
         * value they were handed. Given a yes, a caller would read its own copy; given this, it
         * reads the one this reading made.
         *
         * <p>Which is also what makes asking here worth anything. Whether a border is one of this
         * reading's is what its behavior, its numbers, the position it is on and the orders it is
         * measured on were each being compared for, one attribute at a time and one more of them
         * each time somebody found a way past. A line is a value with an identity, and the reading
         * that drew it is holding it.
         *
         * <p>Asked by {@link Border#sameReadingAs} and not by the record's own equality, which is
         * what that method exists for: the same border met in the same place owing the same things
         * is one line, whatever a level was spelled as or what order a run's ends were listed in.
         */
        public Border held(Border asked) {
            for (Border each : between) {
                if (each.sameReadingAs(asked)) {
                    return each;
                }
            }
            for (List<Border> lines : along.values()) {
                for (Border each : lines) {
                    if (each.sameReadingAs(asked)) {
                        return each;
                    }
                }
            }
            return null;
        }

        /**
         * This reading's lines filed for a caller that asks {@link #held} of many of them: asked one
         * at a time, every line drawn is met for each line asked.
         *
         * <p>Filed once, by where each line was drawn and what drew it ({@link Border#drawnAt}),
         * which two lines {@link Border#sameReadingAs} calls one share, and a line is looked for
         * among those filed with it, in the order they were drawn, so the line found is the one
         * {@link #held} finds. Made for the call and not kept here: this value is held in answers.
         */
        public HeldLines lines() {
            return new HeldLines(this);
        }
    }

    /** The lines of one reading, filed by where each was drawn and what drew it
     *  ({@link Partitioning#lines}). */
    public static final class HeldLines {

        private final Map<Border.DrawnAt, List<Border>> drawn = new HashMap<>();

        private HeldLines(Partitioning reading) {
            for (Border each : reading.between()) {
                drawn.computeIfAbsent(each.drawnAt(), _ -> new ArrayList<>()).add(each);
            }
            for (List<Border> lines : reading.along().values()) {
                for (Border each : lines) {
                    drawn.computeIfAbsent(each.drawnAt(), _ -> new ArrayList<>()).add(each);
                }
            }
        }

        /** The reading's own line where it read {@code asked}, or null where it read none. */
        public Border held(Border asked) {
            for (Border each : drawn.getOrDefault(asked.drawnAt(), List.of())) {
                if (each.sameReadingAs(asked)) {
                    return each;
                }
            }
            return null;
        }
    }

    /**
     * The axes of one behavior, derived from the one reading of its input.
     *
     * <p>Nothing is read here. Which positions the input has and what can stand at each of them is
     * {@link InputDomain}'s, asked once and read by every measure; what this adds is which of them
     * an axis is drawn at, what each class is called and how a row for it is written.
     *
     * @param behavior what the axes are named after, which is the behavior the reading was made for
     */
    public static Partitioning of(String behavior, InputReading input,
                                  ReadingPolicy policy) {
        InputDomain inputs = input.domain();
        Quantities quantities = input.quantities();
        RuleReadingSource ruleSource = input.rules();
        // The one world the walk below reads in: the input's rules, what this caller allows a
        // reading to spend, and the readings the input already made of the declarations it met.
        // A step of it left to read a declaration for itself reads the same declaration once per
        // position that arrives at it.
        RuleReadingContext ruleReading =
                RuleReadingContext.of(ruleSource, policy, inputs.machines(), inputs.today());
        java.util.Set<NumericTerm> uncertain = new java.util.LinkedHashSet<>();
        RulesWithNoLine.Gathered rulesWithoutALine = new RulesWithNoLine.Gathered();
        // What the reading could not hold together, asked of every position it read rather than of
        // the ones left pending. This qualifies the classes and does not stand in for them: a
        // position with classes read from a product wider than the rules admit is exactly where it
        // has something to say, and a position with none is no more affected than any other.
        List<souther.compiler.inputs.PositionValuesNotSeparated> notSeparated = new ArrayList<>();
        List<StandingQuestion> standing = new ArrayList<>();
        // The positions this phase answers for, each with what measures it, as they are made. A
        // position is what a reader of a stop or an absence is asking about, and a measure is what
        // a reader of a class or a line is; holding the second under the first is what keeps which
        // of them answers for the other from being worked out again by whoever asks.
        List<Drawn> drawn = new ArrayList<>();
        for (Position position : inputs.positions()) {
            // Not at a position made of positions. Such a one is given up in favour of what is
            // under it and carries no classes of its own, so what this qualifies is not there —
            // and the same reading is said at each of the positions that do carry them, which is
            // where an author can act on it.
            if (position.valuesNotSeparated()
                    && !(position.structure()
                            instanceof souther.compiler.inputs.StructuralInspection.Decomposed)) {
                notSeparated.add(
                        new souther.compiler.inputs.PositionValuesNotSeparated(position.path()));
            }
            axisOf(behavior, position, ruleReading, drawn, uncertain, rulesWithoutALine);
            // What the rules of this position raise that nothing answered, gathered from the
            // reading that found it. Once per position and not once per axis: a question is the
            // model's, and which axis is standing beside it is this compiler's business.
            //
            // At every position the reading found, including one this drew no axis at. A position
            // given up in favour of its fields has none, and read off the axes its questions would
            // be dropped for the position having been decomposed — which is a fact about this
            // compiler deciding what a document says the model left standing. Nothing writes one
            // there today; it is gathered here so that the day something does, the question is
            // reported rather than lost.
            standing.addAll(position.unansweredQuestions());
        }
        // Every position the reading found, including the ones nothing divides: a report names what
        // it could not measure at one of those, and a body's comparison can still draw the first
        // line there. Nothing is dropped for how many there are. What an axis is worth is not known
        // here — `withThresholds` has not run, so a position a `guard` divides has no cut yet — and
        // a selection made now would be made where the least is known about what it selects
        // (see this package's documentation).
        List<PositionAccount> positions = drawn.stream().map(Drawn::at).toList();
        List<Axis> kept = drawn.stream().flatMap(each -> each.axes().stream()).toList();
        // A position undivided because a rule about it drew no line says that here, without waiting
        // for a body: a type bounded by a rule this cannot read is one whether or not any behavior
        // compares it, and so is one bounded by a rule read to the end that divides nothing. What
        // the rules came to is whether either happened, and which of the two it was — settled
        // beside each axis, as it is once a body has spoken.
        List<PositionMeasurements> settled = new ArrayList<>();
        // What every position's rules came to, the findings and the questions together. A location
        // is asked what its rules came to, and a rule nothing could classify is one of them: read
        // off the findings alone, a position whose only rule was one nothing worked out came back
        // as one no rule was written about.
        unclassifiedIn(standing, rulesWithoutALine);
        RulesWithNoLine cameToHere = rulesWithoutALine.found();
        List<RuleWithoutALine> refused = cameToHere.reported();
        for (Drawn at : drawn) {
            BodyCutInspection came = null;
            for (Axis axis : at.axes()) {
                came = BodyCutInspection.combined(came,
                        cameTo(axis.term(), axis.path(), cameToHere));
            }
            if (came == null) {
                came = cameTo(null, at.at().path(), cameToHere);
            }
            settled.add(new PositionMeasurements(at.at(), at.axes(), came));
        }
        // The lines first, because the closure is a conclusion about them: whether the reading ran
        // out is asked of what it produced beside what it found, and not of the gaps alone. Both
        // producers write into the one account — here there is only the one. A rule of a declaration
        // that relates two positions draws a line on neither of them, and every line on no position
        // is arranged with the others where they are all in hand, which this phase is not.
        LinesRead read = new LinesRead();
        // No body was read here, so no line is on a way another one is not.
        Map<AxisId, List<Border>> lines = linesAlong(kept, quantities, read, (one, other) -> false);
        read.returning(lines.values().stream().flatMap(List::stream).toList());
        MeasureClosure.Both closed = MeasureClosure.of(positions, standing, read);
        return new Partitioning(List.copyOf(settled), standing, uncertain,
                refused, cameToHere.stopping(),
                List.copyOf(notSeparated),
                List.of(), lines, ReachingCuts.NONE,
                closed.partition(), closed.border(),
                // Asked once, of the one reading that holds every parameter's rules together. A
                // contradiction between two declarations is visible nowhere else, and a reader
                // asking per position or per rule would be asking what neither of them decides.
                quantities.emptiness().orElse(null),
                // No body is read here.
                WhereTheOperationsStand.NONE);
    }

    /**
     * One position and what the declarations measured it at, before what its rules came to is
     * folded over those measures.
     *
     * <p>Not a {@link PositionMeasurements}, which is what this phase answers with and which says
     * what the rules came to. The fold wants every rule of every position in hand, and that is one
     * walk later than the walk that reads the positions — so this is what the first walk leaves,
     * and the answer is made once, whole. Written as the answer with the fold left out, the type a
     * reader is handed would carry a state only this file ever passes through.
     */
    private record Drawn(PositionAccount at, List<Axis> axes) {}

    /**
     * What the rules this phase drew no line from leave at one number of a position, or at the
     * position itself where nothing measures it.
     *
     * <p>Whether this phase left anything with no line, and not which limit it was. A limit belongs
     * to the rule it stopped, and the findings carry it there; taken as the position's, the first
     * rule of however many were stopped alike was the one a report named.
     *
     * <p>The number where a measure was made of it. A {@code String} is measured more than one
     * way: a rule about a length that nothing could read leaves the length blocked and says
     * nothing about the string's own values, and matched by path alone either measure answered for
     * both.
     *
     * <p>Where nothing measures the location, every rule filed anywhere in it is one the location
     * is left with — filed by where its coordinate sits, and not by which number the reading
     * happened to name. How exactly a rule was filed is how far its reading got, which is what the
     * finding says and not a claim about what the rule divides; a location with no measure has no
     * number for such a rule to be left at instead.
     *
     * <p>A finding the reading did not name a number for is at the position, and answers for every
     * measure on it: what number it was about is what was not read, so a measure cannot be excused
     * by it naming another.
     */
    private static BodyCutInspection cameTo(NumericTerm.FromOnePosition term,
                                            TermPath path,
                                            RulesWithNoLine found) {
        // Each bit asked of what says it, and neither read off the other's list. Every rule that
        // came to no line is reported here, whichever of the two things happened to the reading, so
        // the list alone answers neither question — the reason a finding carries is what says which
        // of them it is.
        boolean stated = found.modelStatements().stream()
                .anyMatch(one -> filedHere(one.at(), term, path));
        // And a reading stopped wherever a finding says so, or wherever a rule nothing classified
        // stands. Both are the same sentence about this compiler reaching different surfaces: a
        // reader that files no finding for such a rule leaves the question as the only thing
        // saying it, and one whose questions are the accounting's leaves the finding.
        boolean stopped = found.readingsThatStopped().stream()
                        .anyMatch(one -> filedHere(one.at(), term, path)
                                && leavesTheDivisionUnknown(one.why()))
                || found.unclassified().stream()
                        .anyMatch(one -> filedHere(one.at(), term, path));
        if (!stated && !stopped) {
            return new BodyCutInspection.Exhausted();
        }
        // What the rules came to, asked of each of them and kept apart. A reading that stopped on
        // one rule is not answered for by another read from end to end, and a rule read from end to
        // end is the model stating something whatever became of the reading beside it.
        return new BodyCutInspection.NoLine(stopped, stated);
    }

    /**
     * Whether a rule this compiler did not get through leaves how the position divides unknown.
     *
     * <p>Asked of the reason and not read off the list it arrived in. Every rule here is one a
     * reading stopped on, and which reading stopped decides what is unknown: the reading that says
     * which values may stand at a position is what the classes are made of, and one that says
     * where they stop is not. A rule read to the end by the first and given up on by the second
     * leaves the classes exactly as the rules leave them — and answered off the list, the position
     * came back as one this compiler could not divide, which is a limit of the border said about
     * the partition ({@link BlockReason.RuleReadingStopped
     * #widensWhatThePositionAdmits}).
     *
     * <p><b>A reason that names no rule passes through, and is not asked.</b> The question is one a
     * rule's own reading answers; a position that could not hand its sets on has no rule to ask it
     * of, and what it does to a verdict here is what it did before this was asked. That those
     * reasons say one thing here and another where the same question is asked of a whole position
     * ({@link souther.compiler.inputs.RulesWithNoLine#aReadingThatStopped}) is older than this and
     * is not settled by it.
     */
    private static boolean leavesTheDivisionUnknown(
            BlockReason.RuleWithoutLineReason why) {
        return !(why instanceof BlockReason.RuleReadingStopped it)
                || it.widensWhatThePositionAdmits();
    }

    /**
     * The questions about rules nothing classified, put where a location's own account is read.
     *
     * <p>They are questions and they are also what one of this location's rules came to, and the
     * two readers of them want different things: one asks what holds a measure open and the other
     * asks what became of the rules written here. Neither is read off the other.
     */
    private static void unclassifiedIn(List<StandingQuestion> asked,
                                       RulesWithNoLine.Gathered into) {
        for (StandingQuestion each : asked) {
            if (each instanceof StandingQuestion.Unclassified it) {
                into.asked(it);
            }
        }
    }

    /** Whether a finding filed at {@code at} is one about this measure of this location. */
    private static boolean filedHere(FilingCoordinate at, NumericTerm.FromOnePosition term,
                                     TermPath path) {
        if (term == null) {
            return at.path().equals(path);
        }
        return switch (at) {
            case FilingCoordinate.OfTerm it -> it.term().equals(term);
            case FilingCoordinate.AtPosition it -> it.path().equals(path);
        };
    }

    /**
     * The numbers this position is measured at, which is not always the one the declarations named.
     *
     * <p>A position no rule of its own divides, whose body measures numbers of it: a bare
     * {@code List<String>} nothing bounds, under a {@code guard List.length(t.names) > 0}. The line
     * is on that number, so an axis about it is what there is to make — there is nothing else here
     * for one to be about, and dropping the evidence loses a line the body draws.
     *
     * <p><b>As many as the rules name.</b> {@code Time.hour(slot.at) >= 9 && Time.minute(slot.at)
     * >= 30} draws two lines on two numbers of one location, and both are measures. There is no
     * answering such a location with one of its numbers: picking one drops the other's lines and
     * picking neither drops both, and a location with two lines drawn on it then gets the sentence
     * a body with no comparison in it gets.
     *
     * <p>In the order the rules were read, so that what a report lists and what a search enumerates
     * are in the order an author wrote them.
     */
    private static List<NumericTerm.FromOnePosition> numbersMeasuring(
            PositionMeasurements at, List<RuleEvidence> evidence,
            List<ClassingBlocker> blocked) {
        TermPath path = at.position().path();
        List<RuleEvidence> here = evidence.stream()
                .filter(each -> each.at().position().equals(path)).toList();
        List<NumericTerm.FromOnePosition> numbers = new ArrayList<>();
        for (RuleEvidence each : here) {
            if (!numbers.contains(each.at())) {
                numbers.add(each.at());
            }
        }
        // And the numbers a rule was to divide and did not. A blocker is what keeps a position's
        // classes from being composed out of the rules that worked, so a number reached by one and
        // by no evidence is exactly the number it has to reach — measured off the evidence alone,
        // the one case a blocker exists for is the one it never arrives at.
        for (ClassingBlocker each : blocked) {
            if (each.at().position().equals(path) && !numbers.contains(each.at())) {
                numbers.add(each.at());
            }
        }
        // Every number a rule named, whether or not the declarations already measured some other
        // number of the same place. A measure is of a number and a location has as many as the
        // rules name of it, so which measures there are is a question about numbers and never
        // about how many the location already has — asked of the location, a body dividing the
        // value of a position whose length a declaration bounds says nothing anybody reads, and
        // the distinction the model does make is not published at all.
        //
        // Nothing is deduplicated here that the walk below does not already: one entry per number,
        // and the measure of each is looked up by that number, so a number both a declaration and
        // a body speak about is one measure with both read into it.
        return numbers;
    }

    /**
     * One axis, with what the rules about its number divide it into.
     *
     * <p>The same walk whichever number it is. What the declarations named and what a body measures
     * a position by are two ways to arrive at a number and one thing to do with it, and a second
     * route through this would be a second answer to what a rule about a number comes to.
     */
    private static BodyCutInspection measureAt(List<Axis> out, PositionMeasurements at, Axis axis,
                                  NumericTerm.FromOnePosition term, List<RuleEvidence> evidence,
                                  List<ClassingBlocker> blocked,
                                  Quantities reading, RuleReadingContext ruleReading,
                                  Allowance<NumericTerm.FromOnePosition> allowance,
                                  RulesWithNoLine rules, RulesWithNoLine.Gathered found,
                                  EvidenceAccount account) {
        RuleReadingSource ruleSource = ruleReading.source();
        String behavior = at.position().behavior();
        // What a report calls this measure, which is what its number is called under this
        // behavior. Read the same way the measure itself takes its name, so that a piece of
        // evidence said to be measured here and the measure it was measured at are one name.
        AxisId id = AxisId.of(behavior, term);
        Type type = at.position().type();
        List<RuleEvidence> mine = evidence.stream()
                .filter(each -> each.at().equals(term)).toList();
        List<GuardThresholds.Guards.Singled> points = RuleEvidence.pointsIn(mine);
        // What this term's values can be, which is the type's bound already narrowed by whatever
        // the record it sits in says about it. Reading the type again here would put a threshold
        // back inside a range the record has no values in.
        NumericDomain.Bounds domain = domainOf(reading, term);
        // Both orders as the reading has them. Worked out here from the type this reader happens
        // to hold, the answer would be about wherever that type came from rather than about where
        // the reading has this term standing.
        TermOrders orders = reading.ordersOf(term);
        Carrier carrier = orders.answered();
        // What the rules about this position tell apart as sets, which is a vocabulary of its own.
        // Where they are the whole of what divides the position, the classes are what they come to
        // between them and there is nothing to put them beside.
        // What the rules leave the position divided into, asked once. The vocabulary decides the
        // classes and nothing else: what the lines cut, where the rules part the position and what
        // the account is owed are observations of their own, so everything below runs whichever way
        // this came out. A second route past them would be a second answer about all of them.
        TypeView view = TypeView.of(type, ruleSource.inners(), ruleSource.symbols(),
                ruleSource.kinds(), ruleSource.sums());
        // What writing one value out is allowed to cost, one allowance to each value written. Named
        // here because this is where a witness for a row is paid for: a string offered for a row is
        // no answer about the position, and paying for it out of what the position may build would
        // let a representative decide how exactly the model was read.
        Classing.Result answered = Classing.of(term, mine, blocked, carrier,
                at.position().admits(), allowance, PatternPlan.Budget.OF_A_WITNESS::meter,
                place -> standing(view, carrier, place, ruleSource));
        Classing.Classed classed = answered.classed();
        // What became of each rule, applied and not decided again. The answer is total over what
        // was handed in, so a rule with nothing said about it is not something this loop can leave
        // behind — which is what the account below refuses, and what a stage deciding the three
        // cases for itself was one forgotten branch away from doing.
        for (Classing.Disposed each : answered.forEach()) {
            switch (each.outcome()) {
                // The classes are made out of it. A rule that states a set is measured here, at the
                // axis they are on; a line and a value singled out are measured by the walk below,
                // which is where what they leave is worked out.
                case DIVIDED -> {
                    if (each.what() instanceof RuleEvidence.BySet) {
                        account.measured(each.what(), id);
                    }
                }
                // Read, and tells none of the position's values from the others. Reported, and the
                // rules beside it divide the position exactly as they would have without it.
                case TOLD_NOTHING_APART -> {
                    found.add(RuleWithoutALine.of(each.what().by().cited(),
                            each.what().by().readAt(),
                            new FilingCoordinate.AtPosition(term.position()), each.why()));
                    account.disposedOf(each.what(),
                            new EvidenceAccount.Disposition.TheRuleDividedNothing(term));
                }
                // There are no classes, so this rule is among none. Whether this stage got as far
                // as qualifying it is its own business and not something a reader is told.
                case NOT_COMPOSED -> account.disposedOf(each.what(),
                        new EvidenceAccount.Disposition.TheClassesWereNotComposed(term));
                // A line, or a value singled out that no set class took up. It still cuts the
                // position, and the walk below is where that is said.
                case LEFT_TO_THE_WALK -> { }
            }
        }
        // The answer's own population, and not what is left after taking the rest away. Subtracted
        // here, the same question is answered twice — and the day the two subtract differently the
        // classes are composed out of one list and recorded as composed out of another.
        List<RuleEvidence> dividing = answered.dividing();
        // And what the walk below still reads, which is not the same list. Only the classes turn on
        // whether they composed: where they did not, the lines a rule drew are still lines and the
        // places it parts the position are still places, so the walk runs over everything that
        // reached here but the rules proved to tell nothing apart — those state nothing, and a line
        // read off one would be a line the model does not draw.
        List<RuleEvidence> taken = answered.forEach().stream()
                .filter(each -> each.outcome() == Classing.Outcome.LEFT_TO_THE_WALK
                        || each.outcome() == Classing.Outcome.DIVIDED)
                .map(Classing.Disposed::what).toList();
        // One switch and not three conditionals. What each answer means for the classes, for the
        // rules they were composed from and for whether the cuts stand is the answer's, said once;
        // read off it three times, each reading is a place to disagree about what the arm meant.
        Composition made = switch (classed) {
            // The classes are what the walk below works out of the lines and the values singled
            // out, and the cuts are as they have always been.
            case Classing.Classed.OnTheOrder _ -> Composition.ON_AN_ORDER;
            // A cut is a place on the order, and a class that is a set has no answer to where it
            // lies — so a position whose classes are sets has none, and a value singled out is in
            // them rather than beside them. Published as both, one distinction would be stated
            // twice in two algebras and every line would fall in no class ({@link Axis}).
            // Under the names the position wears, which is where they are put on: the rules divided
            // the values the position holds and knew nothing of what is written over them, and a
            // row writes one of those values under every name the type puts on it. Left off, a
            // class drawn over strings is asked about a construction and holds none of them —
            // which is the classes of a position holding nothing the position holds.
            case Classing.Classed.Composed(List<PartitionClass> it) ->
                    new Composition(it.stream().map(each -> each.under(view.wrappers())).toList(),
                            composedFrom(dividing), false, null);
            // No classes and nothing they were composed from, and the cuts stand: they are
            // observations of their own rather than a projection of the classes.
            case Classing.Classed.NotComposed(var why) ->
                    new Composition(List.of(), List.of(), true, why);
        };
        // What a reader is told about the rules the classes were not composed out of. The account
        // for them is above, with every other rule's — this is the sentence, and only where the
        // classes were the group's own to compose: a blocker says what became of its own rule and
        // has already been reported, so a reason copied from it onto the rules beside it would name
        // them for something that happened to another.
        //
        // Into the gathering the whole stage answers with, and not a list of this method's own:
        // what a reader is told is assembled once, after every position has been measured, so a
        // finding kept here would be one nobody reads.
        if (made.why() != null && blocked.isEmpty()) {
            RuleEvidence.statementsIn(answered.notComposed())
                    .forEach(each -> found.add(RuleWithoutALine.of(each.origin().cited(),
                            each.origin().readAt(),
                            new FilingCoordinate.AtPosition(term.position()), made.why())));
        }
        // Said here because this is where they were asked. A blocker carried in and never reached
        // is a denominator this stage closed over the rules that worked, which the account refuses.
        account.heldShut(blocked);
        RulesWithNoLine stated = rules;
        // Every line handed here is one the quantity reaches, and nothing here asks again. Whether
        // it does is {@link Cutting#reached}'s answer, given where the comparison is read and again
        // at each position its name is filed at; a line it refuses never becomes evidence. Asked
        // again here, the question would be read off where the rule wrote its number rather than
        // off where the values part — and `> 10` over values from eleven up, which parts them at
        // the end of what the position holds, would be dropped while `>= 11`, the same division,
        // was kept. The intervals and the cuts below both read this one list, so a line at the end
        // of the position is a cut and a border there, and an interval on its empty side is no
        // class.
        List<Threshold> reachable = new ArrayList<>();
        for (RuleEvidence each : taken) {
            if (each instanceof RuleEvidence.BySet) {
                continue;   // already answered for above, as a class the vocabularies will not hold
            }
            account.measured(each, id);
            // A value singled out is not a line among the ranges: it is a class of its own inside
            // the run it falls in, which the classes below take up beside the lines.
            if (each instanceof RuleEvidence.Divides(Threshold line)) {
                reachable.add(line);
            }
        }
        // Through `excluding`, so that a class list replaced by the intervals a threshold cuts
        // keeps only the exclusions it still has classes for.
        //
        // A line at the end of what the position holds leaves values on one side only, so it
        // divides the position into nothing, and it is not a rule that went unread either: what
        // it says was understood. So the answer there is that the rules were exhausted, which is
        // what keeps `NoLine` meaning that a rule was written about the position rather than
        // everything that came to nothing.
        NumericDomain.Bounds within = domain;
        // The lines and the values singled out divide the position together, into one list of
        // classes: the runs the lines leave, and each value out of the run it falls in.
        List<Parting> parted = new ArrayList<>(partedOf(axis));
        reachable.forEach(each -> parted.add(
                Parting.by(each.parts(), each.origin())));
        return made(out, at, behavior, term,
                made.classesFor(axis, () -> OrderedClasses.of(
                        Intervals.of(reachable, within == null ? null : within.min(),
                                within == null ? null : within.max(), carrier),
                        points, term, type, reading, ruleReading, within,
                        PatternPlan.Budget.OF_A_WITNESS::meter)),
                made.divides(),
                // A cut is a place on the order the values are counted on, and a class that is a
                // set has no answer to where it lies — so a position whose classes are sets
                // carries none, and the value singled out is in them rather than beside them.
                // Published as both, the position would state one distinction twice in two
                // algebras, and every line on it would fall in no class ({@link Axis}). A bounded
                // string with a rule about its prefixes is exactly that pair, and it is a model
                // somebody writes.
                made.keepsCuts()
                        ? mergedPoints(merged(cutsOf(axis), reachable, carrier), points, carrier)
                        : List.of(),
                parted, narrowedOf(axis),
                reachable.isEmpty() && points.isEmpty() ? null : new BodyCutInspection.Evidence(),
                stated);
    }

    /**
     * The measure the rules about one number came to, kept where it measures something.
     *
     * <p>A run of classes, the lines cut on the number, or where the rules part it: with none of
     * the three the rules measured the number at nothing, and what there is to say is about the
     * location rather than about a measure of it. Kept anyway, the location would be counted among
     * the measures — which is what a measure of nothing was.
     */
    private static BodyCutInspection made(List<Axis> out, PositionMeasurements at, String behavior,
                                          NumericTerm.FromOnePosition term,
                                          List<PartitionClass> classes,
                                          List<RuleEvidenceOrigin> divides, List<Cut> cuts,
                                          List<Parting> parted, NarrowedBounds narrowed,
                                          BodyCutInspection drew, RulesWithNoLine rules) {
        if (classes.isEmpty() && cuts.isEmpty() && parted.isEmpty()) {
            return cameTo(term, at.position().path(), rules);
        }
        out.add(Axis.of(behavior, term, classes, divides, cuts, parted, narrowed));
        return drew != null ? drew : cameTo(term, at.position().path(), rules);
    }

    /**
     * What a number is already divided into, or what the rules now read about it divide it into.
     *
     * <p>Refinement and not replacement. What a body draws is evidence arriving after the model's
     * own, and evidence only ever tells a position's values apart more finely — so where the model
     * already divides the number, the lines a body draws are lines among those classes and the
     * classes stay as they are. Rebuilt from the lines, a position the model divides three ways
     * would come back divided two ways, and the loss reads as the model never having stated the
     * third.
     *
     * <p>Which is a rule about the classes and not about the carrier. A position whose rules name
     * the values it holds is divided just as finely, so a {@code guard} over it replaced what the
     * model states. The two agree wherever this fires, and by construction rather than by luck: an
     * enumeration's cases are its classes, and a crossing never leaves a position whose type states
     * classes without any ({@code LocalInspection}'s {@code constructibleAt}).
     *
     * @param otherwise the classes to use where nothing divides the number yet, asked for only
     *                  there — a number that already has classes has no use for them, and working
     *                  them out would be a reading whose answer is thrown away
     */
    private static List<PartitionClass> classesOf(
            Axis axis, java.util.function.Supplier<List<PartitionClass>> otherwise) {
        return axis != null && axis.derivable() ? axis.classes() : otherwise.get();
    }

    /**
     * What one answer about a position's classes means for the measure built from it.
     *
     * <p>Three things follow from which answer it was, and they follow together: what the classes
     * are, which rules they were composed out of, and whether the cuts a line drew stand. Read off
     * the answer once each, the three are three places to decide what the arm meant — and a measure
     * that said its classes came out of rules it did not compose is one nothing can hold to it.
     *
     * @param keepsCuts whether the cuts stand. They do wherever the classes are not sets: a cut is
     *                  a place on the order and a set class has no answer to where it lies
     * @param why       what stopped the classes, or null where nothing did
     */
    private record Composition(List<PartitionClass> classes, List<RuleEvidenceOrigin> divides,
                               boolean keepsCuts, BlockReason.RuleWithoutLineReason why) {

        /** The order is the vocabulary, so the run of classes the caller works out is the answer. */
        private static final Composition ON_AN_ORDER =
                new Composition(List.of(), List.of(), true, null);

        boolean onAnOrder() {
            return this == ON_AN_ORDER;
        }

        /**
         * What the axis's classes are, which is this answer's to say and not a caller's.
         *
         * <p>Where the classes were not composed there are none, and what the declarations already
         * left is not them. A position the model divides is divided by everything said about it —
         * so a list kept because it happened to be there before is a denominator that says a
         * distinction was taken up when this stage has just said it was not, and the rows are owed
         * at classes nothing holds them to.
         *
         * <p>Everywhere else refinement is the rule ({@link #classesOf}): what a body draws is
         * evidence arriving after the model's own, and where the model already divides the number
         * the classes stay as they are.
         */
        List<PartitionClass> classesFor(Axis axis, Supplier<List<PartitionClass>> onTheOrder) {
            if (why != null) {
                return List.of();
            }
            return classesOf(axis, onAnOrder() ? onTheOrder : this::classes);
        }
    }

    /** Which rules the classes were composed out of, which is every distinction that went in. */
    private static List<RuleEvidenceOrigin> composedFrom(List<RuleEvidence> mine) {
        return mine.stream().map(RuleEvidence::by).toList();
    }

    /** The lines already cut on the number, of which there are none where nothing measured it. */
    private static List<Cut> cutsOf(Axis axis) {
        return axis == null ? List.of() : axis.cuts();
    }

    /** Likewise where the rules already part it. */
    private static List<Parting> partedOf(Axis axis) {
        return axis == null ? List.of() : axis.parted();
    }

    /** And where the rules leave its ends, which is an answer about this number and no other. */
    private static NarrowedBounds narrowedOf(Axis axis) {
        return axis == null ? NarrowedBounds.NOTHING : axis.narrowed();
    }

    /**
     * The same, given what the rules said as the reading of them met it.
     *
     * <p>One list and not one per kind of thing a rule can say. What this stage does with a piece of
     * evidence — divide a position by it, leave it outside what the position holds, or not take it
     * up at all — is the same question whichever kind it is, and the account of what became of each
     * is over all of them ({@link EvidenceAccount}). Handed one list per kind, both the numbers a
     * position is measured at and that account have to put them back together, and a position
     * measured at one kind alone is measured at neither.
     */
    public static Partitioning withEvidence(Partitioning base,
                                            Quantities reading,
                                            List<RuleEvidence> evidence,
                                            List<ClassingBlocker> blocked,
                                            Allowance<NumericTerm.FromOnePosition> allowance,
                                            RuleReadingContext ruleReading,
                                            RulesWithNoLine rulesWithoutALine,
                                            List<LineDrawn> between,
                                            ReachingCuts reaching,
                                            MeasureClosure.Drawing drawing,
                                            WhereTheOperationsStand operationsStanding) {
        // Both producers of one kind of evidence. What a body compared and what a type's own rules
        // bound are read by different readers and answer the same question, so a position either of
        // them wrote about and neither could turn into a line is named once, whichever wrote it.
        RulesWithNoLine.Gathered found = new RulesWithNoLine.Gathered();
        found.addAll(base.rulesWithoutALine());
        found.addAll(rulesWithoutALine);
        unclassifiedIn(base.unanswered(), found);
        RulesWithNoLine gathered = found.found();
        // And what these readers could not classify, beside the questions the base reading already
        // had. One list of what holds a measure open, for the one reader of it.
        //
        // Taken from the same fold as the findings, because a rule both readers met is one rule
        // however many of them say so. Concatenated instead, the reader of the report was told
        // twice about one rule nothing worked out.
        List<StandingQuestion> asked = new ArrayList<>(base.unanswered().stream()
                .filter(each -> !(each instanceof StandingQuestion.Unclassified)).toList());
        asked.addAll(gathered.unclassified());
        List<PositionMeasurements> measurements = new ArrayList<>();
        EvidenceAccount account = new EvidenceAccount(evidence, blocked);
        // A position at a time, so that what a body's rules add is added where the position already
        // is. Walked as one run of measures, which position each of them came back for is a
        // question this would have to answer again once the rules name a second number of one.
        for (PositionMeasurements at : base.measurements()) {
            List<Axis> here = new ArrayList<>();
            // What the rules came to about the location, folded as its numbers are measured. One
            // sentence for the location: a number the rules divide and a number they say nothing
            // about are both measures of it, and which of the two answers a report is owed is
            // taken together rather than chosen between by the order this happens to walk them in.
            BodyCutInspection came = null;
            List<NumericTerm.FromOnePosition> numbers =
                    numbersMeasuring(at, evidence, blocked);
            for (NumericTerm.FromOnePosition term : numbers) {
                // The measure of this number where the declarations made one, and nothing where a
                // body's rules are the first to name it. What such a measure starts from is what
                // the location is, which is where this reads it from.
                Axis measured = at.axes().stream()
                        .filter(each -> each.term().equals(term)).findFirst().orElse(null);
                came = BodyCutInspection.combined(came,
                        measureAt(here, at, measured, term, evidence,
                                blocked.stream()
                                        .filter(each -> each.at().equals(term)).toList(),
                                reading, ruleReading, allowance, gathered, found, account));
            }
            // The measures nothing new was said about, kept as they are, and what they were left
            // with folded in beside the rest.
            for (Axis axis : at.axes()) {
                if (numbers.contains(axis.term())) {
                    continue;
                }
                here.add(axis);
                came = BodyCutInspection.combined(came,
                        cameTo(axis.term(), axis.path(), gathered));
            }
            if (came == null) {
                came = cameTo(null, at.position().path(), gathered);
            }
            measurements.add(at.measuredAt(here, came));
        }
        List<Axis> out = measurements.stream().flatMap(each -> each.axes().stream()).toList();
        account.everyPieceWasDisposedOf(out);
        // Both producers into the one account. A line that divides a position leaves its border on
        // the position and a line between two leaves its border beside them; they are the same
        // reading, and an accounting over one of them says nothing about the other.
        LinesRead read = new LinesRead();
        BiPredicate<LineOrigin, LineOrigin> apart = reaching.apart();
        Map<AxisId, List<Border>> lines = linesAlong(out, reading, read, apart);
        // Once per quantity: several lines on one quantity are held to one answer, and working it
        // out reads every value of the position again.
        Map<BorderQuantity, HeldValues> heldTo = new LinkedHashMap<>();
        List<Border> across = Border.allOf(between, partedByQuantity(out), read, apart,
                quantity -> heldTo.computeIfAbsent(quantity,
                        each -> each.heldIn(reading.region())));
        read.returning(lines.values().stream().flatMap(List::stream).toList());
        read.returning(across);
        // Drawn from the reading that was made, or said to be the absence of one. A body this
        // elaboration has none of was not read: the classes above are what the declarations and
        // the clauses came to, and what the body's own rules add to them is unknown — so neither
        // measure may conclude over it, and neither may name a question either.
        MeasureClosure.Both closed = switch (drawing) {
            case MeasureClosure.Drawing.FromTheReading _ ->
                    MeasureClosure.of(base.positions(), asked, read);
            case MeasureClosure.Drawing.NoneWasMade it -> MeasureClosure.bodyNotRead(
                    it.behavior(), MeasureClosure.of(base.positions(), asked, read));
        };
        return new Partitioning(measurements, asked, base.uncertain(),
                // Read after every position was measured, so that what a position's classes would
                // not compose is in it. Taken before, the list is what the producers handed over and
                // nothing this stage found out.
                List.copyOf(found.found().reported()), found.found().stopping(),
                // Carried across: what a reading could not hold together is a fact about the
                // declarations, and a body drawing a line on a position does not make the product
                // it was read from the relation the rules admit.
                // Turned into borders here and nowhere else, so that every rule about one
                // quantity is arranged together however the rules were written — a body's
                // condition and a clause cut one form as readily as two conditions do.
                // Every rule about one quantity arranged together, whichever producer its border
                // came from. A line that divides a position leaves its division on the axis and,
                // where the position has no value beside it, its border over here — and the two
                // sides of that border are runs of what all of them leave.
                base.notSeparated(), across,
                lines,
                reaching, closed.partition(), closed.border(),
                // Carried across. Whether the rules leave the input a value is the declarations'
                // answer, and a body drawing lines on what they left does not change it.
                base.inputIsEmpty(),
                operationsStanding);
    }

    /**
     * The lines each position has, assembled where the reading of the declarations is.
     *
     * <p>Here and not at whoever measures them. Which lines a position has is what the model says,
     * and a reader assembling them needs what the rules leave the term — so assembled at the reader,
     * it takes a reading of its own and the set of lines becomes that reader's answer rather than
     * the model's.
     *
     * <p>Only the positions there is anything to measure at. A position with no classes and no cuts
     * has no line to draw, and an entry saying so would be a list of nothings per behavior. Nor
     * does one no value can stand at, though the input has values: the elements of a container
     * the rules hold to none. A row puts nothing there, so nothing there is owed one.
     */
    private static Map<AxisId, List<Border>> linesAlong(
            List<Axis> axes, Quantities reading, LinesRead read,
            BiPredicate<LineOrigin, LineOrigin> apart) {
        Map<AxisId, List<Border>> out = new LinkedHashMap<>();
        for (Axis axis : axes) {
            if (axis.asksForARow() && reading.projectionOfTheDeclarations(axis.term())
                    instanceof NumericDomain.FormProjection.Within(NumericDomain.Bounds within)) {
                out.put(axis.id(), bordersOf(axis, reading, within, read, apart));
            }
        }
        return out;
    }

    /** A count written at a position, wearing every name that position declares — which the reading
     *  of the position says, and nothing here asks again. */
    private static FixtureTemplate standing(TypeView view, Carrier carrier, Place at,
            RuleReadingSource ruleSource) {
        return WornNames.under(view.wrappers(),
                FixtureTemplate.on(carrier, at, ruleSource.symbols().scope()::reach), ruleSource);
    }

    /** The cuts a position has, with the values a body singled out added as lines of their own. */
    private static List<Cut> mergedPoints(List<Cut> had, List<GuardThresholds.Guards.Singled> points,
                                          Carrier carrier) {
        Map<String, Cut> byValue = new LinkedHashMap<>();
        for (Cut cut : had) {
            byValue.put(cut.key(), cut);
        }
        for (GuardThresholds.Guards.Singled each : points) {
            Cut cut = Cut.at(carrier, each.value(), each.origin());
            byValue.merge(cut.key(), cut, (there, _) -> there.and(each.origin()));
        }
        return List.copyOf(byValue.values());
    }

    /**
     * What the rules leave one term, including a term an axis only took on here.
     *
     * <p>Which numbers a position is measured at is not settled by the reading of the declarations
     * alone: a bare list nothing bounds becomes an axis about its length where a body measures it,
     * and what such a term guarantees of its own values is what bounds it. Asked of the reading
     * rather than kept per term beside it, which is where the two came to disagree.
     */
    private static NumericDomain.Bounds domainOf(Quantities reading,
                                                 NumericTerm term) {
        return reading.runsBetween(term);
    }

    /**
     * Where the rules part each of this behavior's quantities, by the quantity they are on.
     *
     * <p>Read off the axes, which is where a division of a position is recorded whether or not the
     * position has a value at it. A line over a form of several positions divides none of them and
     * is on a quantity of its own, which no axis names — those arrive with the lines themselves.
     */
    private static Map<String, List<Parting>> partedByQuantity(List<Axis> axes) {
        Map<String, List<Parting>> out = new LinkedHashMap<>();
        for (Axis axis : axes) {
            if (axis.parted().isEmpty()) {
                continue;
            }
            out.computeIfAbsent(QuantityKey.of(LinearForm.atom(axis.term())).key(),
                    _ -> new ArrayList<>()).addAll(axis.parted());
        }
        return out;
    }

    private static List<Cut> merged(List<Cut> had, List<Threshold> thresholds, Carrier carrier) {
        Map<String, Cut> byValue = new LinkedHashMap<>();
        for (Cut cut : had) {
            byValue.put(cut.key(), cut);
        }
        for (Threshold each : thresholds) {
            // A line the position has no value at is not a cut of it. It divides the position all
            // the same — the classes either side are what the model distinguishes — and there is no
            // value for a row to be written at, so there is no border here either. The rule's own
            // border is on the quantity it wrote, which can name the line.
            if (each.value() == null) {
                continue;
            }
            Cut cut = Cut.at(carrier, each.value(), each.origin());
            byValue.merge(cut.key(), cut, (there, _) -> there.and(each.origin()));
        }
        return List.copyOf(byValue.values());
    }

    /**
     * The borders a position's rules drew, one per rule that drew a cut.
     *
     * <p>One entry per line and not per point. What each of them owes a row at, in each of the four
     * roles the technique names, is the border's own answer — including the roles it owes nothing in
     * and why. Built as a list of points instead, a role nobody was owed a row in and a role this
     * reader forgot to build were the same thing.
     *
     * <p>Keeping a rule per cut means the same value can be owed three times. That is the point: an
     * invariant and two guards that name one value are three rules, and a row that meets one of them
     * has met one.
     *
     * <p>Not visible outside this package, so that what lines a behavior has is asked of the
     * partitioning ({@link Partitioning#along}) and never assembled again. Assembling them takes
     * what the rules leave the term, which is a reading of the declarations — so a caller that could
     * assemble them would be deciding, from a reading of its own, which lines exist to be measured.
     *
     * @param apart whether no row meets two lines at once, which leaves the one's places out of the
     *              runs beside the other ({@link ReachingCuts#neverTogether})
     */
    static List<Border> bordersOf(Axis axis, Quantities reading, NumericDomain.Bounds within,
                                  LinesRead read, BiPredicate<LineOrigin, LineOrigin> apart) {
        // Both orders of the number this axis measures, as the reading has them. A pair put
        // together here out of the position's order and the carrier a cut was drawn on is a pair
        // whose two halves came from two places, and the day they part is the day a row is decoded
        // on a count the value is not written in.
        TermOrders orders = reading.ordersOf(axis.term());
        // What the declarations hold the value to, which the range alone cannot say: a point inside
        // the range they refuse is one the rules refuse.
        HeldValues heldTo = HeldValues.of(reading.region(), orders);
        List<Border> out = new ArrayList<>();
        // Every place the rules part this position's values, collected before any border is built.
        // What a comparison's border owes away from its line is a run of the arrangement they make
        // together, and one built without them would read its two sides to the end of the order —
        // so a row in the partition after next would answer for a point inside the one it bounds.
        // A bound reads none of them: its run is what the rules leave.
        // Every place the rules part this position's values: the ones its cuts stand at, and the
        // ones no cut stands at because the position holds no value there. A border built from the
        // cuts alone read its two sides past exactly the lines that were left out.
        List<Parting> known = new ArrayList<>(axis.parted());
        UnheldNumber notWorkedOut = null;
        for (Cut cut : axis.cuts()) {
            BoundaryTarget where = BoundaryTarget.at(
                    new BorderQuantity.OfACoordinate(axis.id().behavior(), axis.term(), orders),
                    new Level.OnACarrier(cut.carrier(), cut.at()));
            for (LineOrigin origin : cut.origins()) {
                // Every rule that drew a line here, as it was read. Which of them fall in one place
                // is the arrangement's answer, and telling them apart here kept the first and lost
                // the rest — so a run bounded by two rules knew about one of them. A place that was
                // not worked out is kept as that, since every border on this position is read off
                // an arrangement it is missing a place of.
                switch (Border.partedBy(where, origin)) {
                    case ExactAnswer.Held<List<Parting>> held -> known.addAll(held.value());
                    case ExactAnswer.Unheld<List<Parting>> unheld -> {
                        if (notWorkedOut == null) {
                            notWorkedOut = unheld.why();
                        }
                    }
                }
            }
        }
        for (Cut cut : axis.cuts()) {
            // The level is on the cut's carrier, which is the one the rule was read on. What the
            // quantity is measured on is the reading's answer and not read off the line: a line
            // drawn on a count taken of a position would otherwise be written back as a value of
            // the position.
            BoundaryTarget target = BoundaryTarget.at(
                    new BorderQuantity.OfACoordinate(axis.id().behavior(), axis.term(), orders),
                    new Level.OnACarrier(cut.carrier(), cut.at()));
            for (LineOrigin origin : cut.origins()) {
                // One cut, one border. Whether the quantity reaches the line is settled where the
                // cut was made — a bound's line is an end of what the bound leaves — so there is
                // nothing to test here and nothing to drop. It used to answer null and be dropped
                // without a word, which is how a strict bound on a carrier with no step left the
                // measure saying the behavior's rules draw no line anywhere (issue #1079).
                //
                // The line is written down as it is met and the border where it lands, so that the
                // day something is written between the two the reading is held to having lost one.
                read.found(target, origin);
                ExactAnswer<List<Parting>> parted;
                if (notWorkedOut == null) {
                    parted = ExactAnswer.held(Border.besideThe(origin, known, apart));
                } else {
                    parted = ExactAnswer.unheld(notWorkedOut);
                }
                out.add(read.drew(Border.at(target, origin, within, heldTo, parted,
                        axis.narrowed())));
            }
        }
        return List.copyOf(out);
    }

    /**
     * One position, turned into an axis or given up in favour of what is under it.
     *
     * <p>The local answer first, whole: the classes the position's declarations state and the lines
     * its rules draw come back as one value, so what "local evidence ran out" means is an answer
     * rather than two empty lists to be noticed. Only where it ran out does what the position is
     * made of decide anything — a position its own declarations answered for keeps its axis,
     * whatever is under it, and that precedence is the arm this is written in rather than the order
     * of two {@code if}s.
     *
     * <p>Of the structural answers only {@code Children} takes the position away: the fields are
     * positions of their own and were read as such, and the classes belong to them. A leaf and a
     * block both leave the position standing, pending what a body's rules say later.
     *
     * <p><b>A position with local evidence and children is unreachable today, and is refused rather
     * than resolved.</b> Only a product has children, and a product states no distinction — its type
     * declares no division — and carries no cut, having no order for a rule to name a value on. A
     * language that grew one would have this reader keeping the parent's axis while the reading kept
     * its fields, and two readers of one input disagreeing about which positions there are is the
     * thing this arrangement exists to stop.
     */
    private static void axisOf(String behavior, Position position, RuleReadingContext reading,
                               List<Drawn> drawn,
                               java.util.Set<NumericTerm> uncertain,
                               RulesWithNoLine.Gathered rulesWithoutALine) {
        rulesWithoutALine.addAll(position.rulesWithoutALine());
        switch (LocalInspection.of(position, reading)) {
            case LocalPartition.Divided divided -> {
                if (position.structure() instanceof StructuralInspection.Decomposed) {
                    throw new IllegalStateException(
                            "`" + position.path() + "` both divides and is made of positions; the"
                                    + " reading of an input and the axes drawn from it disagree"
                                    + " about which positions there are");
                }
                // One axis per measure the declarations made, and nothing decided here. Which
                // number each of them is of is the reading's answer and arrives as it was given;
                // what this adds is the behavior the measure is named after.
                List<Axis> axes = new ArrayList<>();
                for (DeclaredMeasure each : divided.measures()) {
                    if (each.cuts() instanceof CutEvidence.Present cut && cut.uncertain()) {
                        uncertain.add(each.term());
                    }
                    axes.add(Axis.of(behavior, each.term(), each.classes(), List.of(),
                            each.cuts().cuts(), List.of(), each.narrowed()));
                }
                // No continuation, because something answered for the position and a fallback is
                // what a position with no answer is left with. What the reading came to is carried
                // all the same: a `Map` a rule about its size divides is one nothing was read into,
                // and taking that off the axis with the fallback is how the stop went unreported
                // (issue #1084).
                PositionAccount at = PositionAccount.of(behavior, position, null);
                drawn.add(new Drawn(at, List.copyOf(axes)));
            }
            // Nothing local divides the position, which is what licenses asking what it is made of.
            // What its rules still raise is carried rather than acted on here: a position made of
            // positions is given up in favour of what is under it either way, and a question about
            // the whole value says nothing about which of its fields it would have divided.
            case LocalPartition.Open _ -> {
                switch (position.structure()) {
                    // The one answer that takes the position away: what is under it is what the
                    // classes belong to, and those positions were read on their own.
                    case StructuralInspection.Decomposed _ -> { }
                    // A leaf and a block are both positions still to be answered for, and each
                    // carries what the walk found and what its rules still raise, which is what
                    // keeps the position from completing as one the model divides no way.
                    case StructuralInspection.Retained retained -> {
                        // The position and no measure of it. Nothing local divided the number the
                        // declarations name, and a measure with nothing in it would be a location
                        // counted among the measures — what is still to be answered for here is
                        // the position's to carry.
                        drawn.add(new Drawn(
                                PositionAccount.of(behavior, position, retained.continuation()),
                                List.of()));
                    }
                }
            }
        }
    }



    // --- small helpers ----------------------------------------------------------------------------

    /** Values that could stand for a type wherever nothing else has been said about the position — the
     * inner value of a newtype, a field no axis divides. A record is not one of these: its fields are
     * composed, which is the generator's work and not a value this can hand over.
     *
     * <p>With what of this compiler's building them met ({@link Proposals}), so that a position
     * offering a value short of its rules because the value they ask for is past a figure says so. */
    static Proposals representativesOf(Type type, RuleReadingContext reading) {
        return representativesOf(type, reading, null);
    }

    /**
     * The same, for a position the record it sits in has already narrowed.
     *
     * <p>{@code within} is what is left of the position once the rest of the assignment is settled:
     * an {@code endsAt} beside a {@code startsAt} of 1439 can only be 1440, and the value this offers
     * has to come from there rather than from the bottom of the type's own range.
     */
    static Proposals representativesOf(Type type, RuleReadingContext reading,
                                       NumericDomain.Bounds within) {
        return representativesOf(type, reading, within, Set.of());
    }

    /**
     * The same, with the newtypes this is already inside the value of.
     *
     * <p>Carried because what stands for a collection is built from what stands for its element, which
     * is this question again. A name met while its own value is being built is a type written in terms
     * of itself and is given up on — the names and not a count of them, since how many names a value
     * wears on the way down is not what has to be stopped.
     */
    static Proposals representativesOf(Type type, RuleReadingContext reading,
                                       NumericDomain.Bounds within,
                                       Set<TypeSymbol> expanding) {
        return type == null ? Proposals.NONE
                : representativesOf(TypeView.of(type, reading.source().inners(), reading.source().symbols(),
                        reading.source().kinds(), reading.source().sums()), reading,
                        within, expanding);
    }

    /**
     * The same, of a position that has already been read.
     *
     * <p>One reading, three answers taken from it. What the position is, with every name off, is what
     * the values are made of; the rules of every name it wears are the rules its value is under; and
     * the names themselves are what the value is written with. Held as one walk, how far to look to
     * know what a rule is about and how far to descend to write the value were the same number — and
     * one name is right for the second and wrong for the first, so a rule on a name that wraps a name
     * was never reached.
     *
     * <p>Rules first, then what the shape stands for. Each rule is a reason to offer another value
     * and never to withdraw one already offered: which of them the whole of the rules admits is the
     * decoder's answer, so a position carrying a format and a floor gets a value from each and the
     * order they were declared in does not decide whether one builds.
     *
     * <p><b>And a value every rule admits, which is none of theirs.</b> A proposal per rule is a
     * proposal each of the others may refuse, so a position carrying two rules about its strings was
     * offered what each asked for and nothing that clears both — the decoder refused all of it and
     * the position had no value at all. That it went unnoticed is what the rest of this offers: a
     * rule counting the value reaches the same meet through {@link Witnesses}, so the same two rules
     * composed a row wherever a third rule happened to count what they were about.
     */
    static Proposals representativesOf(TypeView view, RuleReadingContext reading,
                                       NumericDomain.Bounds within,
                                       Set<TypeSymbol> expanding) {
        return representativesOf(view, reading, within, expanding, RulesAround.NONE);
    }

    /**
     * The same, of a value built inside others whose rules name places in it ({@link RulesAround}):
     * a record of it, or a case of a sum it is, is built field by field held to those rules as
     * well, under the names the value wears as any value of it is.
     */
    static Proposals representativesOf(TypeView view, RuleReadingContext reading,
                                       NumericDomain.Bounds within,
                                       Set<TypeSymbol> expanding, RulesAround around) {
        RuleReadingSource ruleSource = reading.source();
        // Already inside the value of one of the names this wears, so the type is written in terms of
        // itself and there is nothing to hand back. Which is the answer and not a limit: no value of
        // such a type exists.
        Set<TypeSymbol> inside = new LinkedHashSet<>(expanding);
        for (TypeSymbol wears : view.wrappers()) {
            if (!inside.add(wears)) {
                return Proposals.NONE;
            }
        }
        // A name this module cannot write leaves no value to write. Asked of the position and not of
        // each value: whether the names can be spelled is a fact about where the value is going, and
        // a value at a position wearing one of them is no value here whatever it is.
        if (!(WornNames.of(view.wrappers(), ruleSource) instanceof WornNames.Spelled spelled)) {
            return Proposals.NONE;
        }
        // What the rules say about the strings and how many characters they hold, each read once
        // for the three readers below. Asked again per reader, a position carrying a format paid
        // for the clauses to be walked and the counts to be read as many times as it has readers.
        PatternsStated stated = patternsStatedOn(view, ruleSource);
        DeclaredBounds.CountRange characters = DeclaredBounds.countsHeld(view, reading, null);
        // What the rules ask for, and then what the position is where nothing was written about it,
        // each value once and under the names the position wears.
        Proposals.Gathering candidates = Proposals.Gathering.distinct();
        Function<FixtureTemplate, FixtureTemplate> named =
                each -> RepresentativeSource.under(spelled.names(), each);
        candidates.addAll(Proposals.of(whatEveryRuleAdmits(stated, characters, reading)).map(named));
        candidates.addAll(Proposals.of(whereTheRulesLeaveTheValue(view, reading, within)).map(named));
        candidates.addAll(Proposals.of(whatAFormatAsksFor(stated.patterns(), reading)).map(named));
        // What the rules say the value holds, before the value that would hold nothing. A floor
        // past what a proposal holds is a value not built, and stands where it would have stood.
        candidates.addAll(Witnesses.holding(view, characters.least(), List.of(), reading, inside)
                .map(named));
        Proposals ofTheShape = whatTheShapeStandsFor(view, reading, within, inside, around);
        candidates.addAll(ofTheShape.map(named));
        // Where the shape stands for no value of its own, what stands at the position is one of the
        // kinds its type divides into, and the classes are what name them. Asked only there, because
        // a class of a position says what stands at the position under it: asked of a shape that has
        // a value of its own, the answer is that value again, arrived at by building it.
        if (ofTheShape.isEmpty()) {
            candidates.addAll(dividedInto(view, reading, inside, around));
        }
        return candidates.done();
    }

    /**
     * What a position divides into, or nothing where its type states no division.
     *
     * <p>The first class anything can be produced for and not all of them: what is wanted here is a
     * value of the position, and the classes are how a position that has more than one kind of value
     * says which kinds there are. Their recipes carry the names the position wears already
     * ({@link RepresentativeSource}), so nothing is put on them here.
     *
     * <p>Where there were classes and none produced a value, that is the answer. Each said nothing
     * can be produced for it and why, and arriving at a value another way is this deciding the
     * classes were wrong about themselves — the answer they carry is the one an author is shown.
     */
    private static Proposals dividedInto(TypeView view, RuleReadingContext reading,
                                         Set<TypeSymbol> expanding, RulesAround around) {
        // In front of what is offered, what the classes passed over met: a class with nothing for a
        // figure is the class that would have been offered in its place.
        Proposals.Gathering out = Proposals.Gathering.inOrder();
        for (PartitionClass each : PartitionClasses.of(
                Distinctions.ofType(view.shape(), reading.source().symbols(),
                        reading.source().kinds(), reading.source().sums()),
                view, reading, expanding)) {
            Proposals stands = standingFor(each.representatives(), reading, expanding, around);
            out.addAll(stands);
            if (!stands.isEmpty()) {
                return out.done();
            }
        }
        return out.done();
    }

    /**
     * The value at the edge the rules leave, or nothing where they leave no edge.
     *
     * <p>Read of the position and not of one of its names: a value wearing two names is bounded by
     * the rules written on either, and both are what its reading came to. Nothing where no rule and
     * no narrowing said anything — the value the position stands for is what answers there, and a
     * number named here as well would be the same number said twice.
     */
    private static List<FixtureTemplate> whereTheRulesLeaveTheValue(TypeView view,
                                                                    RuleReadingContext reading,
                                                                    NumericDomain.Bounds within) {
        RuleReadingSource ruleSource = reading.source();
        DeclaredBounds.Range own = DeclaredBounds.of(view, reading);
        if (own == null) {
            return List.of();   // nothing here reads a number of this position at all
        }
        NumericDomain.Bounds bounds = TypeBounds.admissible(own, within);
        Place held = bounds == null || bounds.saysNothing() ? null
                : inside(bounds, own.carrier(), reading.today());
        FixtureTemplate at = held == null ? null
                : FixtureTemplate.on(own.carrier(), held, ruleSource.symbols().scope()::reach);
        return at == null ? List.of() : List.of(at);
    }

    /**
     * A value each of {@code stated} admits, in the order they were read.
     *
     * <p>One per rule and none of them met with another: each is what one rule asked for, and which
     * of them the whole of the rules admits is the decoder's answer. What every rule admits at once
     * is a value of its own ({@link #whatEveryRuleAdmits}) and is offered beside these.
     *
     * <p>Innermost first, which is an order over the proposals and not over the rules: every name's
     * rules govern the value, whichever end they are read from. What the order decides is which
     * proposal a bounded search reaches before it stops, and the value a name wraps is the one its
     * own rules were written closest to. It is {@link #patternsStatedOn}'s order, read once for
     * every reader of it here.
     *
     * <p>Each value is the revision's ({@link PatternForAWitness}). A pattern whose machine could
     * not be built and one none of whose strings anybody can paste both offer nothing, and are not
     * told apart here: a row is offered or it is not, and what the offer was short of is said where
     * a search came back without one.
     */
    private static List<FixtureTemplate> whatAFormatAsksFor(
            List<StringPredicates.StatedPattern> stated, RuleReadingContext reading) {
        List<FixtureTemplate> out = new ArrayList<>();
        for (StringPredicates.StatedPattern each : stated) {
            if (reading.revision().settled(new PatternForAWitness(each))
                    instanceof PatternForAWitness.Made.Built(var _, Optional<String> written)) {
                written.ifPresent(text -> out.add(FixtureTemplate.string(text)));
            }
        }
        return out;
    }

    /**
     * The value a shape stands for where nothing has been written about the position.
     *
     * <p>Exhaustive, with no {@code default}: what stands at a position is a question about each
     * kind of position, and a shape added later is one this has to be told about rather than one
     * that falls to whichever arm it was not named in.
     */
    private static Proposals whatTheShapeStandsFor(TypeView view, RuleReadingContext reading,
                                                   NumericDomain.Bounds within,
                                                   Set<TypeSymbol> inside, RulesAround around) {
        RuleReadingSource ruleSource = reading.source();
        return switch (view.shape()) {
            case Shape.Scalar scalar -> Proposals.of(standsForA(scalar, within, reading));
            // The empty one, for every collection nothing has said otherwise about. A row whose
            // collection is not what it is about should say so by carrying nothing, and where no rule
            // counts what the position holds there is nothing else to go on.
            case Shape.Sequence _, Shape.Mapping _ ->
                    Proposals.of(List.of(FixtureTemplate.emptyCollection()));
            // Absence, which every optional holds. Answered here rather than through the classes
            // because what a class says about `Some` is what stands for the element, and asking that
            // while the element is being built is the element asking for itself.
            case Shape.Optional _ -> Proposals.of(List.of(FixtureTemplate.none()));
            // A unit data is one value, and naming it writes it. Nothing tells its one value from
            // another, so no class of the position names it and it is said here.
            case Shape.Unit unit ->
                    ruleSource.symbols().scope().reach(unit.name())
                            instanceof TypeReachName.Written written
                            ? Proposals.of(List.of(FixtureTemplate.unitCase(written)))
                            : Proposals.NONE;
            // A record is written field by field, against the rules relating them — those of the
            // names it is worn under as well as its own.
            case Shape.Product product -> product.name() instanceof TypeSymbol.AtModule named
                    ? composed(named, rulesOver(view.wrappers(), named, ruleSource), reading,
                            inside, around)
                    : Proposals.NONE;
            // What a sum or a union stands for is which of its cases it is, which is what the
            // position divides into rather than a value to name here.
            case Shape.Sum _, Shape.Cases _ -> Proposals.NONE;
            // And the shapes that carry no value of their own, or that this compiler could not read.
            case Shape.Unresolved _, Shape.Tuple _, Shape.Function _, Shape.Uninhabited _,
                 Shape.Bottom _, Shape.Erroneous _, Shape.Undecided _ -> Proposals.NONE;
        };
    }

    /** The value a primitive stands for, which for one whose values are counted is one the position
     *  is left able to hold and for the rest is one fixed value. */
    private static List<FixtureTemplate> standsForA(Shape.Scalar scalar, NumericDomain.Bounds within,
                                                    RuleReadingContext reading) {
        return switch (scalar.prim()) {
            // Where the range is entered on the order the value is compared on, which is where a
            // second value and a set's further elements are stepped from as well, so the second is
            // beside the first. A date is entered nearest the day the reading was made on, which
            // the compilation settles once: never the clock's, which would move between two rows of
            // one block.
            case INT, DECIMAL, DATE, TIME, DATETIME, INSTANT ->
                    countStandingFor(Carrier.ofPrimitive(scalar.prim()), within, reading);
            case STRING -> List.of(FixtureTemplate.string("x"));
            case BOOL -> List.of(FixtureTemplate.bool(true));
            // A Rational reaches no position: it has no external form, so nothing declares one and no
            // row is written at one (ADR-0116). Said here rather than left to the arm above, which
            // would offer a value of a type a fixture cannot carry.
            case RATIONAL -> List.of();
        };
    }

    /** A count the position is left able to hold, or none where what is left of it holds none. */
    private static List<FixtureTemplate> countStandingFor(Carrier carrier,
                                                          NumericDomain.Bounds within,
                                                          RuleReadingContext reading) {
        Place at = inside(within, carrier, reading.today());
        FixtureTemplate standing = at == null ? null
                : FixtureTemplate.on(carrier, at, reading.source().symbols().scope()::reach);
        return standing == null ? List.of() : List.of(standing);
    }

    /**
     * The values a recipe arrives at, whichever way it arrives at them.
     *
     * <p>{@code Values} and {@code Compose} are two ways of writing where a representative comes
     * from and not two answers about whether there is one, so a reader asking for one takes both
     * here. Read as a reader's own two questions — is it generatable, and does it hold values — a
     * class naming a constructor answered yes and then handed over nothing, and the position it
     * stood at was reported as one no value can be written at (issue #651).
     *
     * <p>And what of this compiler's arriving at them met, the class's own where it says it was
     * not arrived at.
     */
    static Proposals standingFor(RepresentativeSource source, RuleReadingContext reading,
                                 Set<TypeSymbol> expanding) {
        return standingFor(source, reading, expanding, RulesAround.NONE);
    }

    /** The same, of a class of a value built inside others whose rules name places in it
     *  ({@link RulesAround}). */
    static Proposals standingFor(RepresentativeSource source, RuleReadingContext reading,
                                 Set<TypeSymbol> expanding, RulesAround around) {
        return switch (source) {
            case RepresentativeSource.Values values -> values.offered();
            // Against the case's own rules: the names the position wears are over the sum, and a
            // rule of theirs reads no field of one of its cases. A rule of a value around the sum
            // reads the names its cases share, and comes down with it.
            case RepresentativeSource.Compose compose ->
                    composed(compose.through(), compose.through(), reading, expanding, around)
                            .map(compose::written);
            case RepresentativeSource.NothingProducible _ -> Proposals.NONE;
            case RepresentativeSource.NotArrivedAt notArrived ->
                    Proposals.NONE.meeting(notArrived.met());
        };
    }

    /**
     * A record composed field by field, or nothing where one of its fields has nothing to stand for
     * it.
     *
     * <p>{@code expanding} carries the names this is already inside the value of, so a record
     * reached from its own field is given up on there rather than composed forever. Path-local: a
     * name is in it only while the value under it is being built, so a type met twice in two
     * branches is composed in both.
     *
     * <p>Each field is chosen against what the record's rules leave it, which is the reading
     * {@link FieldDomains} makes of them: the range a clause leaves the value, and the floor a
     * clause counting it puts on what it holds. Chosen from the field's type alone, a record whose
     * rule asks its list for two is handed one holding none, and the row it was composed for comes
     * back as one every value tried was refused at.
     *
     * <p>Nothing about the clauses relating two fields, which are read where a row is searched for
     * one position at a time. Whether the values may be held together is the decoder's answer — the
     * same answer every other candidate this offers is put through.
     *
     * <p>Composed once for the revision ({@link ARecordComposed}). A search asks what stands for a
     * record from every point and every settling it visits, and the answer is about the record and
     * the rules and nothing about where the search is.
     *
     * <p>Except where a rule of a value around the record reads one of its places: then the record
     * is composed here, held to that rule as well, since the answer is about where it is built.
     * Each such composing is counted against the one count its outermost record was given
     * ({@link RulesAround#reserve}), whatever sum or record it is under — the cases of each nested
     * sum multiply, and a count per sum would let the product past it.
     *
     * @param rulesOn the name whose rules the fields are chosen against ({@link #rulesOver})
     */
    private static Proposals composed(TypeSymbol.AtModule record, TypeSymbol.AtModule rulesOn,
                                      RuleReadingContext reading,
                                      Set<TypeSymbol> expanding, RulesAround around) {
        // Given up on before it is asked, so that a record reached from its own field is the work
        // stopping and never the work borrowing itself.
        if (expanding.contains(record)) {
            return Proposals.NONE;
        }
        if (around.readAnything()) {
            // Taken before the fields are chosen: a record built inside this one asks the same
            // count, and one asked only afterwards lets every record on the way down pass it.
            if (!around.reserve()) {
                return Proposals.NONE.meeting(CompositionShortfall.of(
                        Set.of(CompositionBudget.CASES_A_RULE_ABOVE_IS_PLANNED_UNDER)));
            }
            FieldsChosen chosen = fieldsOf(record, rulesOn, reading, expanding, Map.of(), around);
            // Given back where nothing was built: a record whose rules leave one of its fields no
            // value was settled before that, and a count spent on it is a case further on never
            // tried.
            if (chosen.leftNothing()) {
                around.refund();
            }
            return written(record, chosen, reading.source());
        }
        return reading.revision().settled(
                new ARecordComposed(record, rulesOn, reading, expanding));
    }

    /**
     * The name whose rules a record worn under {@code worn} is composed against: the outermost of
     * them that wraps the record itself, or the record where none does.
     *
     * <p>The outermost, because a name's reading reaches every rule beneath it — those of each name
     * it wraps and the record's own — and names a field of the record as the record does, a
     * newtype's value being at no name of its own. Read on the record alone, a rule a name wrapping
     * it writes about one of its fields is a rule the value is held to and nothing composing it was
     * told of.
     *
     * <p>One that wraps the record and not a sum it is a case of: a position narrowed to a case
     * wears the names over the sum as well, and a rule of theirs reads no field of a case.
     */
    static TypeSymbol.AtModule rulesOver(List<? extends TypeSymbol> worn,
                                         TypeSymbol.AtModule record, RuleReadingSource source) {
        for (TypeSymbol each : worn) {
            if (each instanceof TypeSymbol.AtModule named
                    && TypeView.shapeOf(Type.ref(named), source.inners(), source.symbols(),
                            source.kinds(), source.sums()) instanceof Shape.Product product
                    && record.equals(product.name())) {
                return named;
            }
        }
        return record;
    }

    /** The same, of a position of type {@code position} whose value is {@code record}: the name it
     *  is written under, where it is written under one. */
    static TypeSymbol.AtModule rulesOver(Type position, TypeSymbol.AtModule record,
                                         RuleReadingSource source) {
        return rulesOver(position instanceof Type.Ref ref ? List.of(ref.name()) : List.of(),
                record, source);
    }

    /**
     * What stands for a record with none of its fields decided, as work settled by the record, the
     * name its rules are read on, the source they are read from, what the reading may spend and the
     * names it is inside.
     *
     * <p>The source by its origin and not by the reading that is handed over to do the work. A
     * reading is a capability and compares as one, so two readings of one source are two objects;
     * the origin is what says they are one source ({@link RuleReadingSource.Origin}), and under one
     * origin and one policy a revision has one world to read in — the terms a declaration's own
     * reading is lent under ({@link DeclarationReadings#reading}). The reading is carried to do the
     * work with and is no part of which work this is.
     *
     * <p>The names it is inside, as a set. Which of them a value is under is what decides where a
     * record reached from its own field is given up on, and the order they were met in decides
     * nothing.
     *
     * <p>Kept with what composing it met, so that a record with no value because a field's value
     * is past a figure says so wherever it is asked for — kept apart, the second asking would have
     * the record and not the reason.
     */
    static final class ARecordComposed implements RevisionWork<Proposals> {

        private final TypeSymbol.AtModule record;

        private final TypeSymbol.AtModule rulesOn;

        private final RuleReadingSource.Origin origin;

        private final ReadingPolicy policy;

        private final Set<TypeSymbol> expanding;

        private final RuleReadingContext reading;

        ARecordComposed(TypeSymbol.AtModule record, TypeSymbol.AtModule rulesOn,
                        RuleReadingContext reading, Set<TypeSymbol> expanding) {
            this.record = record;
            this.rulesOn = rulesOn;
            this.origin = reading.source().origin();
            this.policy = reading.policy();
            this.expanding = Set.copyOf(expanding);
            this.reading = reading;
        }

        @Override
        public Proposals workedOut(RevisionKnowledge revision) {
            return composed(record, rulesOn, reading, expanding, Map.of(), RulesAround.NONE);
        }

        @Override
        public boolean equals(Object other) {
            return other instanceof ARecordComposed it && record.equals(it.record)
                    && rulesOn.equals(it.rulesOn) && origin.equals(it.origin)
                    && policy.equals(it.policy) && expanding.equals(it.expanding);
        }

        @Override
        public int hashCode() {
            return Objects.hash(record, rulesOn, origin, policy, expanding);
        }

        @Override
        public String toString() {
            return "ARecordComposed[" + record + " under the rules of " + rulesOn + " inside "
                    + expanding + "]";
        }
    }

    /**
     * The same, with some fields already decided.
     *
     * <p>A field handed over is not chosen and is settled like any other: the rules are read again
     * with it in them, so what the fields beside it may be is asked of the record as it is being
     * built rather than of the record before anything was said. A caller composing the rest itself
     * would be choosing them against {@code a < b} with {@code a} open, which is the reading this
     * loop exists to avoid.
     *
     * @param given  what stands at some of the fields, by name. A name no field has is nothing this
     *               can build, and is the caller asking for a value of another type
     * @param around the rules of the values the record is built inside ({@link RulesAround})
     */
    static Proposals composed(TypeSymbol.AtModule record, TypeSymbol.AtModule rulesOn,
                              RuleReadingContext reading, Set<TypeSymbol> expanding,
                              Map<String, FixtureTemplate> given, RulesAround around) {
        if (expanding.contains(record)) {
            return Proposals.NONE;
        }
        return written(record, fieldsOf(record, rulesOn, reading, expanding, given, around),
                reading.source());
    }

    /** The record {@code chosen} builds, where {@code record} can be written, with what it met. */
    private static Proposals written(TypeSymbol record, FieldsChosen chosen,
                                     RuleReadingSource ruleSource) {
        return (chosen.fields() == null || !(ruleSource.symbols().scope().reach(record)
                instanceof TypeReachName.Written written)
                        ? Proposals.NONE
                        : Proposals.of(List.of(FixtureTemplate.record(written, chosen.fields()))))
                .meeting(chosen.met());
    }

    /**
     * What {@code within} leaves the number of each field of an element of {@code container}, for
     * the fields that hold one and are left less than their type holds.
     *
     * <p>Asked of the fields that hold a number and of no other: the region answers for numbers,
     * and a field of text or of a container has none to be asked of. And of the fields of the
     * element itself — a field of a record in the element is the record's own, which the ends
     * are not read for.
     *
     * @param record    the type of the element
     * @param container the container the way bounds the elements of, which a parameter roots
     */
    static Map<String, NumericDomain.Bounds> leftTheFieldsOfAnElement(
            TypeSymbol.AtModule record, TermPath container, SearchRegion within,
            RuleReadingContext reading) {
        RuleReadingSource ruleSource = reading.source();
        if (!(TypeView.shapeOf(Type.ref(record), ruleSource.inners(), ruleSource.symbols(),
                ruleSource.kinds(), ruleSource.sums())
                instanceof Shape.Product(TypeSymbol _, SequencedMap<String, Type> fields))) {
            return Map.of();
        }
        Map<String, NumericDomain.Bounds> held = new LinkedHashMap<>();
        for (Map.Entry<String, Type> field : fields.entrySet()) {
            TypeView view = TypeView.of(field.getValue(), ruleSource.inners(),
                    ruleSource.symbols(), ruleSource.kinds(), ruleSource.sums());
            if (DeclaredBounds.of(view, reading) != null
                    && within.projectionOf(
                            new NumericTerm.ValueOf(container.element().then(field.getKey())))
                    instanceof NumericDomain.FormProjection.Within(NumericDomain.Bounds bounds)
                    && !bounds.saysNothing()) {
                held.put(field.getKey(), bounds);
            }
        }
        return held;
    }

    /**
     * A record whose fields stand inside {@code held} as well as inside what its rules leave them,
     * each chosen as {@link #composed} chooses one: in the order the record declares them, against
     * the rules with the fields before it settled into them.
     *
     * <p>For a record that is an element of a container composed under what every element is to
     * meet: the bounds are what the way leaves a number of each element. They narrow the field as
     * the record's own rules do, so a rule relating two fields is asked of the second with the
     * first in it — a field chosen inside its bounds alone would be chosen against {@code a + b}
     * with {@code a} open, and would be written where the record's rules refuse it.
     *
     * @param held by field name, what the way leaves that field's number
     */
    static Proposals composedHeldTo(TypeSymbol.AtModule record, TypeSymbol.AtModule rulesOn,
                                    RuleReadingContext reading,
                                    Map<String, NumericDomain.Bounds> held) {
        return written(record,
                fieldsOf(record, rulesOn, reading, Set.of(), Map.of(), RulesAround.NONE, held),
                reading.source());
    }

    /**
     * Values of {@code record} no two of which are alike, up to {@code many} of them, or none
     * where no field of it has two values to differ at.
     *
     * <p>Alike everywhere but the first field whose values are more than one, where that field has
     * as many as were asked for. A record is apart from another wherever one field is, so a field
     * is all a list kept apart as records needs — and the values there are what the record's rules
     * leave the field ({@link FieldDomains.Held}), each written in and the rest composed against
     * the rules as they then stand ({@link #composed}).
     *
     * <p>Where it has fewer, every value found so far is taken on to the next field and written
     * again with each of that field's values beside what it already holds. A record of a two-valued
     * field and a three-valued one has six values, and stopping at the first field offered two of
     * them, which a set of three such records could not be built from. Taken on only while fewer
     * than {@code many} are found, so a record whose first field has enough is answered as before.
     *
     * @param rulesOn the name whose rules the fields are chosen against ({@link #rulesOver})
     */
    static Proposals differingAtItsFields(TypeSymbol.AtModule record, TypeSymbol.AtModule rulesOn,
                                          int many, RuleReadingContext reading,
                                          Set<TypeSymbol> expanding) {
        RuleReadingSource ruleSource = reading.source();
        if (expanding.contains(record)
                || !(TypeView.shapeOf(Type.ref(record), ruleSource.inners(), ruleSource.symbols(),
                        ruleSource.kinds(), ruleSource.sums())
                        instanceof Shape.Product(TypeSymbol _,
                        SequencedMap<String, Type> fields))) {
            return Proposals.NONE;
        }
        Set<TypeSymbol> inside = new LinkedHashSet<>(expanding);
        inside.add(record);
        FieldDomains.Composing left = FieldDomains.of(rulesOn, reading).composing(Map.of());
        // What each value found was written with, in the order found, keyed by how it is written.
        Map<String, Map<String, FixtureTemplate>> found = new LinkedHashMap<>();
        // The records found, and where the walk was stopped on the way to them: a field whose
        // values were cut at a figure, in front of the records that field would have told apart,
        // and a record whose composing met one, in front of that record.
        Proposals.Gathering out = Proposals.Gathering.inOrder();
        for (Map.Entry<String, Type> field : fields.entrySet()) {
            FieldDomains.ConstructionLimits limits = left.at(RuleKey.of(field.getKey()));
            Proposals values = Witnesses.distinctValuesOf(field.getValue(), many,
                    limits.held(), limits.admits(), reading, inside);
            if (values.values().size() < 2) {
                out.stop(values.met());
                continue;
            }
            List<Map<String, FixtureTemplate>> bases = found.isEmpty()
                    ? List.of(Map.of()) : List.copyOf(found.values());
            boolean first = true;
            for (Map<String, FixtureTemplate> base : bases) {
                for (Proposals.Entry entry : values.entries()) {
                    if (out.size() >= many) {
                        return out.done();
                    }
                    switch (entry) {
                        // Met once, the first time the walk comes to it.
                        case Proposals.Stopped(CompositionShortfall met) -> {
                            if (first) {
                                out.stop(met);
                            }
                        }
                        case Proposals.Offered(FixtureTemplate value) -> {
                            Map<String, FixtureTemplate> given = new LinkedHashMap<>(base);
                            given.put(field.getKey(), value);
                            Proposals composed = composed(record, rulesOn, reading, expanding,
                                    given, RulesAround.NONE);
                            out.stop(composed.met());
                            for (FixtureTemplate each : composed.values()) {
                                if (found.putIfAbsent(each.text(), given) == null) {
                                    out.add(each);
                                }
                            }
                        }
                    }
                }
                first = false;
            }
            if (out.size() >= many) {
                return out.done();
            }
        }
        // One record is no values that differ, and what stopped the others is why.
        Proposals differ = out.done();
        return differ.values().size() > 1 ? differ : Proposals.NONE.meeting(differ.met());
    }

    /**
     * Which values the rules of {@code record} leave at {@code field}, which is what a builder of
     * the record's values chooses that field's among.
     *
     * <p>Asked here, where a field of a record is taken for the name its rules write it under,
     * so that a builder holding the field by name is handed the answer rather than deciding for
     * itself which of a value's steps a rule names.
     */
    static AdmissibleSet admittedAt(TypeSymbol.AtModule record, String field,
                                    RuleReadingContext reading) {
        return FieldDomains.of(record, reading).admits(RuleKey.of(field));
    }

    /**
     * What stands at each field of a record, or null where one of them has nothing to stand for
     * it, and what of this compiler's choosing them met.
     *
     * @param fields      by name, in the order the record declares them; null where a field has
     *                    nothing
     * @param met         what building the fields' values met — a field with nothing because its
     *                    value is past a figure is a record this compiler did not build, not one
     *                    with no value
     * @param leftNothing whether a field had nothing because the rules leave it no value, which is
     *                    settled before anything is built and is no record this tried to build
     */
    record FieldsChosen(SequencedMap<String, FixtureTemplate> fields, CompositionShortfall met,
                        boolean leftNothing) {

        static final FieldsChosen NONE = new FieldsChosen(null, CompositionShortfall.NONE);

        FieldsChosen(SequencedMap<String, FixtureTemplate> fields, CompositionShortfall met) {
            this(fields, met, false);
        }
    }

    /**
     * What stands at each field of {@code record}, or nothing where one of them has nothing to
     * stand for it.
     *
     * <p>Beside {@link #composed} and under it: this is the choosing, and writing the record is what
     * a caller then does with it. Asked on its own by the composing of a plan, which has the record
     * to write and needs what goes in it — a caller that took a written record apart again to get at
     * the fields would be reading one answer back out of another.
     *
     * @param rulesOn the name whose rules the fields are chosen against: {@code record} itself, or
     *                a name worn over it ({@link #rulesOver}), whose reading names the record's
     *                fields as the record does
     * @param around  the rules of the values the record is being built inside, which name its
     *                fields as well: each field is held to what they leave it beside what the
     *                record's own rules do
     */
    static FieldsChosen fieldsOf(TypeSymbol.AtModule record, TypeSymbol.AtModule rulesOn,
                                 RuleReadingContext reading, Set<TypeSymbol> expanding,
                                 Map<String, FixtureTemplate> given, RulesAround around) {
        return fieldsOf(record, rulesOn, reading, expanding, given, around, Map.of());
    }

    /**
     * The same, with some fields held to where a search leaves them besides.
     *
     * <p>A field is chosen inside what its record's rules leave it, what the rules around it leave
     * it, and {@code held}: the three are met, and the field is chosen in what they leave
     * together.
     *
     * @param held by field name, the ends a search holds that field's number to, which no rule of
     *             the declarations says
     */
    static FieldsChosen fieldsOf(TypeSymbol.AtModule record, TypeSymbol.AtModule rulesOn,
                                 RuleReadingContext reading, Set<TypeSymbol> expanding,
                                 Map<String, FixtureTemplate> given, RulesAround around,
                                 Map<String, NumericDomain.Bounds> held) {
        RuleReadingSource ruleSource = reading.source();
        // What the record is made of, read where a position's reading is made. A walk from the
        // declaration to its fields is that same reading taken a second time, and the two part
        // wherever one of them reaches through a name the other stops at.
        //
        // And the fields have to be the record's own, because the rules below name them. Read
        // through a name to another declaration's fields, the fields would be one declaration's
        // and the rules another's, and every field would be chosen against rules that name
        // nothing it has.
        Type position = Type.ref(record);
        if (expanding.contains(record)
                || TypeOps.outermost(position, ruleSource.inners()) != null
                || !(TypeView.shapeOf(position, ruleSource.inners(), ruleSource.symbols(),
                        ruleSource.kinds(), ruleSource.sums())
                        instanceof Shape.Product(TypeSymbol _,
                        SequencedMap<String, Type> fields))) {
            return FieldsChosen.NONE;
        }
        if (fields.isEmpty()) {
            // A unit has no fields to compose, and is named rather than built.
            return FieldsChosen.NONE;
        }
        Set<TypeSymbol> inside = new LinkedHashSet<>(expanding);
        inside.add(record);
        // What is settled is kept once for everything built under the outermost record, by where
        // it stands, and every value's rules are asked about it as they name those places. Kept
        // beside each record's rules, a number chosen in an inner record would be one the rules
        // outside it were never told.
        RulesAround within = around.sharing();
        within.forgetUnder(within.here());
        FieldDomains rules = FieldDomains.of(rulesOn, reading);
        // The record's rules, read once. Each field is then chosen against this with the fields
        // before it settled into it, which is what a settling states — a reading per settled field
        // would be paying for every clause again to arrive where the first one already is.
        FieldDomains.Composing left = rules.composing(Map.of());
        // The places the record's own rules read, which a value built at one of its fields is held
        // to where they are under the field.
        PlacesTheRulesRead read = PlacesTheRulesRead.of(Type.ref(rulesOn), ruleSource);
        SequencedMap<String, FixtureTemplate> chosen = new LinkedHashMap<>();
        if (!fields.keySet().containsAll(given.keySet())
                || !fields.keySet().containsAll(held.keySet())) {
            return FieldsChosen.NONE;
        }
        CompositionShortfall met = CompositionShortfall.NONE;
        // What the rules ask of each map beside the other fields, and so which fields have to be
        // chosen before the map that is asked for an entry under them.
        Map<String, List<EntryHeld.Requirement>> asked = new LinkedHashMap<>();
        for (String name : fields.keySet()) {
            List<EntryHeld.Requirement> requirements = rules.entriesHeldAt(RuleKey.of(name));
            if (!requirements.isEmpty()) {
                asked.put(name, requirements);
            }
        }
        List<String> order = new ArrayList<>(fields.keySet());
        order.sort(Comparator.comparingInt(name -> standsAsAKeyOf(name, asked) ? 0 : 1));
        Map<String, Set<String>> apart = keysThatMustDiffer(asked);
        Map<String, FixtureTemplate> chosenByName = new LinkedHashMap<>();
        for (String name : order) {
            Map.Entry<String, Type> field = Map.entry(name, fields.get(name));
            FixtureTemplate at = given.get(field.getKey());
            if (at == null) {
                FieldDomains.ConstructionLimits limits = left.at(RuleKey.of(field.getKey()))
                        .meet(within.at(field.getKey()))
                        .meet(heldTo(held.get(field.getKey())));
                // A field the rules leave no value at leaves the record none, which is settled
                // here and said as itself: nothing was built and nothing was tried.
                if (limits.leavesNothing()) {
                    within.forgetUnder(within.here());
                    return new FieldsChosen(null, met, true);
                }
                // What every value around this one, and this one's own rules, say of the places
                // under the field: the value there is built held to them as well as to its own
                // declaration's rules, by whatever builds a value of its type.
                RulesAround inner = within.aroundTheField(read, rules, field.getKey());
                // A map asked for an entry under a key already chosen is built holding it.
                Proposals holding = asked.containsKey(name)
                        ? holdingTheEntriesAskedFor(field.getValue(), asked.get(name),
                                chosenByName, limits, reading)
                        : null;
                List<SidesBalanced.Requirement> sides = rules.sidesBalancedAt(RuleKey.of(name));
                if (holding == null && !sides.isEmpty()) {
                    holding = balancedSides(field.getValue(), sides.getFirst(), limits, reading);
                }
                // The first value, with what was met in front of it: a field's later values are
                // values nothing here takes. Except past the values already chosen for the keys
                // this one may not be: two keys asked for two numbers are two keys, and a value
                // the first took is the next one's to pass over.
                Set<String> taken = new LinkedHashSet<>();
                apart.getOrDefault(name, Set.of()).forEach(other -> {
                    if (chosenByName.containsKey(other)) {
                        taken.add(chosenByName.get(other).text());
                    }
                });
                Proposals stands = holding != null ? holding.firstOf(1)
                        : !taken.isEmpty() ? Witnesses.distinctValuesOf(field.getValue(),
                                taken.size() + 1, limits.held(), limits.admits(), reading, inside)
                        : Witnesses.firstWhatThePlaceAdmits(
                        field.getValue(), limits, reading, inside, inner,
                        () -> representativesHolding(field.getValue(), reading, limits, inside,
                                inner))
                        .firstOf(1);
                met = met.and(stands.met());
                at = stands.values().stream().filter(each -> !taken.contains(each.text()))
                        .findFirst().orElse(null);
                if (at == null) {
                    within.forgetUnder(within.here());
                    return new FieldsChosen(null, met);
                }
            }
            chosenByName.put(field.getKey(), at);
            // Settled, and the rules read again with it in them. A field chosen against the rules as
            // they stand before anything is settled is chosen against `a < b` with `a` still open,
            // which leaves `b` its whole range and takes the bottom of it. Every number the value
            // writes, wherever in it, from the value chosen and not from what was tried on the way
            // to it.
            Counts.writtenUnder(within.here().then(field.getKey()), at.value(), within::settle);
            left = rules.composing(FieldDomains.atValues(within.settledUnder(within.here())));
        }
        // Written in the order the record declares them, whichever order they were chosen in.
        for (String name : fields.keySet()) {
            chosen.put(name, chosenByName.get(name));
        }
        return new FieldsChosen(chosen, met);
    }

    /** What a search leaves a field besides the rules, as the limits a field is chosen in: none
     *  where it holds the field to nothing. */
    private static FieldDomains.ConstructionLimits heldTo(NumericDomain.Bounds bounds) {
        return bounds == null ? FieldDomains.ConstructionLimits.NONE
                : FieldDomains.ConstructionLimits.of(bounds, null, null,
                        FieldDomains.ConstructionLimits.NONE.admits(), HeldClass.NONE);
    }

    /**
     * For each field standing as a key, the fields standing as keys it may not be the same value
     * as: those asked for another number under the same map.
     */
    private static Map<String, Set<String>> keysThatMustDiffer(
            Map<String, List<EntryHeld.Requirement>> asked) {
        Map<String, Set<String>> apart = new LinkedHashMap<>();
        for (List<EntryHeld.Requirement> inOneMap : asked.values()) {
            for (EntryHeld.Requirement one : inOneMap) {
                for (EntryHeld.Requirement other : inOneMap) {
                    if (one.valueIs() != null && other.valueIs() != null
                            && one.valueIs().compareTo(other.valueIs()) != 0) {
                        apart.computeIfAbsent(one.key().steps().getFirst(),
                                _ -> new LinkedHashSet<>()).add(other.key().steps().getFirst());
                    }
                }
            }
        }
        return apart;
    }

    /** Whether {@code field} is the key some map is asked for an entry under. */
    private static boolean standsAsAKeyOf(String field,
                                          Map<String, List<EntryHeld.Requirement>> asked) {
        return asked.values().stream().flatMap(List::stream)
                .anyMatch(each -> each.key().steps().equals(List.of(field)));
    }

    /**
     * A map of {@code type} holding every entry the rules ask of it, under the keys already
     * chosen, or nothing where no such map can be written.
     *
     * <p>Never a fallback to choosing the field as any other: the rules asking these entries were
     * read as kept by this ({@link EntryHeld#writtenOn} is the one list both go by), and a map
     * chosen without them is a map the rule refuses. Nothing is what it answers for a map the
     * position does not declare, a key not chosen, a number the position cannot write, and two
     * numbers asked of one key.
     */
    private static Proposals holdingTheEntriesAskedFor(Type type,
                                                       List<EntryHeld.Requirement> asked,
                                                       Map<String, FixtureTemplate> chosen,
                                                       FieldDomains.ConstructionLimits limits,
                                                       RuleReadingContext reading) {
        RuleReadingSource source = reading.source();
        TypeView view = TypeView.of(type, source.inners(), source.symbols(), source.kinds(),
                source.sums());
        if (!(view.shape() instanceof Shape.Mapping map)) {
            return Proposals.NONE;
        }
        List<Witnesses.Filed> entries = new ArrayList<>();
        for (EntryHeld.Requirement each : asked) {
            FixtureTemplate key = chosen.get(each.key().steps().getFirst());
            // A number the value's type admits and can be written as: a value written under a name
            // is a value of the type only if its rules let it be.
            FixtureTemplate value = each.valueIs() == null
                    || !EntryHeld.valueTypeAdmits(map.value(), each.valueIs(), null, reading)
                    ? null
                    : writtenNumberAt(map.value(), each.valueIs(), reading);
            if (key == null || (each.valueIs() != null && value == null)) {
                return Proposals.NONE;
            }
            entries.add(new Witnesses.Filed(key, value));
        }
        Proposals made = Witnesses.holdingEntries(map, entries,
                heldRange(type, reading, limits.held()), reading);
        List<FixtureTemplate> worn = new ArrayList<>();
        for (FixtureTemplate each : made.values()) {
            FixtureTemplate under = WornNames.under(view.wrappers(), each, source);
            if (under == null) {
                return Proposals.NONE.meeting(made.met());
            }
            worn.add(under);
        }
        return Proposals.of(worn).meeting(made.met());
    }

    /**
     * A list of {@code type} whose elements at the two cases the rule names add up to one another,
     * or nothing where no such list can be written.
     *
     * <p>At least as many elements as the rules require, and at least two, split between the two
     * cases: the fewest that the numbers balance, walked up from the least the rules ask for. The
     * numbers they add are numbers the element's own rules admit ({@link #balancingAmounts}), so
     * every element is one its type allows and the totals are equal because the numbers were found
     * to make them so.
     *
     * <p>Never a fallback to choosing the field as any other: the rule asking the sides to balance
     * was read as kept by this ({@link SidesBalanced#writtenOn} is the one list both go by), and a
     * list chosen without it is a list the rule refuses. Nothing is what it answers for an element
     * that is no record, numbers the element admits that balance no count it walks, a list also
     * kept apart, and a count past what a proposal may hold. It is an answer about what this
     * builds and not about the type: a list kept apart as well, or a count past the sizes walked,
     * may exist, and the figures that ended the walk travel with the nothing.
     */
    private static Proposals balancedSides(Type type, SidesBalanced.Requirement rule,
                                           FieldDomains.ConstructionLimits limits,
                                           RuleReadingContext reading) {
        RuleReadingSource source = reading.source();
        TypeView view = TypeView.of(type, source.inners(), source.symbols(), source.kinds(),
                source.sums());
        if (!(view.shape() instanceof Shape.Sequence(Shape.Sequence.Kind kind, Type element))
                || kind != Shape.Sequence.Kind.LIST) {
            return Proposals.NONE;
        }
        TypeView elementView = TypeView.of(element, source.inners(), source.symbols(),
                source.kinds(), source.sums());
        if (!(elementView.shape() instanceof Shape.Product product)
                || !(product.name() instanceof TypeSymbol.AtModule record)
                || !product.fields().containsKey(rule.field())
                || !product.fields().containsKey(rule.number().getFirst())
                || !(source.symbols().scope().reach(rule.one())
                        instanceof TypeReachName.Written one)
                || !(source.symbols().scope().reach(rule.other())
                        instanceof TypeReachName.Written other)) {
            return Proposals.NONE;
        }
        // A list whose elements are also held apart is a list this does not build: the elements it
        // makes differ in their side and their amount and nothing else, and nothing here keeps
        // them apart in the rest. A list that is both exists wherever its amounts allow, so this is
        // a combination left unbuilt and not a statement that there is none.
        if (limits.held() != null && !limits.held().keptApart().isEmpty()) {
            return Proposals.NONE;
        }
        DeclaredBounds.CountRange room = heldRange(type, reading, limits.held());
        int first = Math.max(2, room.least());
        if (first > room.most()) {
            return Proposals.NONE;
        }
        Type numberType = product.fields().get(rule.number().getFirst());
        TypeSymbol.AtModule rulesOn = rulesOver(elementView.wrappers(), record, source);
        // The numbers the element's own rules admit there, as the position offers them, and the
        // sides made up of them. Nothing is chosen beside the rules: a list of numbers the type
        // does not admit is not the list the rule asks for, whatever the totals come to.
        FieldDomains.ConstructionLimits admitted = FieldDomains.of(rulesOn, reading)
                .composing(Map.of()).at(RuleKey.of(rule.number().getFirst()));
        List<FixtureTemplate> numbers = admittedNumbers(numberType, admitted, reading);
        // The count the rules ask for at least is where the walk starts and not the only count:
        // numbers that balance four elements two against two do not balance three, and the list
        // of four is as much a list the rules allow.
        CompositionBudget past = Witnesses.pastTheElements(first);
        if (past != null) {
            return Proposals.NONE.meeting(CompositionShortfall.of(List.of(past)));
        }
        int walked = CompositionBudget.ELEMENTS_A_COUNT_IS_COMPOSED_WITH.maximum();
        int held = CompositionBudget.ELEMENTS_A_PROPOSAL_HOLDS.maximum();
        int last = (int) Math.min(Math.min(room.most(), held), (long) first + walked - 1);
        Walk walk = balancedSplit(numbers, first, last);
        Split split = walk.split();
        if (split == null) {
            // Nothing among the sizes walked, which says the walk ended and not that no size is
            // left: past the last one there may be a list the figure did not reach. And a side
            // made of a number repeated has not been searched.
            List<CompositionBudget> met = new ArrayList<>();
            if (walk.reduced()) {
                met.add(CompositionBudget.ELEMENTS_A_SIDE_IS_SEARCHED_OVER);
            }
            // Only the numbers of the type nearest its ends were balanced from, unless the type
            // names all it admits and they are no more than that.
            FieldDomains.ConstructionLimits.ValuesNamed named = admitted.valuesNamed();
            if (!named.areTheValues()
                    || named.values().size() > CompositionBudget.NUMBERS_A_SIDE_IS_BALANCED_FROM
                            .maximum()) {
                met.add(CompositionBudget.NUMBERS_A_SIDE_IS_BALANCED_FROM);
            }
            if (last < room.most()) {
                met.add(last < held ? CompositionBudget.ELEMENTS_A_COUNT_IS_COMPOSED_WITH
                        : CompositionBudget.ELEMENTS_A_PROPOSAL_HOLDS);
            }
            return met.isEmpty() ? Proposals.NONE
                    : Proposals.NONE.meeting(CompositionShortfall.of(met));
        }
        int count = split.count();
        int onOne = split.onOne();
        List<FixtureTemplate> amounts = split.amounts();
        List<FixtureTemplate> elements = new ArrayList<>();
        for (int i = 0; i < count; i++) {
            boolean atOne = i < onOne;
            FixtureTemplate amount = amounts.get(i);
            Proposals composed = amount == null ? Proposals.NONE
                    : composed(record, rulesOn, reading, Set.of(),
                            Map.of(rule.field(), FixtureTemplate.unitCase(atOne ? one : other),
                                    rule.number().getFirst(), amount),
                            RulesAround.NONE);
            FixtureTemplate each = composed.isEmpty() ? null
                    : WornNames.under(elementView.wrappers(), composed.values().getFirst(), source);
            if (each == null) {
                return Proposals.NONE;
            }
            elements.add(each);
        }
        FixtureTemplate list = WornNames.under(view.wrappers(),
                FixtureTemplate.collection(elements), source);
        return Proposals.ofNullable(list);
    }

    /**
     * Numbers a position admits, written as values of its type: those the type offers, and whole
     * numbers from the near end of its range, each one the range holds and the set of values it is
     * held to has.
     *
     * <p>Asked of both, because neither is the whole of what a position admits. The type offers few
     * numbers — the ends of its range, and a last one of its own that its rules may refuse — and the
     * range says where numbers are and not which of them the rules leave, where the rules leave a
     * set.
     */
    private static List<FixtureTemplate> admittedNumbers(
            Type type, FieldDomains.ConstructionLimits limits, RuleReadingContext reading) {
        ValueSet held = limits.valuesNamed().asASet();
        List<FixtureTemplate> out = new ArrayList<>();
        Set<String> seen = new LinkedHashSet<>();
        List<FixtureTemplate> offered = new ArrayList<>(Witnesses.distinctValuesOf(type,
                CompositionBudget.NUMBERS_A_SIDE_IS_BALANCED_FROM.maximum(), limits.held(),
                limits.admits(), reading, Set.of()).values());
        for (BigInteger whole : wholeNumbersNear(limits.values(),
                CompositionBudget.NUMBERS_A_SIDE_IS_BALANCED_FROM.maximum())) {
            FixtureTemplate written = writtenNumberAt(type, new BigDecimal(whole), reading);
            if (written != null) {
                offered.add(written);
            }
        }
        // The figure bounds the numbers balanced from, which is what the two walks above add up to
        // once the ones the position refuses and the repeats are gone, and not either walk alone:
        // the type's own first, then the whole numbers from the end nearest nought.
        int most = CompositionBudget.NUMBERS_A_SIDE_IS_BALANCED_FROM.maximum();
        for (FixtureTemplate each : offered) {
            if (out.size() >= most) {
                break;
            }
            if (Counts.writtenIn(each.value()) instanceof Count count
                    && (limits.values() == null || limits.values().admits(count.exactly()))
                    && held.has(Value.number(count.at())) && seen.add(count.exactly().key())) {
                out.add(each);
            }
        }
        return out;
    }

    /**
     * Whole numbers from the end of {@code range} nearest to nought, as many as asked for: upward
     * from its floor, downward from its ceiling where it has no floor, and from one upward where it
     * has neither.
     */
    private static List<BigInteger> wholeNumbersNear(NumericDomain.Bounds range, int many) {
        List<BigInteger> out = new ArrayList<>();
        if (range != null && range.min() != null) {
            ExactRatio low = Count.number(range.min().at()).exactly();
            if (low.ceiling() instanceof ExactAnswer.Held<BigInteger>(BigInteger first)) {
                for (int i = 0; i < many; i++) {
                    out.add(first.add(BigInteger.valueOf(i)));
                }
            }
        } else if (range != null && range.max() != null) {
            ExactRatio high = Count.number(range.max().at()).exactly();
            if (high.floor() instanceof ExactAnswer.Held<BigInteger>(BigInteger last)) {
                for (int i = 0; i < many; i++) {
                    out.add(last.subtract(BigInteger.valueOf(i)));
                }
            }
        } else {
            for (int i = 1; i <= many; i++) {
                out.add(BigInteger.valueOf(i));
            }
        }
        return out;
    }

    /** A count of elements, how many of them are at the first case, and the amounts they add. */
    private record Split(int count, int onOne, List<FixtureTemplate> amounts) {}

    /**
     * What walking the counts found: the split, or null, and whether a side was past the elements
     * a side is searched over, which leaves what was not found as not found by that search.
     */
    private record Walk(Split split, boolean reduced) {}

    /**
     * The first count from {@code first} to {@code last} that {@code numbers} balance, and the
     * split of it between the two cases that does — the sides nearest to equal in size first.
     *
     * <p>A side of more elements than the figure is searched over is made of one number repeated,
     * which finds the balances that need one number to a side and no others; the walk says it was
     * reduced to that whenever it came to such a side with more than one number to choose among.
     */
    private static Walk balancedSplit(List<FixtureTemplate> numbers, int first, int last) {
        int searched = CompositionBudget.ELEMENTS_A_SIDE_IS_SEARCHED_OVER.maximum();
        boolean reduced = false;
        for (int count = first; count <= last; count++) {
            for (int onOne = count / 2; onOne >= 1; onOne--) {
                reduced |= numbers.size() > 1 && count - onOne > searched;
                List<FixtureTemplate> amounts = balancingAmounts(numbers, onOne, count - onOne);
                if (amounts != null) {
                    return new Walk(new Split(count, onOne, amounts), reduced);
                }
            }
        }
        return new Walk(null, reduced);
    }

    /**
     * Numbers for the elements at the two sides, taken from {@code admitted}, whose totals are
     * equal — or null where those numbers make none.
     *
     * <p>Only numbers the type admits ({@link #admittedNumbers}), whatever they are: a side of
     * negative numbers balances as well as one of positive, and nought is a number like another. A total that is not nought is preferred, because a side of nothing
     * balances anything and shows nothing; it is a preference and not a condition, so a type that
     * admits nothing else still gets its list.
     *
     * <p>One number for every element of a side where that balances them, which any count of
     * elements allows. Past that, for few enough elements, the numbers of each side are searched
     * for ones that add up alike; with more elements than that, and no number that balances them
     * one each, there is no list and none is offered.
     */
    private static List<FixtureTemplate> balancingAmounts(List<FixtureTemplate> admitted,
                                                          int onOne, int onOther) {
        List<FixtureTemplate> fixtures = new ArrayList<>();
        List<ExactRatio> numbers = new ArrayList<>();
        for (FixtureTemplate each : admitted) {
            if (Counts.writtenIn(each.value()) instanceof Count count) {
                fixtures.add(each);
                numbers.add(count.exactly());
            }
        }
        Map<String, int[]> oneSide = totals(numbers, onOne);
        Map<String, int[]> otherSide = onOne == onOther ? oneSide : totals(numbers, onOther);
        int[] one = null;
        int[] other = null;
        for (Map.Entry<String, int[]> each : oneSide.entrySet()) {
            int[] match = otherSide.get(each.getKey());
            if (match == null) {
                continue;
            }
            if (!each.getKey().equals(ExactRatio.ZERO.key())) {
                one = each.getValue();
                other = match;
                break;
            }
            // Nought only when nothing else balances.
            if (one == null) {
                one = each.getValue();
                other = match;
            }
        }
        if (one == null) {
            return null;
        }
        List<FixtureTemplate> out = new ArrayList<>();
        for (int at : one) {
            out.add(fixtures.get(at));
        }
        for (int at : other) {
            out.add(fixtures.get(at));
        }
        return out;
    }


    /**
     * Every total {@code count} of {@code numbers} can come to, by the total, each with numbers that
     * come to it.
     *
     * <p>One number for every element where the count is past what is searched, so that a side of
     * many elements is made of one number repeated, which is every total the count times a number
     * comes to. The search keeps one way to each total, and stops growing at a size no list needs.
     */
    private static Map<String, int[]> totals(List<ExactRatio> numbers, int count) {
        Map<String, int[]> out = new LinkedHashMap<>();
        if (count > CompositionBudget.ELEMENTS_A_SIDE_IS_SEARCHED_OVER.maximum()) {
            for (int at = 0; at < numbers.size(); at++) {
                ExactRatio total = numbers.get(at).times(ExactRatio.of(count)).orNull();
                if (total != null) {
                    int[] repeated = new int[count];
                    Arrays.fill(repeated, at);
                    out.putIfAbsent(total.key(), repeated);
                }
            }
            return out;
        }
        Map<String, int[]> reached = new LinkedHashMap<>();
        reached.put(ExactRatio.ZERO.key(), new int[0]);
        Map<String, ExactRatio> sums = new LinkedHashMap<>();
        sums.put(ExactRatio.ZERO.key(), ExactRatio.ZERO);
        for (int step = 0; step < count; step++) {
            Map<String, int[]> next = new LinkedHashMap<>();
            Map<String, ExactRatio> nextSums = new LinkedHashMap<>();
            for (Map.Entry<String, int[]> each : reached.entrySet()) {
                for (int at = 0; at < numbers.size(); at++) {
                    ExactRatio total = sums.get(each.getKey()).plus(numbers.get(at)).orNull();
                    if (total != null && !next.containsKey(total.key())) {
                        int[] picks = Arrays.copyOf(each.getValue(), step + 1);
                        picks[step] = at;
                        next.put(total.key(), picks);
                        nextSums.put(total.key(), total);
                    }
                }
            }
            reached = next;
            sums = nextSums;
        }
        return reached;
    }

    /** {@code number} written as a value of {@code type}, or null where the position holds no
     *  number of that kind or cannot name the names it wears. */
    private static FixtureTemplate writtenNumberAt(Type type, BigDecimal number,
                                                   RuleReadingContext reading) {
        RuleReadingSource source = reading.source();
        TypeView view = TypeView.of(type, source.inners(), source.symbols(), source.kinds(),
                source.sums());
        if (!(view.shape() instanceof Shape.Scalar(Type.Prim prim))) {
            return null;
        }
        FixtureTemplate written = switch (prim) {
            case DECIMAL -> FixtureTemplate.decimal(number);
            case INT -> ExactRatio.of(number).isWhole()
                    && ExactRatio.of(number).truncated()
                            instanceof ExactAnswer.Held<BigInteger>(BigInteger whole)
                    && whole.bitLength() < Long.SIZE
                    ? FixtureTemplate.integer(whole.longValue()) : null;
            default -> null;
        };
        return WornNames.under(view.wrappers(), written, source);
    }

    /**
     * The rules of the values a value being built sits inside, and where it sits.
     *
     * <p>What a value built inside another is held to besides its own declaration's rules, handed to
     * whatever builds a value of its type — which is the only builder there is, so the names the
     * value wears, the rules of a name wrapping a record and the cases a sum is built as are that
     * builder's, as for any value. A rule of {@code Holder} about {@code q.limit} names a field of
     * whatever case {@code q} is, and a case built on its own reads only its own rules: so every
     * value's rules out here come down, and a record built under them is built field by field held
     * to what each leaves the field ({@link #at}).
     *
     * <p>One state for everything built under the outermost record ({@link Shared}): the count of
     * records built afresh, and what has been settled so far by where it stands. A record built
     * here is built afresh rather than borrowed from the revision, and under nested sums the cases
     * tried multiply — so each is counted ({@link #reserve}) against the count the outermost record
     * began, and the figure stops the lot. And a number chosen anywhere in the value is told to
     * the rules of every value around it as they name its place ({@link #at}), so a rule relating
     * two fields of an inner record is asked about the second with the first in it.
     *
     * @param each   every value around, outermost first
     * @param here   where the value being built sits, relative to the places those values stand at
     * @param shared what is shared by everything built under the outermost record, or null where
     *               none has begun to be built
     */
    record RulesAround(List<Around> each, TermPath here, Shared shared) {

        /** Nothing around: a value built on its own, at a place named for nothing in particular. */
        static final RulesAround NONE = new RulesAround(List.of(), TermPath.of("value"), null);

        RulesAround {
            each = List.copyOf(each);
        }

        /**
         * One value's rules, and where that value stands relative to what is being built.
         *
         * <p>Places and not names. What a rule of that value calls a place under it is the
         * translation from a place to a name, which has one home ({@link RuleAddress#of}): the
         * fields on the way are names its rules write, and a case on the way is not.
         *
         * @param read  the places that value's rules read, which say whether one reads under a
         *              place ({@link PlacesTheRulesRead})
         * @param rules that value's rules, which are asked what is settled when a field is chosen
         * @param root  where that value stands
         */
        record Around(PlacesTheRulesRead read, FieldDomains rules, TermPath root) {}

        /**
         * What is shared by everything built under the outermost record: what is left of the one
         * count, and the numbers settled so far by where each stands.
         */
        static final class Shared {

            private int left = CompositionBudget.CASES_A_RULE_ABOVE_IS_PLANNED_UNDER.maximum();

            private final Map<TermPath, Count> settled = new LinkedHashMap<>();
        }

        /** This, with the state of the outermost record begun where nothing has begun it. */
        RulesAround sharing() {
            return shared != null ? this : new RulesAround(each, here, new Shared());
        }

        /** What every value around leaves the field {@code field} of the record being built, met. */
        FieldDomains.ConstructionLimits at(String field) {
            FieldDomains.ConstructionLimits out = FieldDomains.ConstructionLimits.NONE;
            for (Around one : each) {
                RuleAddress named = RuleAddress.of(one.root(), here.then(field));
                if (named != null) {
                    out = out.meet(one.rules()
                            .composing(FieldDomains.atValues(settledUnder(one.root())))
                            .at(named.key()));
                }
            }
            return out;
        }

        /** Whether a rule of some value around reads a place under the value being built. */
        boolean readAnything() {
            for (Around one : each) {
                RuleAddress at = RuleAddress.of(one.root(), here);
                if (at != null && one.read().readUnder(at.key())) {
                    return true;
                }
            }
            return false;
        }

        /** Whether the count has one left for another value built here. */
        boolean hasLeft() {
            return shared != null && shared.left > 0;
        }

        /**
         * Takes one from the count for a value about to be built here, or says there is none.
         * Taken before and not after, since what is built inside it asks the same count.
         */
        boolean reserve() {
            if (!hasLeft()) {
                return false;
            }
            shared.left--;
            return true;
        }

        /** Gives back the one {@link #reserve} took, for a value the rules left no room for. */
        void refund() {
            shared.left++;
        }

        /** Takes in that the number {@code count} stands at {@code path}. */
        void settle(TermPath path, Count count) {
            shared.settled.put(path, count);
        }

        /** What is settled under {@code root}, by the name a rule of the value there gives it. */
        Map<RuleKey, Count> settledUnder(TermPath root) {
            Map<RuleKey, Count> out = new LinkedHashMap<>();
            if (shared != null) {
                shared.settled.forEach((path, count) -> {
                    RuleAddress named = RuleAddress.of(root, path);
                    if (named != null) {
                        out.put(named.key(), count);
                    }
                });
            }
            return out;
        }

        /** Takes back what was settled under {@code root}: the value there is built afresh. */
        void forgetUnder(TermPath root) {
            if (shared != null) {
                shared.settled.keySet().removeIf(path -> RuleAddress.of(root, path) != null);
            }
        }

        /** These and a record's own rules, around the record's field {@code field}. */
        RulesAround aroundTheField(PlacesTheRulesRead read, FieldDomains rules, String field) {
            List<Around> out = new ArrayList<>(each);
            out.add(new Around(read, rules, here));
            return new RulesAround(out, here.then(field), shared);
        }
    }

    /** How many of whatever counts a value the rules on it require it to hold, read where the rules
     * are: {@link DeclaredBounds#leastCountOf}. Of the position as it was read, since how many a
     * value holds is what the rules of every name it wears say. */
    static int leastHeld(TypeView view, RuleReadingContext reading) {
        return DeclaredBounds.leastCountOf(view, reading);
    }

    /** The same, where the record the position sits in has a rule about it too. */
    static int leastHeld(TypeView view, RuleReadingContext reading, FieldDomains.Held held) {
        return DeclaredBounds.leastCountOf(view, reading, held);
    }

    /**
     * From how few to how many the rules let a value at the position hold, as one answer.
     *
     * <p><b>Both ends of one reading, and there is no reading of the cap alone.</b> A caller
     * deciding whether there is room for a value being placed needs the floor to know how many the
     * whole collection has to hold and the cap to know whether that many fit. Taken as two
     * readings, the two can be of different states of the row — which is how a floor settled where
     * the caller had fixed a field came to be compared with a cap read where it had not. So the
     * cap has no projection of its own here: a caller wanting it takes both and is holding one
     * answer.
     */
    static DeclaredBounds.CountRange heldRange(Type type, RuleReadingContext reading,
                                               FieldDomains.Held held) {
        return DeclaredBounds.countsHeld(type, reading, held);
    }

    /**
     * What the rules about the strings at {@code type} left out of the values offered there, or
     * nothing where every one of them reached the offer.
     *
     * <p>Why the values offered at a position are the ones they are, asked where none of them was
     * taken. A rule this could not read composed nothing, and neither did one whose machine cost
     * more than composing a value may spend, so what was offered came from the rules beside them —
     * and a search that had every one of those refused has not shown that the model refuses what it
     * states. It has shown that what it tried was refused, which is a different sentence and is the
     * one an author can act on.
     *
     * <p>Asked only where nothing was written: this reads the rules again and builds what they
     * leave, and a row that was composed has no reason to pay for that. A rule that could not be read is not an answer about the model either way — the values
     * it admits may be as many as anybody could want, and none of them was composed here.
     */
    static StringOfferShortfall notOffered(Type type, RuleReadingContext reading) {
        if (type == null) {
            return StringOfferShortfall.NONE;
        }
        TypeView view = TypeView.of(type, reading.source().inners(), reading.source().symbols(),
                        reading.source().kinds(), reading.source().sums());
        PatternsStated stated = patternsStatedOn(view, reading.source());
        RulesRead rules = rulesReadOn(stated, view, reading);
        return rules == null ? stated.unread()
                : reading.revision().settled(new WhatTheOfferIsShortOf(rules));
    }

    /**
     * The values the rules on {@code view} leave it able to hold, by index: each written under the
     * names the position wears, or null where it has no value at that index.
     *
     * <p>Asked where several values of one type are needed and they have to differ — the elements of a
     * set, the keys of a map. Counted from inside the range rather than from zero, because a second
     * value the type itself refuses would have the collection refused for its elements while saying
     * nothing about how many of them there are.
     *
     * <p>Stepped on the order the position's values are compared on, which is the one the rules were
     * read on ({@link DeclaredBounds#of(TypeView, RuleReadingContext)}) and the one the value is
     * written back from. A date steps by a day and a time of day by a second, as a whole number steps
     * by one: each is held on a grid, and what is beside a value on it is a value of the type. Between
     * two decimals there is no next value, so a dense order names the one value inside its range and
     * no more.
     *
     * <p>Away from the end the range has ({@link #stepped}).
     *
     * <p>The rules are read and the range entered once, here, and each index is a step from there. A
     * caller filling a collection asks for every index up to how many it holds, and none of what is
     * read depends on which.
     */
    static IntFunction<FixtureTemplate> valuesInside(TypeView view, RuleReadingContext reading) {
        DeclaredBounds.Range declared = countedOrder(view, reading);
        if (declared == null) {
            return index -> null;
        }
        Carrier carrier = declared.carrier();
        NumericDomain.Bounds range = TypeBounds.admissible(declared, null);
        Place from = inside(range, carrier, reading.today());
        if (from == null) {
            return index -> null;
        }
        RuleReadingSource source = reading.source();
        if (carrier.spacing() != Granularity.DISCRETE) {
            FixtureTemplate only = standing(view, carrier, from, source);
            return index -> index == 0 ? only : null;
        }
        return index -> {
            Place at = stepped(range, carrier, from, index, carrier.usualPlace(reading.today()));
            return at == null ? null : standing(view, carrier, at, source);
        };
    }

    /**
     * What the rules a position's own value is stepped on were read on, or null where its value has
     * no count to step.
     *
     * <p>A value of its own that counts: a number, a date, a time, a moment. Not a string, which is
     * ordered and has no count under it, and not an enumeration, whose cases are what the position
     * divides into and are offered as that. Asked once, here, by every reader that steps a value, so
     * which values step is not decided twice.
     */
    private static DeclaredBounds.Range countedOrder(TypeView view, RuleReadingContext reading) {
        if (!(view.shape() instanceof Shape.Scalar)) {
            return null;
        }
        DeclaredBounds.Range declared = DeclaredBounds.of(view, reading);
        return declared != null && declared.carrier().counts() ? declared : null;
    }

    /**
     * The count {@code index} steps from {@code from} on a discrete carrier, away from the one end
     * {@code range} has, or null where the carrier or the range holds nothing there.
     *
     * <p>Away from that end because a range bounded only above is entered at its end, and a step up
     * from there is a value the rules refuse. On the carrier's grid because a step past the end of
     * what the carrier holds — the second after the last of the day — is no value.
     *
     * <p>And outward from {@code from} where it is where the number is usually near, in a range left
     * open on a side ({@link Carrier#aPlaceInside}): the {@code index}th place of the range taking
     * the one above before the one below at each step out, as every outward walk here does. Stepped
     * one way from there, a range whose far end is before today would hold today's nearest date and
     * nothing else.
     */
    private static Place stepped(NumericDomain.Bounds range, Carrier carrier, Place from,
                                 int index, UsualPlace usual) {
        Count origin = Count.number(from);
        if (usual instanceof UsualPlace.Near near
                && near.leftOpenIn(range == null ? null : range.min(),
                        range == null ? null : range.max())) {
            int reached = 0;
            for (long away = 0; ; away++) {
                boolean inside = false;
                for (Count each : away == 0 ? List.of(origin)
                        : Arrays.asList(origin.plus(away), origin.minus(away))) {
                    Place at = each == null ? null : carrier.onTheGrid(each);
                    if (at != null && holdsCount(range, at)) {
                        inside = true;
                        if (reached++ == index) {
                            return at;
                        }
                    }
                }
                // A range of a discrete carrier holds every place between two it holds, so one
                // past which neither side holds a place is one past which none does.
                if (!inside) {
                    return null;
                }
            }
        }
        boolean downwards = range != null && range.min() == null && range.max() != null;
        Place at = carrier.onTheGrid(downwards ? origin.minus(index) : origin.plus(index));
        return at != null && holdsCount(range, at) ? at : null;
    }

    /**
     * The same, with what a floor asks for offered ahead of it.
     *
     * <p>Both, and the floor first. Each is what one rule was read to produce and which of them the
     * whole of the rules admits is the decoder's answer, so neither withdraws the other — the same
     * reading {@link #representativesOf(TypeView, RuleReadingContext, NumericDomain.Bounds,
     * java.util.Set)} makes of a position whose own rules give it a floor,
     * made here of one whose floor is its record's. What the order decides is not which is right:
     * the search over a
     * row's positions is bounded, so a position offering the value that holds nothing first spends
     * an assignment on a value the rule refuses, and rows at positions the rule has nothing to do
     * with are what runs out.
     */
    static Proposals representativesHolding(Type type, RuleReadingContext reading,
                                            FieldDomains.ConstructionLimits limits) {
        return representativesHolding(type, reading, limits, Set.of());
    }

    /** The same, of a position nothing here has read yet. */
    static Proposals representativesHolding(Type type, RuleReadingContext reading,
                                            FieldDomains.ConstructionLimits limits,
                                            Set<TypeSymbol> expanding) {
        return representativesHolding(type, reading, limits, expanding, RulesAround.NONE);
    }

    /** The same, of a value built inside others whose rules name places in it
     *  ({@link RulesAround}). */
    static Proposals representativesHolding(Type type, RuleReadingContext reading,
                                            FieldDomains.ConstructionLimits limits,
                                            Set<TypeSymbol> expanding, RulesAround around) {
        return representativesHolding(TypeView.of(type, reading.source().inners(), reading.source().symbols(),
                        reading.source().kinds(), reading.source().sums()), reading,
                limits, expanding, around);
    }

    /** The same, with the names this is already inside the value of, for the same reason
     *  {@link #representativesOf} carries them. */
    static Proposals representativesHolding(TypeView view, RuleReadingContext reading,
                                            FieldDomains.ConstructionLimits limits,
                                            Set<TypeSymbol> expanding, RulesAround around) {
        FieldDomains.Held held = limits.held();
        RuleReadingSource ruleSource = reading.source();
        Proposals.Gathering candidates = Proposals.Gathering.distinct();
        // A position the rules leave nothing at is offered nothing: every value written there is
        // one they refuse.
        if (limits.leavesNothing()) {
            return candidates.done();
        }
        // A member of the class the value is held to, first: the values offered below are read off
        // where the value stops, and a value between the ends is of the class only by luck — the
        // first of a month offered for a position held to the first of each, and not whatever date
        // the order happens to start from.
        FixtureTemplate member = aMemberOf(view, reading, limits);
        if (member != null) {
            candidates.add(member);
        }
        // Under every name the position wears, because a floor read off the record says how much the
        // value holds and not what it is written as: a field of a newtype over a list takes a list
        // inside that newtype's own name.
        //
        // A name this module cannot write leaves no value to write, which is asked once of the
        // position rather than of each value built for it.
        if (WornNames.of(view.wrappers(), ruleSource) instanceof WornNames.Spelled spelled) {
            candidates.addAll(Witnesses.holding(view, leastHeld(view, reading, held),
                    ElementsKeptApart.heldBy(held), reading, expanding)
                    .map(bare -> RepresentativeSource.under(spelled.names(), bare)));
        }
        // Of each run the order leaves the value, lowest first: a value between the ends of the
        // first and the last is one every alternative refuses where it falls between two runs.
        for (NumericDomain.Bounds run : limits.runs()) {
            candidates.addAll(representativesOf(view, reading, run, expanding, around));
        }
        return candidates.done();
    }

    /**
     * The same, with a second value offered at a position whose values are counted — a number, a
     * date, a time.
     *
     * <p>One value is enough only where the rules that decide it are the rules the projection holds.
     * A disequality is a hole no range keeps, and a form that is neither an interval nor a difference
     * is not recorded at all — so the value a range gives up can be one those rules refuse, and a
     * position offering only that has nothing left to try.
     *
     * <p>Displaced and not invented. A whole number and a date have a next one; a decimal between
     * two ends has a midpoint, and where it has no second end it gets no second value, because an
     * epsilon is a value the type does not name. A candidate is a proposal the decoder answers — it
     * carries no promise that the value is writable, which is what separates this from a boundary a
     * person is asked to write.
     *
     * <p>With what building the ordinary offer met, which the second value does nothing to change.
     */
    static Proposals displacedRepresentativesOf(Type type, RuleReadingContext reading,
                                                FieldDomains.ConstructionLimits limits) {
        // The position, read once and handed to everything below: what it ordinarily offers, what it
        // holds back, where its rules leave a number, and the names any of those go under.
        RuleReadingSource ruleSource = reading.source();
        TypeView view = TypeView.of(type, ruleSource.inners(), ruleSource.symbols(),
                ruleSource.kinds(), ruleSource.sums());
        NumericDomain.Bounds within = limits.values();
        Proposals ordinarily = representativesHolding(view, reading, limits, Set.of(),
                RulesAround.NONE);
        Proposals.Gathering base = Proposals.Gathering.distinct();
        base.addAll(ordinarily);
        // Nothing held back and nothing displaced where nothing can stand: both are values beside
        // the ones offered, and there are none.
        if (limits.leavesNothing()) {
            return base.done();
        }
        // What a position holds back for the product search's second pass is on offer here from the
        // start. This pass runs only where both of those have already failed, and a position keeping
        // a value from the last search there is a value nothing will ever be tried at.
        inReserve(view, reading, within, ordinarily.values()).forEach(base::add);
        // On the order the rules were read on, so a date is displaced by a day as a whole number is
        // by one, and only where a value of its own counts — the same values that step as elements.
        DeclaredBounds.Range declared = countedOrder(view, reading);
        if (declared == null) {
            return base.done();
        }
        Carrier carrier = declared.carrier();
        // Displaced inside the first run, where the first value was chosen: the ends around every
        // run hold the gaps between them, and a value displaced into one is no second value but
        // one every alternative refuses.
        NumericDomain.Bounds range = TypeBounds.admissible(declared, limits.runs().getFirst());
        Place step = displaced(range, carrier, reading.today());
        if (step == null) {
            return base.done();
        }
        FixtureTemplate value = standing(view, carrier, step, ruleSource);
        // Nothing to offer beside the first, either because the order has no value there or because
        // a name the position wears is one this module cannot write. One already on offer is left
        // out as every value is that is offered twice.
        if (value != null) {
            base.add(value);
        }
        return base.done();
    }

    /**
     * The member of the class {@code limits} holds the position to nearest the value standing for
     * where it stops ({@link Carrier#aPlaceInside}) — the lower end of a run a rule closed, or
     * where the order is usually near in one left open on a side — that the values the rules
     * admit there take in, written as the position writes it; or null where it is held to no class,
     * its order counts none, or the run holds no such member.
     *
     * <p>The members looked at are as many as can all be values the admitted set keeps out, and one
     * more: a set naming finitely many values it refuses refuses at most that many members, so one
     * past them is a member it takes. Any other set refuses no member by a value it names, and the
     * first member is the one.
     */
    private static FixtureTemplate aMemberOf(TypeView view, RuleReadingContext reading,
                                             FieldDomains.ConstructionLimits limits) {
        HeldClass held = limits.heldTo();
        DeclaredBounds.Range declared = held instanceof HeldClass.None ? null
                : countedOrder(view, reading);
        if (declared == null || !held.countsOn(declared.carrier())) {
            return null;
        }
        FieldDomains.ConstructionLimits.ValuesNamed named = limits.valuesNamed();
        ValueSet admits = named.asASet();
        Carrier carrier = declared.carrier();
        // In each run the value may be in, since a member between two of them is one every
        // alternative refuses.
        for (NumericDomain.Bounds within : limits.runs()) {
            NumericDomain.Bounds run = TypeBounds.admissible(declared, within);
            ClassMembers members = held.standingIn(run, carrier,
                    carrier.usualPlace(reading.today()), named.keptOut() + 1);
            for (BigInteger each : members.values()) {
                Place at = new Count(new BigDecimal(each));
                if (declared.carrier().admitted(admits, at)) {
                    return standing(view, declared.carrier(), at, reading.source());
                }
            }
        }
        return null;
    }

    /** A second count of a range, or null where the carrier has none to give. */
    private static Place displaced(NumericDomain.Bounds range, Carrier carrier, Today today) {
        Place from = inside(range, carrier, today);
        if (from == null) {
            return null;
        }
        Endpoint min = range == null ? null : range.min();
        Endpoint max = range == null ? null : range.max();
        if (carrier.spacing() == Granularity.DENSE) {
            // No smallest step, so the only second count a range names is one inside both its ends —
            // and the one already on offer is that count where the range is open below.
            return min == null || max == null || !min.inclusive() ? null
                    : carrier.somethingInside(Endpoint.exclusive(min.at()), max, Towards.ABOVE,
                            UsualPlace.NONE);
        }
        // The step an element of a collection takes after the first, so a position's second value and
        // a set's second element are one value.
        return stepped(range, carrier, from, 1, carrier.usualPlace(today));
    }

    /** Whether a range holds a count, with no range holding everything. */
    private static boolean holdsCount(NumericDomain.Bounds range, Place at) {
        return range == null || range.admits(at);
    }

    /**
     * Up to {@code many} strings the rules on {@code type} admit, written under the names the
     * position wears, and none of them the same string twice.
     *
     * <p>Asked where several values of one type are needed and they have to differ — the elements of
     * a set, the keys of a map. The counterpart of {@link #valuesInside} over the strings, and it is
     * here for the same reason: a second value stepped off the first by the carrier alone is a value
     * the type's own rules may refuse, and a collection filled from those comes back as one every
     * value tried was refused at while the strings the rule admits are as many as anybody could want.
     *
     * <p><b>What the whole of the rules admits, which is not what {@link #whatAFormatAsksFor}
     * offers.</b> That one is a proposal per rule, put to the decoder one at a time, and a value
     * refused there costs a caller one candidate. These go inside a collection, where a value the
     * rules refuse takes the whole collection with it and no other element can make up for it — so
     * the rules are met with each other first and what comes back is from the meet.
     *
     * <p>A rule this could not read is left out of the meet rather than stopping it, which widens
     * what is offered and never narrows it: these are proposals like any other and the decoder
     * answers them. Empty where no rule about the strings was read at all — there the position has
     * nothing to say about which strings, and what a value of one more is is the carrier's to step.
     */
    static List<FixtureTemplate> admittedStrings(Type type, RuleReadingContext reading, int many) {
        if (type == null) {
            return List.of();
        }
        RuleReadingSource ruleSource = reading.source();
        TypeView view = TypeView.of(type, ruleSource.inners(), ruleSource.symbols(),
                ruleSource.kinds(), ruleSource.sums());
        List<FixtureTemplate> out = new ArrayList<>();
        for (String each : textsTheRulesAdmit(view, reading, many)) {
            FixtureTemplate written =
                    WornNames.under(view.wrappers(), FixtureTemplate.string(each), ruleSource);
            if (written == null) {
                return List.of();   // a name this module cannot write leaves no value to offer
            }
            out.add(written);
        }
        return List.copyOf(out);
    }

    /**
     * A string of exactly {@code size} characters the rules on {@code view} admit, or nothing where
     * they say nothing about its strings or leave none of that many.
     *
     * <p>For a caller that has a count to meet and the position's reading in hand. What a value of
     * a shape counting that many looks like is {@link Witnesses}'s, asked of the shape and shared
     * by every caller; which of those strings this position admits is the position's, and a caller
     * holding both offers this one first and that one after it. Kept apart because the two answer
     * different questions: whether a string of that length exists at all is a claim about strings,
     * and a reading of it that had consulted one type's format would be that claim taken from an
     * opinion about that type.
     */
    static List<FixtureTemplate> admittedStringOfSize(TypeView view, RuleReadingContext reading,
                                                      int size) {
        return admittedStringsOfSizes(view, reading, List.of(size));
    }

    /**
     * The same for each of {@code sizes}, in the order they are given.
     *
     * <p>The rules on {@code view} are read once for all of them: they are the same rules whatever
     * size is asked, and a caller walking several sizes would otherwise read them again for each.
     */
    static List<FixtureTemplate> admittedStringsOfSizes(TypeView view, RuleReadingContext reading,
                                                        Collection<Integer> sizes) {
        RulesRead rules = rulesReadOn(view, reading);
        if (rules == null) {
            return List.of();
        }
        List<FixtureTemplate> out = new ArrayList<>();
        for (int size : sizes) {
            if (size < 0) {
                continue;
            }
            // That many and no other is one more count the rules leave, met with the one they
            // wrote.
            DeclaredBounds.CountRange exactly = new DeclaredBounds.CountRange(
                    Math.max(rules.characters().least(), size),
                    Math.min(rules.characters().most(), size));
            for (String each : reading.revision().settled(
                    new StringsTheRulesAdmit(new RulesRead(rules.stated(), exactly), 1))) {
                out.add(FixtureTemplate.string(each));
            }
        }
        return List.copyOf(out);
    }

    /**
     * A value the whole of the rules on {@code view} admits, or nothing where fewer than two of them
     * say anything about its strings.
     *
     * <p>Written bare, because {@link #representativesOf} is what puts the names on. One and not
     * more: what a position offers is what a search walks, and a second value of the same set tells
     * a reader nothing the first did not — telling them apart is what a collection needs, and it
     * asks for as many as it holds ({@link #admittedStrings}).
     *
     * <p><b>Two, because one reading has nothing to be met with.</b> Where a single rule speaks of
     * the strings, what every rule admits is what that rule asked for, and that value is already
     * offered by whichever reading made it. Composed here as well it would be the same string
     * arrived at through a machine, and every position carrying a format would pay for one.
     */
    private static List<FixtureTemplate> whatEveryRuleAdmits(PatternsStated stated,
                                                             DeclaredBounds.CountRange characters,
                                                             RuleReadingContext reading) {
        // A rule counting the characters says which strings as much as a format does: it leaves out
        // every string of another length.
        if (stated.read().size() + (countsTheCharacters(characters) ? 1 : 0) < 2) {
            return List.of();
        }
        return reading.revision()
                .settled(new StringsTheRulesAdmit(new RulesRead(stated, characters), 1))
                .stream()
                .map(FixtureTemplate::string)
                .toList();
    }

    /** Up to {@code many} of the strings the rules on {@code view} admit, no two of them the
     *  same. */
    private static List<String> textsTheRulesAdmit(TypeView view, RuleReadingContext reading,
                                                   int many) {
        if (many <= 0) {
            return List.of();
        }
        RulesRead rules = rulesReadOn(view, reading);
        return rules == null ? List.of()
                : reading.revision().settled(new StringsTheRulesAdmit(rules, many));
    }

    /**
     * The machine of one pattern a rule states, and the string it offers a row, built once for the
     * revision.
     *
     * <p>The producer of both. A pattern's machine is settled by the pattern, so every question
     * that composes a value out of it — the value one rule asks for, what several rules meet in,
     * what the offer was short of — borrows it from here rather than building it again, and pays
     * nothing for it ({@link PatternPlan.Budget#OF_A_WITNESS}). What it may spend is the
     * allowance one pattern has ({@link PatternPlan.Budget#OF_A_PATTERN_FOR_A_WITNESS}), minted
     * here for it alone.
     *
     * <p><b>A pattern a rule states, and no other.</b> Running out of that allowance is said
     * under the rule, as a pattern an author can write smaller. A machine a question composes on
     * its way to a value — the strings of so many characters a count leaves — is nobody's rule, so
     * it is the question's to build and to pay for, and the type taken here is one only a rule's
     * reading hands out ({@link StringPredicates.StatedPattern}).
     *
     * <p>The string is worked out with the machine, because both are what a search asks of the
     * pattern from every settling it visits, and neither depends on where the search is.
     */
    record PatternForAWitness(StringPredicates.StatedPattern pattern)
            implements RevisionWork<PatternForAWitness.Made> {

        /** The refusal of a pattern's machine by {@code stopped}, as it is made under the allowance
         *  one pattern has: what a search that was kept from a value by it reports. */
        static PatternPlan.Refused refusedAt(Meter.Stopped stopped) {
            return new PatternPlan.Refused(PatternPlan.Budget.OF_A_PATTERN_FOR_A_WITNESS, stopped);
        }

        /** What building the pattern came to. */
        sealed interface Made {

            /**
             * The machine, and a string a source can carry that it accepts, or none where every
             * string it accepts is one nobody can paste.
             */
            record Built(Language language, Optional<String> written) implements Made {}

            /**
             * Building it ran past the allowance one pattern has, and which limit refused it.
             *
             * <p>About this pattern and nothing else, since the allowance was its own: what a
             * question that wanted it says is that this pattern gave nothing, and not that the
             * question ran out ({@link StringOfferShortfall.Why.PatternTooCostly}).
             */
            record NotBuilt(Meter.Stopped stopped) implements Made {}
        }

        @Override
        public Made workedOut(RevisionKnowledge revision) {
            Meter meter = PatternPlan.Budget.OF_A_PATTERN_FOR_A_WITNESS.meter();
            Language language = PatternPlan.of(pattern.meaning()).compile(meter);
            return language == null ? new Made.NotBuilt(meter.stoppedBy())
                    : new Made.Built(language, Optional.ofNullable(language.someWritten()));
        }
    }

    /**
     * Up to {@code many} of the strings the rules read at a position admit together, as work
     * settled by those rules.
     *
     * <p>One allowance for the whole of the question, which is what looking for these values may
     * cost: the meet and every string taken out of it are steps of one search, and a fresh figure
     * per step would be this spending as much as the number asked for. The machines of the rules'
     * patterns are borrowed ({@link PatternForAWitness}), so what it is spent on is what this
     * question makes: the meet, the strings the count leaves and their meet with it, the strings
     * taken out.
     *
     * <p>The revision's for the reason a pattern's machine is. What the meet comes to is read off
     * the rules and the count and nothing about where the search is, and a position carrying a
     * format and a count is asked about from every settling the search visits.
     */
    record StringsTheRulesAdmit(RulesRead rules, int many) implements RevisionWork<List<String>> {

        @Override
        public List<String> workedOut(RevisionKnowledge revision) {
            Meter meter = PatternPlan.Budget.OF_A_WITNESS.meter();
            Language left =
                    admittedBy(rules.stated(), rules.characters(), meter, revision).language();
            List<String> out = new ArrayList<>();
            while (left != null && out.size() < many) {
                String some = left.someWritten();
                if (some == null) {
                    break;   // nothing left in it that anybody could paste
                }
                out.add(some);
                // The strings left only where one more is wanted: taking one out is a machine of
                // its own, and the last one taken needs nothing after it.
                if (out.size() < many) {
                    left = left.without(List.of(some), meter);
                }
            }
            return List.copyOf(out);
        }
    }

    /**
     * What the rules on {@code view} leave its strings, so far as this compiler read them: what
     * they say of the strings, and how many characters one holds. Null where they leave every
     * string, where the type is no string, and where what they leave could not be worked out — a
     * rule not read refuses nothing here and is the decoder's to refuse by.
     *
     * <p>For a caller naming values along the strings' own order, which knows nothing of the type:
     * the least string there is comes first along it, and a rule on the characters is written to
     * refuse it.
     */
    static StringsTheRulesLeave stringsTheRulesLeave(TypeView view, RuleReadingContext reading) {
        if (!(view.shape() instanceof Shape.Scalar scalar) || scalar.prim() != Type.Prim.STRING) {
            return null;
        }
        // Each vocabulary read whether or not the other says anything: a run along the order is
        // a question about where a string lies, which stepping a character onto the last does not
        // answer, so the count is read here even where no pattern is stated.
        RulesRead rules = new RulesRead(patternsStatedOn(view, reading.source()),
                DeclaredBounds.countsHeld(view, reading, null));
        if (rules.stated().read().isEmpty() && !countsTheCharacters(rules.characters())) {
            return null;
        }
        Language leaves = reading.revision().settled(new StringsLeft(rules)).orElse(null);
        return leaves == null ? null : new StringsTheRulesLeave(rules, leaves, reading.revision());
    }

    /**
     * The strings the rules on a type leave, read once and asked of a string or of a run.
     *
     * @param rules    what the rules say of the strings and of how many characters they hold
     * @param leaves   the strings those leave
     * @param revision where what a run leaves is settled
     */
    record StringsTheRulesLeave(RulesRead rules, Language leaves, RevisionKnowledge revision) {

        /** Whether {@code text} is one of them. */
        boolean admits(String text) {
            return leaves.has(text);
        }

        /**
         * Up to {@code many} of them inside the run of the strings' own order from {@code low} to
         * {@code high}, each one somebody can write, shortest first; none where no such string
         * lies there or this compiler could not work out which do. A missing end is none.
         */
        List<String> inside(Endpoint low, Endpoint high, int many) {
            return many <= 0 ? List.of() : revision.settled(new StringsInsideARun(rules,
                    low == null ? null : low.at().key(), low != null && low.inclusive(),
                    high == null ? null : high.at().key(), high != null && high.inclusive(),
                    many));
        }
    }

    /**
     * The strings the rules read at a position leave, the count met with what the patterns say,
     * as work settled by those rules; empty where building them ran past the allowance.
     */
    record StringsLeft(RulesRead rules) implements RevisionWork<Optional<Language>> {

        @Override
        public Optional<Language> workedOut(RevisionKnowledge revision) {
            Meter meter = PatternPlan.Budget.OF_A_WITNESS.meter();
            CandidateStrings left = rules.stated().read().isEmpty()
                    ? withinTheCount(Language.EVERY_STRING, rules.characters(), meter,
                            rules.stated().unread())
                    : admittedBy(rules.stated(), rules.characters(), meter, revision);
            return Optional.ofNullable(left.language());
        }
    }

    /**
     * Up to {@code many} of the strings the rules read at a position leave inside one run of the
     * strings' own order, each somebody can write, as work settled by those rules and the run.
     *
     * @param low  the lower end of the run, or null where it has none
     * @param high the upper end of the run, or null where it has none
     */
    record StringsInsideARun(RulesRead rules, String low, boolean lowIn, String high,
                             boolean highIn, int many) implements RevisionWork<List<String>> {

        @Override
        public List<String> workedOut(RevisionKnowledge revision) {
            Language left = revision.settled(new StringsLeft(rules)).orElse(null);
            Meter meter = PatternPlan.Budget.OF_A_WITNESS.meter();
            if (left != null && high != null) {
                Language below = Language.before(high, meter);
                below = below == null || !highIn ? below : below.with(List.of(high), meter);
                left = below == null ? null : left.and(below, meter);
            }
            if (left != null && low != null) {
                Language below = Language.before(low, meter);
                Language from = below == null ? null : below.not(meter);
                from = from == null || lowIn ? from : from.without(List.of(low), meter);
                left = from == null ? null : left.and(from, meter);
            }
            List<String> out = new ArrayList<>();
            while (left != null && out.size() < many) {
                String some = left.someWritten();
                if (some == null) {
                    break;
                }
                out.add(some);
                if (out.size() < many) {
                    left = left.without(List.of(some), meter);
                }
            }
            return List.copyOf(out);
        }
    }

    /**
     * What the rules read at a position left out of what {@link StringsTheRulesAdmit} offers
     * there, as work settled by those rules.
     *
     * <p>The same meet built the same way, out of the same borrowed machines and under the same
     * allowance, so what this says ran out is what ran out when the values were looked for: built
     * any other way, a report could name a rule as too costly beside a value composed out of it.
     */
    record WhatTheOfferIsShortOf(RulesRead rules) implements RevisionWork<StringOfferShortfall> {

        @Override
        public StringOfferShortfall workedOut(RevisionKnowledge revision) {
            return admittedBy(rules.stated(), rules.characters(),
                    PatternPlan.Budget.OF_A_WITNESS.meter(), revision).shortfall();
        }
    }

    /**
     * What the rules at a position say about its strings, read to compose a value from: the
     * patterns and how many characters.
     *
     * <p>Everything the meet is worked out from, so it is what the work over it is keyed by. Which
     * rule each pattern was written as is part of it, because a shortfall names the rule.
     */
    private record RulesRead(PatternsStated stated, DeclaredBounds.CountRange characters) {}

    /**
     * What the rules on {@code view} say about its strings, or null where none of them says which
     * strings.
     *
     * <p><b>Both vocabularies the rules reach a string in.</b> Which strings is a predicate over
     * them; how many characters is a number, counted by the measure the type is written in
     * ({@link DeclaredBounds#countsHeld}) and read where numbers are read. A value has to clear
     * both, so a reader of one of them alone hands out a string the other refuses — a format met
     * with a floor gives the shortest string the format accepts, which is the one the floor was
     * written to exclude.
     *
     * <p>Every name the position wears, because a value wearing two names is held to the rules
     * written on either. Met rather than listed: what is wanted is a string the rules admit
     * together, and a string one of them admits is what {@link #whatAFormatAsksFor} already offers.
     *
     * <p><b>The count is read to narrow what was said about the strings, and never on its own.</b>
     * A position nothing says the strings of has nothing here to narrow: what one more of its
     * values is is a character on the end of the last ({@link Witnesses}), which is the count
     * answered where counts are answered. Answered here as well, every string a length rule leaves
     * would come from a machine built to say what stepping already says.
     */
    private static RulesRead rulesReadOn(TypeView view, RuleReadingContext reading) {
        return rulesReadOn(patternsStatedOn(view, reading.source()), view, reading);
    }

    /** The same, of patterns already read off {@code view}. */
    private static RulesRead rulesReadOn(PatternsStated stated, TypeView view,
                                         RuleReadingContext reading) {
        // The count narrows what was said about the strings and is not read where nothing was said:
        // there is nothing for it to narrow, and what one more value of such a position is is a
        // character on the end of the last. Read before the patterns are looked at, every position
        // whose rules say nothing about its strings pays for a reading of its counts.
        return stated.read().isEmpty() ? null
                : new RulesRead(stated, DeclaredBounds.countsHeld(view, reading, null));
    }

    /**
     * Strings to offer at a position, and what the rules about its strings left out of them.
     *
     * <p><b>Not what the position admits.</b> What the rules admit is a reading of the position and
     * has an owner; this is a set to take a value out of and paste into a row, worked out of the
     * rules that were read and no further. Where {@link #shortfall} holds anything, the strings are
     * wider than the model's — every rule missing from the meet is one that may still refuse what
     * comes out of it, which is the decoder's answer and not this one's.
     *
     * <p>So a caller offering values takes {@link #language} and a caller saying what the offer was
     * short of takes {@link #shortfall}, and neither is the other's absence. Nothing to paste is an
     * ordinary answer and says nothing about a rule; a rule this compiler could not read is a fact
     * about the rule, and it is here as itself rather than as the absence it also causes.
     *
     * @param language the strings to draw a value from, or null where there is no string to draw
     * @param shortfall what the rules about the strings left out of what can be drawn from here
     */
    private record CandidateStrings(Language language, StringOfferShortfall shortfall) {}

    /**
     * The patterns the rules on {@code view} state about its strings, innermost name first.
     *
     * <p>Read without building anything. Which rules speak of the strings is what the clauses say;
     * what each of them admits is a machine, and a reader that wants one value from each, another
     * that wants the meet, and a third that only asks how many there are would each be paying for
     * every machine to find out.
     *
     * <p>Read off the clauses the checker typed, which is where a pattern is the meaning the checker
     * settled ({@link StringPredicates#statedOn}). The parts are the ones the author wrote, in the
     * order the author wrote them ({@link DeclaredClauses}); what each of them says comes from the
     * declaration that wrote it. Read again off the written tree, a pattern built out of a value of
     * the module came back as text nothing worked out, and the position was offered {@code "x"}.
     *
     * <p>Asked of what the predicate means and not of what the decoder is told. The two are
     * different questions: a constraint is what a generated class declares to the runtime, which is
     * a format and nothing else, and this is which strings the rule admits — asked through the
     * constraint, every predicate the decoder has no word for stated nothing, and a position an
     * author had written a rule for was offered {@code "x"} and refused.
     *
     * <p><b>And which of them this could not read, kept beside the ones it could.</b> A rule read
     * no further states no pattern to compose from, and dropping it there leaves the two apart only
     * until somebody asks why nothing was composed: the values then come from the rules that were
     * read, and a search that refuses all of them has not shown that the rules refuse them. So what
     * was read and what stopped the rest are one answer, and a caller offering values takes the
     * first while a caller saying what the offer was short of takes the second.
     */
    private static PatternsStated patternsStatedOn(TypeView view,
                                                   RuleReadingSource ruleSource) {
        if (!(view.shape() instanceof Shape.Scalar scalar) || scalar.prim() != Type.Prim.STRING) {
            return PatternsStated.NONE;
        }
        List<DeclaredClauses.OnAName> written = DeclaredClauses.of(view.wrappers(), ruleSource);
        List<Stated> read = new ArrayList<>();
        List<StringOfferShortfall.NotOffered> unread = new ArrayList<>();
        for (int name = written.size() - 1; name >= 0; name--) {
            // A name the language declares writes no clause, so it has nothing to say here.
            if (!(written.get(name).worn() instanceof TypeSymbol.AtModule named)) {
                continue;
            }
            StringPredicates.StatedOn stated = StringPredicates.statedOn(named, ruleSource);
            for (DeclaredClauses.Conjunct each : written.get(name).conjuncts()) {
                // A clause the checker has no form for says nothing anybody worked out about the
                // strings, which is a rule not read rather than a rule about something else — said
                // in the reason the reading of the position has for it, and not decided here.
                BlockReason.RuleOfferShortfallReason notTyped = stated.whyNotTyped(each.part());
                if (notTyped != null) {
                    unread.add(StringOfferShortfall.NotOffered.ofARuleNotRead(
                            each.part(), notTyped));
                    continue;
                }
                switch (stated.of(each.part())) {
                    case StringPredicates.Reading.Accepting _ ->
                            read.add(new Stated(each.part(), stated.patternOf(each.part())));
                    // A rule whose text this compiler did not work out is a rule it did not read.
                    case StringPredicates.Reading.WrittenArgumentNotKnown _ ->
                            unread.add(StringOfferShortfall.NotOffered.ofARuleNotRead(
                                    each.part(), new BlockReason.UnreadValueRule()));
                    // No predicate over strings at all, which is nothing about this question.
                    case null -> { }
                }
            }
        }
        return new PatternsStated(read, new StringOfferShortfall(unread));
    }

    /**
     * What the rules about a position's strings came to when they were read to compose a value
     * from: the patterns this compiler read, and what stopped it reading the rest.
     *
     * <p><b>Both, because they answer different callers.</b> A value to paste into a row comes from
     * what was read, and every rule this could not read leaves that value one the rules may still
     * refuse — so a caller that offered them and had them all refused is holding a search that
     * never had the whole of what the position states. Held as the patterns alone, that caller has
     * nothing to say but that the model refused everything.
     *
     * @param read   what each rule this compiler read accepts, under the rule it was written as,
     *               innermost name first
     * @param unread the rules about the strings this compiler did not read, each under itself
     */
    private record PatternsStated(List<Stated> read, StringOfferShortfall unread) {

        private static final PatternsStated NONE =
                new PatternsStated(List.of(), StringOfferShortfall.NONE);

        private PatternsStated {
            read = List.copyOf(read);
        }

        /** Just the patterns, for a caller that offers a value per rule and names none of them. */
        private List<StringPredicates.StatedPattern> patterns() {
            return read.stream().map(Stated::accepts).toList();
        }
    }

    /**
     * One rule about the strings at a position, as the rule it was written as and what it accepts.
     *
     * <p>Carried together because a rule whose machine cannot be afforded is named to an author by
     * the rule and not by the pattern: two rules of one declaration state two patterns, and a
     * sentence about "the pattern here" leaves them to guess which. The pattern is the one the
     * rule's reading handed out, which is what lets its machine be a rule's
     * ({@link PatternForAWitness}).
     */
    private record Stated(PartId<RuleRef.Invariant> part,
                          StringPredicates.StatedPattern accepts) {}

    /**
     * Whether {@code text} is a string every pattern the rules on {@code piece} state admits — and
     * false where there is no such pattern, which says nothing of whether the type admits it.
     *
     * <p>The string of the type itself, which is the string a case conversion has made and not the
     * string the conversion was given: the strings of the input that are made into it are
     * {@link PieceShape.MadeInto}'s to work out.
     *
     * <p>A pattern whose machine could not be made is told to {@code stoppedAt} as the figure it
     * was refused at, and the answer is false: not that the string is refused, but that nothing here
     * can say it is admitted.
     */
    static boolean pieceAdmits(Type piece, RuleReadingContext reading, String text,
                               Consumer<Figure> stoppedAt) {
        List<StringPredicates.StatedPattern> patterns = patternsOfAPiece(piece, reading);
        if (patterns.isEmpty()) {
            return false;
        }
        for (StringPredicates.StatedPattern each : patterns) {
            switch (reading.revision().settled(new PatternForAWitness(each))) {
                case PatternForAWitness.Made.Built(Language language, var _) -> {
                    if (!language.has(text)) {
                        return false;
                    }
                }
                case PatternForAWitness.Made.NotBuilt(Meter.Stopped stopped) -> {
                    stoppedAt.accept(figureOf(PatternForAWitness.refusedAt(stopped)));
                    return false;
                }
            }
        }
        return true;
    }

    /** The figure a machine for the strings that part into pieces was refused at. */
    static Figure figureOf(PatternPlan.Refused refused) {
        return refused.as(WorkFigure.STRINGS_PARTED_ONE_MACHINE,
                WorkFigure.STRINGS_PARTED_IN_ALL);
    }

    /** What refused {@code meter}, or nothing where it refused nothing: a construction that
     *  came back empty for another reason is not one a limit stopped. */
    private static Optional<PatternPlan.Refused> refusedBy(Meter meter) {
        Meter.Stopped stopped = meter.stoppedBy();
        return stopped == null ? Optional.empty() : Optional.of(refusedAsAWitness(stopped));
    }

    /** The refusal by {@code stopped} of what is built under the allowance of a witness. */
    static PatternPlan.Refused refusedAsAWitness(Meter.Stopped stopped) {
        return new PatternPlan.Refused(PatternPlan.Budget.OF_A_WITNESS, stopped);
    }

    /** Every pattern the rules on {@code piece} state, in the order they are written. */
    private static List<StringPredicates.StatedPattern> patternsOfAPiece(
            Type piece, RuleReadingContext reading) {
        RuleReadingSource ruleSource = reading.source();
        return patternsStatedOn(TypeView.of(piece, ruleSource.inners(), ruleSource.symbols(),
                ruleSource.kinds(), ruleSource.sums()), ruleSource).patterns();
    }

    /**
     * The strings that {@code through} makes into a string {@code meaning} accepts, so far as every
     * one of them is known to be: the strings of the ASCII range, where a case conversion maps one
     * code point to one and the same one however it stands among the others.
     *
     * <p>Not the strings of the whole range. What a conversion makes of a text is the run time's full
     * Unicode mapping and then NFC ({@link CaseMapping}), which a code point does not carry alone:
     * a letter followed by a mark composes into another. So the symbols past the ASCII range are
     * left out, which loses strings and never admits one that is not, and a pattern whose strings
     * are all outside it is the empty language — the question has no answer there, and says so by
     * offering nothing.
     */
    private static PatternMeaning beforeConversion(PatternMeaning meaning, CaseMapping through) {
        return switch (meaning) {
            case PatternMeaning.Nothing _, PatternMeaning.Never _ -> meaning;
            case PatternMeaning.Symbols symbols ->
                    new PatternMeaning.Symbols(before(symbols.held(), through));
            case PatternMeaning.InTurn turn -> new PatternMeaning.InTurn(turn.parts().stream()
                    .map(each -> beforeConversion(each, through)).toList());
            case PatternMeaning.EitherOf either -> new PatternMeaning.EitherOf(either.arms()
                    .stream().map(each -> beforeConversion(each, through)).toList());
            case PatternMeaning.Repeated repeated -> new PatternMeaning.Repeated(
                    beforeConversion(repeated.what(), through), repeated.least(),
                    repeated.most());
        };
    }

    /**
     * The code points of the ASCII range that {@code through} makes into one of {@code held}: what
     * the outermost conversion makes of a code point is what the one inside it is then asked of.
     */
    private static CodePoints before(CodePoints held, CaseMapping through) {
        return switch (through) {
            case CaseMapping.None _ -> held;
            case CaseMapping.Lowercase lowercase -> before(asciiMadeInto(held,
                    each -> each >= 'A' && each <= 'Z' ? each + ('a' - 'A') : each),
                    lowercase.of());
            case CaseMapping.Uppercase uppercase -> before(asciiMadeInto(held,
                    each -> each >= 'a' && each <= 'z' ? each - ('a' - 'A') : each),
                    uppercase.of());
        };
    }

    private static CodePoints asciiMadeInto(CodePoints held, IntUnaryOperator convert) {
        CodePoints out = CodePoints.NONE;
        for (int each = 0; each < 128; each++) {
            if (held.has(convert.applyAsInt(each))) {
                out = out.or(CodePoints.of(each));
            }
        }
        return out;
    }

    /**
     * Whether a code point of a string that {@code through} makes into what is parted stands where
     * the string is parted, which is where it is made into {@code separator}.
     *
     * <p>The one answer to where a string is parted that both the language of the strings made for a
     * body and the reading of a string a run was seen with go by, so that the pieces the second
     * counts are the places the first puts.
     */
    static IntPredicate partsAt(int separator, CaseMapping through) {
        return before(CodePoints.of(separator), through)::has;
    }

    /**
     * Whether {@code through} leaves {@code text} as it is, so far as that is known of every string:
     * the code points of the ASCII range each of which is made into itself.
     *
     * <p>For a caller that prefers a string of the input to be the string it is made into, where
     * it can be: the least string that is made into a text is a string of capitals for a text of
     * small letters, which is a string of the input and not one anybody would write.
     */
    static boolean isUnchangedBy(String text, CaseMapping through) {
        return text.codePoints().allMatch(each -> before(CodePoints.of(each), through).has(each));
    }

    /**
     * A string the rules on {@code position} admit that, once {@code through} has made it into
     * what is parted, parts at {@code separator} into the places of {@code pieces}, each as its
     * shape says ({@link PieceShape}) — or nothing where the rules on {@code piece} state no
     * pattern, or leave no such string.
     *
     * <p>Each place is taken to the language of the input by one reading of the shape it is in
     * ({@link StringsPartedInto}), so that a string of the input and a string it is made into are
     * never the same string to a caller.
     *
     * <p>The rules met and not one chosen from the other's strings: a piece that is a string the
     * type admits may be refused as part of the position's string, and the one the position admits
     * may part into pieces the type refuses, so a string meeting both is looked for in the language
     * of their meet. A position whose rules say nothing about its strings admits every string, and
     * the pieces alone decide. A piece held to several patterns is held to each of them in its
     * place, and the languages of the places met.
     *
     * <p>A string that is not there because no string meets the rules is told apart from one that is
     * not there because a machine could not be made: the second says which limit refused it.
     */
    static StringsPartedInto.Parted stringsPartedInto(TypeView position,
                                                      RuleReadingContext reading, Type piece,
                                                      int separator, CaseMapping through,
                                                      List<PieceShape> pieces) {
        if (pieces.isEmpty() || !(position.shape() instanceof Shape.Scalar scalar)
                || scalar.prim() != Type.Prim.STRING) {
            return StringsPartedInto.NONE;
        }
        List<StringPredicates.StatedPattern> patterns = patternsOfAPiece(piece, reading);
        if (patterns.isEmpty()) {
            return StringsPartedInto.NONE;
        }
        // Copied here, so that the work is the same work whoever's list it was asked with.
        return reading.revision().settled(new StringsPartedInto(
                rulesReadOn(position, reading), List.copyOf(patterns), separator, through,
                List.copyOf(pieces)));
    }

    /**
     * A string the rules admit that parts into the pieces of a shape, each a string every pattern of
     * a type admits or the string it is, as work settled by those rules.
     *
     * <p>The parts and the meet are made here, under the allowance of one witness: they are a
     * machine this question composes, which is nobody's rule. The pattern of a piece is borrowed
     * from the rule that states it.
     *
     * @param rules the rules on the position, or null where they say nothing about its strings
     */
    record StringsPartedInto(RulesRead rules, List<StringPredicates.StatedPattern> patterns,
                             int separator, CaseMapping through, List<PieceShape> pieces)
            implements RevisionWork<StringsPartedInto.Parted> {

        /** What making the strings came to. */
        sealed interface Parted {
        }

        /** The strings made, none where no string meets the rules. */
        record StringsMade(List<String> strings) implements Parted {
        }

        /** No strings could be made, and what refused the machine where a limit did. */
        record StringsNotMade(Optional<PatternPlan.Refused> refused) implements Parted {
        }

        /** Nothing to make: the position or the type says nothing this reads. */
        static final Parted NONE = new StringsMade(List.of());

        @Override
        public Parted workedOut(RevisionKnowledge revision) {
            Meter meter = PatternPlan.Budget.OF_A_WITNESS.meter();
            PatternMeaning any = new PatternMeaning.Repeated(
                    new PatternMeaning.Symbols(CodePoints.EVERYTHING), 0,
                    PatternMeaning.Repeated.NO_CEILING);
            // The string is parted as it is made into: what stands where the separator does is
            // whatever the conversion makes into it.
            PatternMeaning at = beforeConversion(
                    new PatternMeaning.Symbols(CodePoints.of(separator)), through);
            // One language for each pattern, the places of the pieces the same in all of them, so
            // that a piece is held to every pattern in its place. The separators the string holds
            // are as many as its pieces leave, so the places do not move between the languages.
            PatternPlan whole = null;
            for (StringPredicates.StatedPattern each : patterns) {
                List<PatternMeaning> parted = new ArrayList<>();
                for (int place = 0; place < pieces.size(); place++) {
                    if (place > 0) {
                        parted.add(at);
                    }
                    parted.add(inTheInput(pieces.get(place), each.meaning(), through));
                }
                PatternPlan one = PatternPlan.of(new PatternMeaning.InTurn(parted));
                whole = whole == null ? one : whole.and(one);
            }
            List<PatternMeaning> tooMany = new ArrayList<>();
            for (int each = 0; each < pieces.size(); each++) {
                tooMany.add(any);
                tooMany.add(at);
            }
            tooMany.add(any);
            // A separator in a piece is another piece, so the strings with as many separators as
            // pieces, or more, are left out.
            Language made = whole.less(PatternPlan.of(new PatternMeaning.InTurn(tooMany)))
                    .compile(meter);
            if (made != null && rules != null) {
                CandidateStrings position = admittedBy(rules.stated(), rules.characters(), meter,
                        revision);
                if (position.language() == null) {
                    // Nothing left of the position's strings: no string meets the rules where
                    // nothing refused the machine, and none can be said to where something did —
                    // which allowance it was is the position's rules' to say, and not this one's.
                    return rules.characters().empty() || position.shortfall().isEmpty() ? NONE
                            : new StringsNotMade(position.shortfall().refusedBy());
                }
                made = made.and(position.language(), meter);
            }
            if (made == null) {
                return new StringsNotMade(refusedBy(meter));
            }
            String some = made.someWritten();
            return some == null ? NONE : new StringsMade(List.of(some));
        }

        /**
         * What a place stands for in the strings of the input: the piece as it was seen is the
         * string itself, and a place made into a string or into any the type admits is the strings
         * that are made into it.
         *
         * <p>Exhaustive over the shapes, so a shape added without a reading here does not compile —
         * which is how a string of one of the two strings stops being taken for the other's.
         */
        private static PatternMeaning inTheInput(PieceShape shape, PatternMeaning admitted,
                                                  CaseMapping through) {
            return switch (shape) {
                case PieceShape.AsSeen seen -> written(seen.written());
                case PieceShape.MadeInto made -> beforeConversion(written(made.converted()),
                        through);
                case PieceShape.AnyTheTypeAdmits _ -> beforeConversion(admitted, through);
            };
        }

        /** The one string {@code text} is, as the pattern that accepts it alone. */
        private static PatternMeaning written(String text) {
            if (text.isEmpty()) {
                return new PatternMeaning.Nothing();
            }
            return new PatternMeaning.InTurn(text.codePoints()
                    .<PatternMeaning>mapToObj(each ->
                            new PatternMeaning.Symbols(CodePoints.of(each))).toList());
        }
    }

    /** Whether a rule counts the characters, which leaves out every string of another length and
     *  is a thing to be met with the patterns like any other. */
    private static boolean countsTheCharacters(DeclaredBounds.CountRange characters) {
        return !(characters.least() == 0 && characters.most() == Integer.MAX_VALUE);
    }

    /**
     * The strings the rules this compiler read admit between them, and what stopped it reading the
     * rest of them.
     *
     * <p>The rules this compiler could not read are carried and not met: there is nothing to meet
     * them with. What comes back is a meet of the rest, which is a set to propose values out of and
     * not what the position admits — every value taken from it is put to the decoder, and the rules
     * that are missing from it are the ones the decoder may still refuse it for.
     *
     * <p>Each rule's machine is borrowed from {@code revision} and costs {@code meter} nothing
     * ({@link PatternForAWitness}); what {@code meter} pays for is the meet and the count.
     */
    private static CandidateStrings admittedBy(PatternsStated stated,
                                               DeclaredBounds.CountRange characters, Meter meter,
                                               RevisionKnowledge revision) {
        StringOfferShortfall shortfall = stated.unread();
        Language all = null;
        for (Stated each : stated.read()) {
            switch (revision.settled(new PatternForAWitness(each.accepts()))) {
                // The rule whose machine this is, so that what could not build it names the rule
                // rather than the position. Whichever limit it was: the allowance it ran past was
                // that pattern's own.
                case PatternForAWitness.Made.NotBuilt(Meter.Stopped stopped) -> {
                    return new CandidateStrings(null, shortfall.and(StringOfferShortfall.of(
                            StringOfferShortfall.NotOffered.patternNotBuilt(
                                    new StringOfferShortfall.Subject.ARule(each.part()),
                                    stopped))));
                }
                case PatternForAWitness.Made.Built(Language one, var _) -> {
                    // And what it comes to with the rules before it, which is nobody's rule: an
                    // author sent to either of them would be sent to one this compiler read from
                    // end to end. Read where the build came back with nothing and not afterwards:
                    // the meter is the whole question's, and the next construction on it says
                    // which limit refused that one.
                    Language both = all == null ? one : all.and(one, meter);
                    if (both == null) {
                        return new CandidateStrings(null, shortfall.and(StringOfferShortfall.of(
                                StringOfferShortfall.NotOffered.whileMaking(
                                        new StringOfferShortfall.Subject.WhatTheyLeaveTogether(),
                                        meter))));
                    }
                    all = both;
                }
            }
        }
        return all == null ? new CandidateStrings(null, shortfall)
                : withinTheCount(all, characters, meter, shortfall);
    }

    /**
     * {@code strings} less the ones the rules leave no room for, with nothing to draw from where
     * the count leaves none at all, and with what the allowance refused where it would not pay for
     * the narrowing.
     *
     * <p>The count as a language, because that is what meeting it with the strings takes. What the
     * rules leave is a run of counts and what is being narrowed is a set of strings, and the two are
     * put together the way every pair of sets here is.
     *
     * <p>The two ways of coming back with nothing are not one answer. A count that leaves no string
     * is what the rules say, and a narrowing this could not afford is what this compiler did — so
     * the second is carried and the first is the ordinary absence of anything to paste.
     *
     * <p>The question's own work, paid out of {@code meter}. The strings so many characters long
     * are a machine this composes on the way to a value and no rule an author wrote, so it is not
     * a pattern's producer that builds it; and the question it is built for is itself worked out
     * once for the revision, so it is built once for every asking of that question.
     */
    private static CandidateStrings withinTheCount(Language strings,
                                                   DeclaredBounds.CountRange characters,
                                                   Meter meter, StringOfferShortfall shortfall) {
        if (characters.empty()) {
            // No count at all, so no string of the position holds one. An answer about the rules
            // and not a shortfall of this compiler's, which is why nothing is added beside it.
            return new CandidateStrings(null, shortfall);
        }
        if (!countsTheCharacters(characters)) {
            return new CandidateStrings(strings, shortfall);  // every count, nothing to take away
        }
        Language counted = PatternPlan.of(PatternMeaning.ofAnySymbols(characters.least(),
                characters.most() == Integer.MAX_VALUE
                        ? PatternMeaning.Repeated.NO_CEILING : characters.most())).compile(meter);
        Language within = counted == null ? null : strings.and(counted, meter);
        // The count met with the strings, which is again nobody's one rule.
        return within == null
                ? new CandidateStrings(null, shortfall.and(StringOfferShortfall.of(
                        StringOfferShortfall.NotOffered.whileMaking(
                                new StringOfferShortfall.Subject.WhatTheyLeaveTogether(), meter))))
                : new CandidateStrings(within, shortfall);
    }

    /** A count the position holds, or null where it holds none. The ends decide it, so nothing here
     * reads one of them as a number and loses whether the range reaches it. A value standing for
     * the range ({@link Carrier#aPlaceInside}), as a date nobody bounded on a side is the date
     * nearest today. */
    private static Place inside(NumericDomain.Bounds within, Carrier carrier, Today today) {
        Place between = carrier.aPlaceInside(within == null ? null : within.min(),
                within == null ? null : within.max(), carrier.usualPlace(today));
        if (between == null) {
            return null;
        }
        // On the carrier's own grid, and then still inside. A number between two counts it can hold
        // is not always one of them (see Carrier#onTheGrid).
        Place held = carrier.onTheGrid(between);
        return held != null && (within == null || within.admits(held)) ? held : null;
    }

    /**
     * What a position can offer once everything it ordinarily offers has been refused.
     *
     * <p>The far edge of a range, for a position that is a bounded number. A rule relating this
     * position to another is what refuses the near one: `low < high` with `low` already fixed leaves
     * `high` a range starting at the value `low` took, and over decimals that range starts at the one
     * number the rule will not accept, because a strict bound there has no next value to step to. The
     * far edge is not knowing which number the rule wants — it is having a second number to be
     * refused at, which a range offering one edge does not.
     *
     * <p>Held back rather than offered beside the others, because what a row is searched for is the
     * product of what its positions offer and that search is bounded. A value added to one position
     * moves every assignment past it further back, so offering this one among the rest would lose
     * rows that were being reached at positions this has nothing to do with.
     *
     * @param offered what the position already offers, which the caller has in hand: nothing held
     *                back is one of them
     */
    static List<FixtureTemplate> inReserve(Type type, RuleReadingContext reading,
                                           NumericDomain.Bounds within,
                                           List<FixtureTemplate> offered) {
        return inReserve(TypeView.of(type, reading.source().inners(), reading.source().symbols(),
                        reading.source().kinds(), reading.source().sums()), reading, within,
                offered);
    }

    /** The same, of a position that has already been read. */
    static List<FixtureTemplate> inReserve(TypeView view, RuleReadingContext reading,
                                           NumericDomain.Bounds within,
                                           List<FixtureTemplate> offered) {
        RuleReadingSource ruleSource = reading.source();
        // A far edge is a rule's, and a rule is written on a name. A position wearing none carries
        // no rule of its own, so there is no edge here to hold anything back at.
        if (!view.isWrapped()) {
            return List.of();
        }
        DeclaredBounds.Range own = DeclaredBounds.of(view, reading);
        NumericDomain.Bounds bounds = TypeBounds.admissible(own, within);
        // The far end has to be a value the position holds. Where the range stops short of it there
        // is nothing there to hold back, and a dense order has no value beside it to hold back
        // instead — what is inside is already what the first tier offers.
        if (bounds == null || bounds.min() == null || bounds.max() == null
                || !bounds.max().inclusive()
                || bounds.max().at().sameAs(bounds.min().at())) {
            return List.of();
        }
        FixtureTemplate held = WornNames.under(view.wrappers(),
                FixtureTemplate.on(own.carrier(), bounds.max().at(),
                        ruleSource.symbols().scope()::reach), ruleSource);
        if (held == null) {
            return List.of();   // a name this module cannot write leaves no value to hold back
        }
        // Nothing already on offer: a range whose far edge is the number the base type stands for
        // would otherwise hold the same value twice, once in each tier. Asked of the offer the
        // caller made rather than of an offer built again for the asking.
        return offered.stream().map(FixtureTemplate::text).anyMatch(held.text()::equals)
                ? List.of() : List.of(held);
    }

    /**
     * What a search composing a value at one of this phase's positions is given: the sets the
     * declarations leave them, where a name of one value stands in another, and what looking for a
     * value in one may cost.
     *
     * <p>Here because this is where what a position admits is already in hand and where what writing
     * one value out may cost is already granted. A search reaching for either would be a second
     * answer about the model beside an allowance nothing granted it.
     */
    static WitnessSearch witnessSearch(List<PositionMeasurements> measurements, NameReach reach,
                                       Today today) {
        java.util.Map<TermPath, ValueSet> sets = new LinkedHashMap<>();
        for (PositionMeasurements at : measurements) {
            // Every position the reading measured, including the ones whose rules leave them
            // everything. What a position admits and whether anybody asked are different states, and
            // a map with a hole in it cannot tell a caller which of the two it is looking at.
            sets.put(at.position().path(), at.position().admits());
        }
        // And what the same walk saw of the names that stand somewhere other than the position of
        // the same name one step down, so that a path this measurement has no position at is told
        // from a position it was left short of. Worked out from the measurements alone, the two
        // would be one hole in one map.
        return new WitnessSearch(AdmittedValues.of(sets, reach),
                PatternPlan.Budget.OF_A_WITNESS::meter, today);
    }

    private Partitions() {}
}
