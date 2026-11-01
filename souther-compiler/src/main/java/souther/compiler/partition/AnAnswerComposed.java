package souther.compiler.partition;

import souther.compiler.inputs.InputNumber;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Requirements;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.AnswerAsAnInput;
import souther.compiler.meaning.DecisionAtom;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.WhyNotTaken;
import souther.compiler.observe.Figure;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import java.util.ArrayList;
import java.util.EnumSet;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.function.Function;

/**
 * A value for one answer a rule asks something of.
 *
 * <p>The same realization a value at a position goes through, asked about a type rather than about
 * a behavior's input. What a demand asks — a case, a truth, a comparison — is what a way already
 * asks of a position, so what composes a value for one composes a value for the other, and a second
 * composer written here would be a second answer to which values a type's own rules leave.
 *
 * <p><b>An adapter and not a promotion.</b> The subject handed in stands for one value and is read
 * by nothing else: an answer is not a position of anybody's input, and what a search may assume
 * about an input is not what a row may pin a dependency to. Where such a subject is made is where
 * every reading of a behavior's input is made, so that nothing here is a second maker of one. What
 * leaves is the value, which belongs to whoever asked.
 *
 * <p>Nothing put through a decoder. What certifies a composed answer is the run: a row is stood up
 * with it, applied, and asked which rule it took, and a value the model refuses is a stand-in that
 * will not build and a rule left where it was. So a value from here is a candidate and never a
 * witness — which is the same standing a value composed at a position has before its row is run.
 */
public final class AnAnswerComposed {

    private AnAnswerComposed() {}

    /** A value for the answer, or the reason nothing here composed one. */
    public sealed interface Outcome {

        /** A value that satisfies every demand this composed against. */
        record Composed(FixtureTemplate value) implements Outcome {}

        /** Nothing came of it, in the words a search comes back with. Never a statement that no
         *  value exists. */
        record NothingComposed(Generator.UnresolvedCombination.Reason why) implements Outcome {}
    }

    /**
     * What came of composing a value, and which demands it was not composed against.
     *
     * <p>A product because the two are independent. A value that meets every demand and a value
     * that meets the ones this compiler could put under it are both values a caller may hand to a
     * row, and only the second leaves a reader something to be told — so the account travels
     * whatever the outcome is, and a caller cannot read one without the other being in hand.
     *
     * @param unaccounted the demands no value here was composed against, in the order they were
     *                    asked
     */
    public record Attempt(Outcome outcome, List<DemandGap> unaccounted) {

        public Attempt {
            if (outcome == null) {
                throw new IllegalArgumentException("a composition of an answer came to something");
            }
            unaccounted = List.copyOf(unaccounted);
        }

        /** One that left nothing out. */
        static Attempt of(Outcome outcome) {
            return new Attempt(outcome, List.of());
        }

        /** One that came to nothing, in the words a search comes back with. */
        static Attempt nothing(Generator.UnresolvedCombination.Reason why,
                               List<DemandGap> unaccounted) {
            return new Attempt(new Outcome.NothingComposed(why), unaccounted);
        }
    }

    /**
     * A value of what {@code subject} stands for that meets {@code demands}.
     *
     * <p>The demands of one answer and no other. What a row stands two dependencies in with is two
     * values, each composed against what the way asks of it; a comparison relating them is not a
     * demand on either, and is one this reading leaves unstated rather than splitting.
     *
     * @param subject one position, standing for what the dependency answers. Made where every
     *                reading of an input is made, and holding one parameter because what is
     *                composed here is one value
     * @param demands what the way asks of it, every one of them about this answer
     */
    public static Attempt of(MeasuredInput subject, List<AnswerDemand> demands) {
        return of(subject, StatementsOfAnInput.NONE, demands);
    }

    /**
     * The same, where a statement about what the answer holds is asked too.
     *
     * @param statements what a statement made over the subject asks of a row, which is the reading
     *                   of the type the subject stands for
     */
    public static Attempt of(MeasuredInput subject, StatementsOfAnInput statements,
                             List<AnswerDemand> demands) {
        return of(subject, statements, Map.of(), demands);
    }

    /**
     * The same, where a statement also names numbers of the behavior's own input.
     *
     * @param pinned the value each such number is put at, which is the row the value is composed
     *               to stand in: what the answer has to be turns on them, and a number left out
     *               is a statement this does not compose against
     */
    public static Attempt of(MeasuredInput subject, StatementsOfAnInput statements,
                             Map<NumericTerm, ExactRatio> pinned, List<AnswerDemand> demands) {
        if (subject.parameters().size() != 1) {
            throw new IllegalArgumentException(
                    "an answer is one value, and this stands for " + subject.parameters().size());
        }
        String at = subject.parameters().getFirst();
        Boolean truth = truthOfTheWholeAnswer(demands);
        if (truth != null) {
            // A truth asked of the answer itself, which is two values and holds no position — so
            // there is nothing to narrow and nothing to place, and the value is the answer. A truth
            // asked of a place inside one is not this, and is written where the value is composed.
            return demands.size() == 1
                    ? Attempt.of(new Outcome.Composed(FixtureTemplate.bool(truth)))
                    : Attempt.of(new Outcome.NothingComposed(
                            Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE));
        }
        Requirements required = Requirements.NONE;
        for (AnswerDemand each : demands) {
            if (!(each instanceof AnswerDemand.ACase(var _, var _, var steps, var to))) {
                continue;
            }
            if (!(required.merge(path(at, steps).refine(to).requirements())
                    instanceof Requirements.Merge.Merged(var both))) {
                // The way asks the answer to be two cases at once, which no value is. A fact about
                // what was asked rather than about what was tried, and it comes back as nothing
                // composed for the reason every other answer here does: what a caller does with it
                // is settle the rule elsewhere, and a second word for it here would be a second
                // account of a way nothing takes.
                return Attempt.of(new Outcome.NothingComposed(
                        Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE));
            }
            required = both;
        }
        // Which value each Bool place inside the answer is asked to hold, which the value is
        // composed holding. Both values asked of one place is the way asking for no value, said
        // for the reason two cases asked of one place are above.
        List<RowDemand.ATruth> asked = new ArrayList<>();
        for (AnswerDemand each : demands) {
            if (each instanceof AnswerDemand.ATruth(var _, var _, var steps, var held)
                    && !steps.isEmpty()) {
                asked.add(new RowDemand.ATruth(path(at, steps), held));
            }
        }
        // What a statement asks, said of the input that stands for the answer and asked of a row
        // as any statement about an input is. A statement that asks one of several things is
        // looked along each of them, as a way over the input is.
        List<DemandGap> unaccounted = new ArrayList<>();
        List<Pending> pending = new ArrayList<>();
        for (AnswerDemand each : demands) {
            if (!(each instanceof AnswerDemand.AStatement statement)) {
                continue;
            }
            AnswerAsAnInput.Remade remade = AnswerAsAnInput.of(statement.statement(), at,
                    subject.rules().inners(), subject.symbols(), pinned);
            // A count of statements in it whose choices are past a figure: nothing was composed
            // against it before that figure, which looking further would cure.
            if (remade instanceof AnswerAsAnInput.Remade.PastAFigure(CompositionBudget figure)) {
                unaccounted.add(new DemandGap.Uncomposed(each,
                        DemandGap.WhyNotComposed.NoWayComposedBeforeAFigureEnded.by(
                                List.of(figure))));
                continue;
            }
            Proposition over = remade instanceof AnswerAsAnInput.Remade.Stated(Proposition stated)
                    ? stated : null;
            List<DemandReading.Read> reads = over == null ? null : statements.asked(over);
            // Past a figure nothing was looked along, which is not the same as there being nothing
            // a composer writes: only the first is cured by looking further.
            switch (reads == null ? new Ways.Unwritable() : written(reads)) {
                case Ways.Written(var stoppedBy) ->
                        pending.add(new Pending(statement, reads, stoppedBy));
                case Ways.Stopped(var by) -> unaccounted.add(new DemandGap.Uncomposed(each,
                        DemandGap.WhyNotComposed.NoWayComposedBeforeAFigureEnded.by(by)));
                case Ways.Unwritable _ -> unaccounted.add(new DemandGap.Uncomposed(each,
                        new DemandGap.WhyNotComposed.NoValueComposedAtItsPositions()));
            }
        }
        // The ways the statements together can be taken: one way of all of them is enough, so
        // those are looked along — every combination of their open alternatives where the figure
        // lets them all be, and otherwise each open alternative once beside the others' first
        // ({@link OneOfEach}) — and where a figure left some of them, each statement is one a
        // figure stopped the looking for.
        List<Asked> entries = new ArrayList<>();
        for (Pending each : pending) {
            each.reads().forEach(read -> entries.add(new Asked(each.statement(), read)));
        }
        Requirements cases = required;
        return composedAlongTheWays(OneOfEach.walk(entries, new WrittenTogether(asked),
                        CompositionBudget.CHOICES_ON_A_WAY_LOOKED_AT,
                        CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG),
                way -> composedAlong(subject, at, cases, asked, unaccounted, way, demands),
                unaccounted, pending);
    }

    /**
     * The first value {@code composing} makes along one of {@code walked}'s ways that meets every
     * statement — or, where none does, what the first way came to, with each statement a figure
     * left some of its ways unlooked at said to be one it stopped the looking for.
     *
     * <p>A way that left a choice unchosen is composed along what it chose, and each statement it
     * left a choice of is said to be one the figure stopped the looking for: nothing composed
     * along it was put to what the choice asks, so the value is not one that meets it.
     *
     * @param unaccounted what no way of the statements accounts for, said beside a way that came
     *                    to nothing
     * @param pending     the statements the ways are of
     */
    static Attempt composedAlongTheWays(OneOfEach.Walked<Asked, Asked> walked,
                                        Function<List<Asked>, Attempt> composing,
                                        List<DemandGap> unaccounted, List<Pending> pending) {
        List<OneOfEach.Way<Asked>> ways;
        CompositionBudget jointly;
        switch (walked) {
            case OneOfEach.Walked.Closed<Asked, Asked> _ -> {
                ways = List.of();
                jointly = null;
            }
            case OneOfEach.Walked.Stopped<Asked, Asked>(var figure) -> {
                ways = List.of();
                jointly = figure;
            }
            case OneOfEach.Walked.Open<Asked, Asked>(var open, var stoppedBy) -> {
                ways = open;
                jointly = stoppedBy;
            }
        }
        Attempt first = null;
        for (OneOfEach.Way<Asked> way : ways) {
            Attempt here = switch (way) {
                case OneOfEach.Way.Chosen<Asked>(var entries, var _) -> composing.apply(entries);
                case OneOfEach.Way.LeftUnchosen<Asked>(var chosen, var unchosen) ->
                        leavingWhatWasNotChosen(composing.apply(chosen), unchosen, jointly);
            };
            if (here.outcome() instanceof Outcome.Composed && here.unaccounted().isEmpty()) {
                return here;
            }
            first = first == null ? here : first;
        }
        if (first == null) {
            first = Attempt.nothing(Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE,
                    unaccounted);
        }
        return sayingWhatStoppedTheLooking(first, pending, jointly);
    }

    /** {@code composed}, with each statement {@code unchosen} is of said to be one {@code figure}
     *  stopped the looking for. */
    private static Attempt leavingWhatWasNotChosen(Attempt composed, List<Asked> unchosen,
                                                   CompositionBudget figure) {
        Set<AnswerDemand> said = new HashSet<>();
        for (DemandGap each : composed.unaccounted()) {
            if (each instanceof DemandGap.Uncomposed(AnswerDemand demand, var _)) {
                said.add(demand);
            }
        }
        List<DemandGap> out = new ArrayList<>(composed.unaccounted());
        for (Asked each : unchosen) {
            if (said.add(each.statement())) {
                out.add(new DemandGap.Uncomposed(each.statement(),
                        DemandGap.WhyNotComposed.NoWayComposedBeforeAFigureEnded.by(
                                Set.of(figure))));
            }
        }
        return new Attempt(composed.outcome(), out);
    }

    /** One thing a statement asks, and the statement. */
    record Asked(AnswerDemand.AStatement statement, DemandReading.Read read) {}

    /**
     * What the statements ask as far as whether one way of them holds together: the truths it
     * asks beside the ones the answer is asked outright, and that nothing it asks is something no
     * value is composed toward or no value meets. A way that does not hold together is said by
     * the read it cannot take in beside the ones before it.
     *
     * @param asked the truths the answer is asked beside the statements
     */
    private record WrittenTogether(List<RowDemand.ATruth> asked)
            implements OneOfEach.Vocabulary<Asked, List<RowDemand.ATruth>, Asked> {

        @Override
        public List<List<Asked>> alternatives(Asked entry) {
            if (!(entry.read() instanceof DemandReading.Read.OneOf oneOf)) {
                return null;
            }
            List<List<Asked>> out = new ArrayList<>();
            for (List<DemandReading.Read> alternative : oneOf.alternatives()) {
                out.add(alternative.stream()
                        .map(read -> new Asked(entry.statement(), read)).toList());
            }
            return out;
        }

        @Override
        public Set<TermPath> positions(Asked entry) {
            return entry.read() instanceof DemandReading.Read.Demands(var demand)
                    ? demand.positions() : Set.of();
        }

        @Override
        public List<RowDemand.ATruth> nothing() {
            return List.copyOf(asked);
        }

        @Override
        public OneOfEach.Step<List<RowDemand.ATruth>, Asked> with(List<RowDemand.ATruth> so,
                                                                  Asked entry) {
            if (!composedAgainst(entry.read())) {
                return new OneOfEach.Step.Closed<>(entry);
            }
            if (!(entry.read() instanceof DemandReading.Read.Demands(RowDemand.ATruth truth))) {
                return new OneOfEach.Step.Held<>(so);
            }
            List<RowDemand.ATruth> truths = new ArrayList<>(so);
            truths.add(truth);
            return TruthsAsked.of(truths) instanceof TruthsAsked.Merge.Merged
                    ? new OneOfEach.Step.Held<>(List.copyOf(truths))
                    : new OneOfEach.Step.Closed<>(entry);
        }
    }

    /**
     * {@code failed}, with each statement some of whose ways a figure left unlooked at, and that
     * no value met, said to be one that figure stopped the looking for.
     *
     * <p>Not one nothing composes for: the ways looked along came to no value, and a way past the
     * figure may be one that does. So the figure is what is said of it, as it is where the values of
     * the input's numbers ran out ({@link CompositionAccount#sayingAFigureEndedTheLookingOverNumbers}).
     *
     * <p>Said whether or not the way looked along wrote anything down about the statement. A way
     * can come to no value for a reason that is about no statement — two truths asked of one place
     * — and a figure ridden on whatever the failure happened to say would go where nothing was
     * said, leaving the statement to be read as one nothing composes for. Where a value was
     * composed, a statement it is not said to be short of is one it met, and nothing is added.
     *
     * @param jointly the figure that cut the ways the statements were taken together along, or
     *                null where every one of them was looked along
     */
    private static Attempt sayingWhatStoppedTheLooking(Attempt failed, List<Pending> pending,
                                                       CompositionBudget jointly) {
        Map<AnswerDemand, Set<CompositionBudget>> stopped = new LinkedHashMap<>();
        for (Pending each : pending) {
            Set<CompositionBudget> by = EnumSet.noneOf(CompositionBudget.class);
            by.addAll(each.stoppedBy());
            if (jointly != null) {
                by.add(jointly);
            }
            if (!by.isEmpty()) {
                stopped.put(each.statement(), by);
            }
        }
        if (stopped.isEmpty()) {
            return failed;
        }
        List<DemandGap> said = new ArrayList<>();
        Set<AnswerDemand> named = new HashSet<>();
        for (DemandGap gap : failed.unaccounted()) {
            if (gap instanceof DemandGap.Uncomposed(AnswerDemand demand, var why)
                    && stopped.containsKey(demand)) {
                named.add(demand);
                if (!(why instanceof DemandGap.WhyNotComposed.NoWayComposedBeforeAFigureEnded)
                        && !(why instanceof DemandGap.WhyNotComposed
                                .NoPairComposedBeforeAFigureEnded)) {
                    said.add(new DemandGap.Uncomposed(demand,
                            DemandGap.WhyNotComposed.NoWayComposedBeforeAFigureEnded.by(
                                    stopped.get(demand))));
                    continue;
                }
            }
            said.add(gap);
        }
        if (failed.outcome() instanceof Outcome.NothingComposed) {
            stopped.forEach((demand, by) -> {
                if (!named.contains(demand)) {
                    said.add(new DemandGap.Uncomposed(demand,
                            DemandGap.WhyNotComposed.NoWayComposedBeforeAFigureEnded.by(by)));
                }
            });
        }
        return new Attempt(failed.outcome(), said);
    }

    /**
     * One statement and what it asks, some of which may be one of several things.
     *
     * @param stoppedBy the figures that left some of its ways unlooked at, empty where none did
     */
    record Pending(AnswerDemand.AStatement statement, List<DemandReading.Read> reads,
                           Set<CompositionBudget> stoppedBy) {}

    /** Whether the reads of a statement come to some way a value is composed toward, or why they
     *  come to none. */
    sealed interface Ways {

        /**
         * Some way of it is one a value is composed toward, and the figures that left others
         * unlooked at.
         *
         * <p>Any one way is enough for the statement to hold, so the ways looked at are composed
         * along whether or not others were left: a choice one of whose alternatives a figure
         * stopped is the other alternatives still.
         */
        record Written(Set<CompositionBudget> stoppedBy) implements Ways {

            public Written {
                stoppedBy = Set.copyOf(stoppedBy);
            }
        }

        /** A read a composer writes toward in no way: a narrowing of a case is what a way over the
         *  input carries, and nothing here puts it under a value composed for an answer. */
        record Unwritable() implements Ways {}

        /** No way looked at, and some left unlooked at by {@code by}: none is known to be one a
         *  composer writes nothing toward. */
        record Stopped(Set<CompositionBudget> by) implements Ways {

            public Stopped {
                by = Set.copyOf(by);
            }
        }
    }

    /**
     * The budget a part declined for {@code why} stopped at, or null where it stopped at none of
     * the composing stage's budgets — read off the figure the reason says it stopped at
     * ({@link WhyNotTaken#figure}). How far a container is written out is a figure and no budget,
     * and a value is not composed past it here.
     */
    private static CompositionBudget stoppedAt(WhyNotTaken why) {
        return why.figure().orElse(null) instanceof Figure.Budget(CompositionBudget budget)
                ? budget : null;
    }

    /**
     * Whether some way of taking {@code reads} is one a value is composed toward.
     *
     * <p>An alternative no way of which is written toward is passed over and the others are
     * taken; only where none is left is the choice what stopped them. Every read beside a choice
     * is asked along every way, so one of those no way is written toward stops all of them.
     */
    static Ways written(List<DemandReading.Read> reads) {
        Set<CompositionBudget> stoppedBy = EnumSet.noneOf(CompositionBudget.class);
        for (DemandReading.Read each : reads) {
            if (each instanceof DemandReading.Read.OneOf oneOf) {
                boolean some = false;
                for (List<DemandReading.Read> alternative : oneOf.alternatives()) {
                    switch (written(alternative)) {
                        case Ways.Written(var by) -> {
                            stoppedBy.addAll(by);
                            some = true;
                        }
                        case Ways.Stopped(var by) -> stoppedBy.addAll(by);
                        case Ways.Unwritable _ -> { }
                    }
                }
                if (!some) {
                    return stoppedBy.isEmpty() ? new Ways.Unwritable()
                            : new Ways.Stopped(stoppedBy);
                }
            } else if (each instanceof DemandReading.Read.Unread(var whys, var _)
                    && whys.stream().allMatch(why -> stoppedAt(why) != null)) {
                // Only where a figure is every reason: a part also left for a reason more
                // reading does not change is one no value is written toward either way.
                whys.forEach(why -> stoppedBy.add(stoppedAt(why)));
                return new Ways.Stopped(stoppedBy);
            } else if (!composedAgainst(each)) {
                return new Ways.Unwritable();
            }
        }
        return new Ways.Written(stoppedBy);
    }

    /**
     * A value for the answer, composed along one way of taking each statement it is asked.
     *
     * @param way what the statements ask along this way, each with the statement asking it
     */
    private static Attempt composedAlong(MeasuredInput subject, String at, Requirements required,
                                         List<RowDemand.ATruth> truthsAsked,
                                         List<DemandGap> unaccountedBefore, List<Asked> way,
                                         List<AnswerDemand> demands) {
        List<RowDemand.ATruth> asked = new ArrayList<>(truthsAsked);
        List<DemandGap> unaccounted = new ArrayList<>(unaccountedBefore);
        List<Taken> ofStatements = new ArrayList<>();
        for (Asked each : way) {
            switch (each.read()) {
                case DemandReading.Read.Demands(RowDemand.OfACondition demand) -> {
                    if (demand instanceof RowDemand.ATruth written) {
                        asked.add(written);
                    }
                    ofStatements.add(new Taken(
                            new OnTheWay.TakenIn(each.statement().anchor(), demand),
                            each.statement()));
                }
                case DemandReading.Read.Settled(boolean thisWay) -> {
                    if (!thisWay) {
                        return Attempt.nothing(
                                Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE,
                                unaccounted);
                    }
                }
                default -> { }
            }
        }
        TruthsAsked truths;
        switch (TruthsAsked.of(asked)) {
            case TruthsAsked.Merge.Merged(var merged) -> truths = merged;
            case TruthsAsked.Merge.Conflict _ -> {
                return Attempt.nothing(Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE,
                        unaccounted);
            }
        }
        SearchRegion region = subject.quantities().region();
        List<Taken> cuts = new ArrayList<>();
        for (Taken each : ofStatements) {
            region = new WayToTheBorder(List.of(each.cut())).narrowing(region);
            cuts.add(each);
        }
        for (AnswerDemand each : demands) {
            if (!(each instanceof AnswerDemand.AComparison(var _, var anchor, var form, var rel))) {
                continue;
            }
            LinearForm<NumericTerm> over = overThisAnswer(subject, at, form);
            if (over == null) {
                // A number the library takes of what stands there by no account this has a term
                // for, so nothing says what a value would have to be.
                unaccounted.add(new DemandGap.Uncomposed(each,
                        new DemandGap.WhyNotComposed.NoValueComposedAtItsPositions()));
                continue;
            }
            // Nothing composed where the region cannot carry what was asked. A demand dropped here
            // and the composition carried on would look for a value in a region wider than the
            // demand — and what came back would be offered as a value that answers it, which is
            // the one thing a caller may not be handed. Conservative widening is a reading's
            // privilege and not a composer's: a reading says what it could not take in and the
            // region it leaves is still every row that arrives, while a value composed against
            // rules the demand is not in answers nothing.
            //
            // Every one of them asked all the same. What the caller is owed is which demands were
            // not composed against, and stopping at the first would name whichever came first in
            // the order the walk met the conditions.
            switch (region.assuming(over, rel)) {
                case SearchRegion.Assumption.Taken(SearchRegion taken) -> {
                    region = taken;
                    cuts.add(new Taken(
                            new OnTheWay.TakenIn(anchor, new RowDemand.Relational(
                                    new TakenConstraint.Affine(over, rel))),
                            each));
                }
                case SearchRegion.Assumption.Refused(var why) ->
                        unaccounted.add(new DemandGap.Uncomposed(each, whyRefused(why)));
            }
        }
        if (!unaccounted.isEmpty()) {
            return Attempt.nothing(Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE,
                    unaccounted);
        }
        return composed(subject, cuts, new Reachability.Reaching(region, required, truths,
                cuts.stream().map(Taken::cut).toList(), Reachability.Ways.ONE, List.of(),
                Optional.empty()));
    }

    /**
     * Whether a composer writes toward what {@code read} says: a demand it can build a value
     * against, or a statement that holds whatever the value is. A narrowing of a case and a choice
     * between alternatives are what a way over the input carries, and nothing here puts them under
     * a value composed for an answer.
     */
    private static boolean composedAgainst(DemandReading.Read read) {
        return read instanceof DemandReading.Read.Demands
                || (read instanceof DemandReading.Read.Settled settled && settled.thisWay());
    }

    /**
     * One demand as the cut a realization was handed for it.
     *
     * <p>Kept as the pair rather than looked up again afterwards. What comes back from a
     * realization is the cut it could not place, and which demand that is is this — asked of the
     * cut it was built from and not of where a report about it points, since one written
     * comparison spliced into two calls of a helper is two demands reported at one place.
     */
    private record Taken(OnTheWay.TakenIn cut, AnswerDemand demand) {}

    /**
     * A region's refusal in the words an account of a demand is written in.
     *
     * <p>Two vocabularies because they answer to two readers, which is the arrangement the account
     * of the way is under as well: what a region says is about its own algebra and names the term
     * it has no order for, and what an account says is what an author is to make of a demand no
     * value was composed against.
     */
    private static DemandGap.WhyNotComposed whyRefused(SearchRegion.Refusal why) {
        return switch (why) {
            case SearchRegion.Refusal.NoOrderUnderATerm(var term) ->
                    new DemandGap.WhyNotComposed.NoOrderUnderATermOfTheAnswer(term);
        };
    }

    /**
     * The one value the subject's realization came to, or why it came to none.
     *
     * <p>One parameter and one value, which is what the reading built here has. A subject of more
     * would be a subject somebody else made, and the answer read off the first of its values would
     * be an answer about whichever position came first.
     */
    private static Attempt composed(MeasuredInput subject, List<Taken> cuts,
                                    Reachability.Reaching reaching) {
        Generator.BoundaryAttempt attempt = Generator.probeFixing(subject,
                "an answer of a dependency", Map.of(), NumbersAskedFor.ANYTHING, reaching,
                // Nothing refuses a candidate here. What a decoder answers about a value is asked
                // where the row that carries it is run, and a check written here would be this
                // reading building the dependency's own boundary a second way.
                Generator.CandidateCheck.ANY);
        List<DemandGap> unaccounted =
                notComposedAgainst(cuts, attempt.unrepresented().onTheWay());
        if (attempt instanceof Generator.BoundaryAttempt.Built(var row, var _, var _)
                && row.inputs().size() == 1) {
            return new Attempt(new Outcome.Composed(row.inputs().getFirst()), unaccounted);
        }
        return Attempt.nothing(attempt instanceof Generator.BoundaryAttempt.Unresolved(
                var why, var _) ? why.reason()
                        : Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE,
                unaccounted);
    }

    /**
     * The demands the realization took in and put no value under, in the words a caller of this
     * reads.
     *
     * <p>Read off what the realization came back with rather than worked out again. Every cut it
     * was handed was built from a demand of this answer and is carried beside it, so an entry it
     * could not place is that demand — asked of the cut and not of where a report about it points,
     * which is a place two demands may share.
     *
     * <p>One word for what the realization says in several. What it holds apart there is how it
     * went about looking — a budget it met, a pair of numbers at one location — and what a reader
     * of an answer acts on is that the demand was not met. A proof that the demands leave nothing
     * standing together is not one of these and is left where it is: it is a fact about what was
     * asked, and the outcome beside it already says the composition came to nothing.
     */
    private static List<DemandGap> notComposedAgainst(List<Taken> cuts,
                                                      List<ReachabilityGap> unrepresented) {
        if (unrepresented.isEmpty()) {
            return List.of();
        }
        List<DemandGap> out = new ArrayList<>();
        for (ReachabilityGap gap : unrepresented) {
            if (!(gap instanceof ReachabilityGap.Uncomposed(var cut, var _))) {
                continue;
            }
            for (Taken each : cuts) {
                if (each.cut().equals(cut)) {
                    out.add(new DemandGap.Uncomposed(each.demand(),
                            new DemandGap.WhyNotComposed.NoValueComposedAtItsPositions()));
                }
            }
        }
        return List.copyOf(out);
    }

    /**
     * Which way a truth asked of the whole answer came out, or null where nothing asks one.
     *
     * <p>Of the answer itself and not of a place inside it. A {@code Bool} divides a position into
     * two values and puts nothing under it, so the demand is the value; a truth read off a field is
     * a demand about a position this reading has no way of placing, and saying it here would
     * compose a value that satisfies the field's type and not the demand.
     */
    private static Boolean truthOfTheWholeAnswer(List<AnswerDemand> demands) {
        for (AnswerDemand each : demands) {
            if (each instanceof AnswerDemand.ATruth(var _, var _, var at, var held)
                    && at.isEmpty()) {
                return held;
            }
        }
        return null;
    }

    /** The place inside the answer, under the name the subject gives the whole of it. */
    private static TermPath path(String head, List<TermPath.Step> steps) {
        return TermPath.of(head, steps);
    }

    /**
     * A comparison's quantity in the terms of the reading built here.
     *
     * <p>The same quantity and not a second reading of it. Each atom is a place inside this answer,
     * which is a position of the one value this composes — so what the comparison states about the
     * dependency's answer is what it states about that position, spelled in the vocabulary the
     * realization works in.
     */
    private static LinearForm<NumericTerm> overThisAnswer(MeasuredInput subject, String head,
                                                          LinearForm<DecisionAtom> form) {
        Map<NumericTerm, ExactRatio> coefs = new LinkedHashMap<>();
        for (Map.Entry<DecisionAtom, ExactRatio> each : form.coefs().entrySet()) {
            TermPath place = path(head, each.getKey().ofTheAnswer().steps());
            NumericTerm term = switch (each.getKey()) {
                case DecisionAtom.OfAnAnswer _ -> new NumericTerm.ValueOf(place);
                // The number the library takes of what stands at the place, which is the term
                // the same call over a position of an input is.
                case DecisionAtom.TakenOfAnAnswer taken -> NumericTerm.TakenOf.asItStands(
                        taken.operation(), place, taken.arguments(), taken.at(),
                        subject.rules().inners(), subject.symbols());
                case DecisionAtom.ComputedOverAnAnswer computed ->
                        InputNumber.overWhatWasComputedByPosition(computed.operation(), place,
                                computed.computation(), computed.each(), computed.direction(),
                                subject.rules().inners(), subject.symbols());
                case DecisionAtom.OfTheInput _ -> throw new IllegalStateException(
                        "a demand of one answer is over what that answer holds, and "
                                + each.getKey() + " is a number of the input");
            };
            if (term == null) {
                return null;
            }
            coefs.put(term, each.getValue());
        }
        return new LinearForm<>(form.constant(), coefs);
    }
}
