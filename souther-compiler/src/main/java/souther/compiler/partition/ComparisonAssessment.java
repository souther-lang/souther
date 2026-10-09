package souther.compiler.partition;

import souther.compiler.check.DeclarationNewtypes;
import souther.compiler.check.StatedComparison;
import souther.compiler.core.Core;
import souther.compiler.coverage.Arrivals;
import souther.compiler.diag.Citation;
import souther.compiler.inputs.BlockReason;
import souther.compiler.inputs.EmptyInput;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.InputReads;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Quantities;
import souther.compiler.inputs.FilingCoordinate;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.meaning.Proposition;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.Place;
import souther.compiler.numeric.UnheldNumber;
import souther.compiler.reach.ComparisonArrival;
import souther.compiler.types.BindingId;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Objects;
import java.util.Optional;
import java.util.SequencedMap;
import java.util.function.Function;
import java.util.function.Predicate;

/**
 * What one comparison comes to on the input space: one reading, and everything read off it.
 *
 * <p><b>One decision with several projections, and not several decisions about one comparison.</b>
 * What a comparison cuts is {@link Cutting}'s one answer, taken from the canonical form the
 * arithmetic reads. What the comparison is a rule <em>about</em> used to be worked out beside that,
 * from the operands as they were written — and the two disagreed. {@code a + 1 <= 10} cut position
 * {@code a} at nine and was classified as naming no position, so a border was drawn and no
 * obligation recorded against it; {@code a <= b - b + 9} cut the same position at the same value and
 * was classified as a rule about a pair, so the question raised was about a place that rule never
 * stopped. A rule was measured by one reading and reported by the other.
 *
 * <p>So the subject is derived here, from the same value the line is, and the disagreement has
 * nowhere to live. Which positions the quantity is over decides both what the rule is about and
 * where the border goes, because both come off {@link Cutting#dividedPosition()} and it is asked
 * once.
 *
 * <p><b>And what a read comparison owes is owed by having been read.</b> The rows at the value it
 * singles out, and the rows in the classes its line makes, are asked for by the reading that found
 * the line — there is no moment at which such a demand is outstanding. So they are the partition's
 * geometry and not a coverage question standing against an answer: carried as both, one decision
 * had two representations again, and the second had no reader once it could never go unanswered.
 *
 * <p><b>Eight ways a comparison leaves the positions nothing, and they are eight.</b> Read to the
 * end and cutting nothing, naming no position at all, reading the answer, reading what a dependency
 * answered, cutting where the quantity does not run, cutting where the rows that arrive stop short,
 * cutting where the statement it is a line of never turns, and not read — each is a different
 * sentence to whoever is told it, and only the last is about a limit of this compiler. Held as one, a tautology was owed a row where the relation changes and a
 * rule this could not read was described as naming no position.
 */
sealed interface ComparisonAssessment {

    /**
     * What a comparison does to the quantity it cuts.
     *
     * <p>Read off the canonical quantity together with the operator, and read once. The operator
     * alone does not answer it: {@code 2 * a == 8} names four and {@code 2 * a == 9} names no whole
     * number at all, under one operator and one shape of rule.
     */
    enum Places {

        /** An order across the line, so rows are owed either side of it and the two sides have
         *  roles. */
        ACROSS_THE_VALUE,

        /** One value put in a class of its own, which has no sides: the values either side of it
         *  are one class. */
        AT_THE_VALUE,

        /** A value the quantity does not hold, which puts nothing in a class of its own. */
        AT_NO_VALUE
    }

    /**
     * The comparison cuts one position's own values.
     *
     * @param cutting  the line, which is what a threshold and a border are read off
     * @param position the position it divides
     * @param value    the value of the position the classes meet at, or null where the position
     *                 holds none there
     */
    record AtAPosition(Cutting cutting, NumericTerm.FromOnePosition position, Place value,
                       Places places)
            implements ComparisonAssessment {

        public AtAPosition {
            if (cutting == null || position == null || places == null) {
                throw new IllegalArgumentException("a line on a position names the position");
            }
        }
    }

    /**
     * The comparison cuts a form over more than one position, so it divides none of them.
     *
     * <p>A distance and a general form alike. What coverage asks of both is one question — no
     * position is divided, and the place is the comparison's to name — and which of the two shapes
     * the quantity is stays with the quantity.
     */
    record AcrossPositions(Cutting cutting, Citation at, Places places)
            implements ComparisonAssessment {

        public AcrossPositions {
            if (cutting == null || at == null || places == null) {
                throw new IllegalArgumentException("a line over a form names the form");
            }
        }

        /** Whether what it cuts is a number read over a run of values rather than a form over
         *  positions, which is a different thing to tell a reader who found no partition. */
        boolean overARun() {
            return cutting.of().readOverARun();
        }
    }

    /** The comparison reads what the behavior answers. */
    record AnswerDependent() implements ComparisonAssessment {}

    /**
     * The comparison is a proposition over what a dependency answered, which the decision table
     * holds as a column ({@link WhatAnAnswerTakesUp}).
     *
     * <p>Not a reading that stopped. A row stands the dependency in rather than writing what it
     * answers, so there is no line on the input space for the comparison to be — and what it
     * distinguishes is still owed rows, on the side that reads it.
     */
    record OnADependencysAnswer() implements ComparisonAssessment {}

    /** The comparison names no position of the behavior's input. */
    record NoInput() implements ComparisonAssessment {}

    /**
     * Read to the end, and the quantity it cuts is nothing: the positions cancel.
     *
     * <p>{@code filedAt} is where the rule is said to have cut nothing, and it comes off the
     * reading rather than off a second walk over the operands. What is left of the quantity is not
     * what the rule is about — {@code a - a <= 0} is about {@code a} and cuts nothing — so the
     * coordinates are the numbers the reading named, whether or not they survived, and they are the
     * numbers rather than the places they sit at ({@link AffineReading#filedAt}).
     */
    record CutsNothing(List<FilingCoordinate> filedAt) implements ComparisonAssessment {

        public CutsNothing {
            filedAt = List.copyOf(filedAt);
        }
    }

    /** Read in full, and the quantity does not run as far as the line the rule draws. */
    record OutsideTheDomain(Cutting cutting) implements ComparisonAssessment {

        public OutsideTheDomain {
            if (cutting == null) {
                throw new IllegalArgumentException("a line outside the domain is still a line");
            }
        }

        /**
         * What a place whose quantity a line does not reach is left with.
         *
         * <p>Said here once, for the two that say it: this assessment, at every coordinate of the
         * quantity it read, and the filing of a name, at the one position it moved the line to
         * and found short of it. The second is a fact about that position and not about the
         * quantity the line was moved onto, whose other coordinates the line reaches elsewhere.
         */
        static BlockReason.RuleWithoutLineReason leaves() {
            return new BlockReason.ComparisonCuttingOutsideDomain();
        }
    }

    /**
     * Read in full, the quantity runs as far as the line — and no row that arrives at the
     * comparison holds a value at it.
     *
     * <p>Its own answer and not {@link OutsideTheDomain}, which is a fact about the declarations
     * alone and holds wherever the comparison stands. This one is about the place: the guards above
     * the comparison rule the line's values out, so the classes it would make are classes of
     * nothing and the rows they would ask for are rows nothing can write. An author told the first
     * would look at the rule for a line their declarations refuse, and the line is fine — what
     * refuses it is on the way.
     *
     * <p>Only a proof lands here: the whole state at the comparison shown empty, or the region the
     * declarations, the way and what arrives leave together shown to hold no row at the line.
     */
    record NothingArrivesAtItsLine(Cutting cutting) implements ComparisonAssessment {

        public NothingArrivesAtItsLine {
            if (cutting == null) {
                throw new IllegalArgumentException(
                        "a line nothing arrives at is still a line somebody wrote");
            }
        }
    }

    /**
     * Read in full, one of several lines a statement holds together — and wherever a row arrives at
     * it, the statement comes out the same on both sides of it.
     *
     * <p>Its own answer beside {@link NothingArrivesAtItsLine}. Rows do arrive at this line; what
     * the rest of the statement leaves them is an outcome the line does not turn: {@code Int.max(a,
     * a + 1) > 5} turns where {@code a} passes four and never where it passes five, since wherever
     * {@code a} reaches five the other part already holds. An author told that the guards on the
     * way rule the line out would go looking above the rule for something that is in it.
     *
     * <p>Only a proof lands here, as there: the line with where it decides taken in, shown to hold
     * no row.
     */
    record TurnsNothing(Cutting cutting) implements ComparisonAssessment {

        public TurnsNothing {
            if (cutting == null) {
                throw new IllegalArgumentException(
                        "a line a statement never turns on is still a line of it");
            }
        }
    }

    /**
     * Read in full, and several relations held together: one rule with a line for each, and where
     * each of them decides.
     *
     * <p>One answer for the comparison, because the comparison is one rule; what each line comes to
     * on the input space is that line's own, read the way a comparison of one line is. Where a line
     * decides is carried with it and never dropped: a row at the line where it decides nothing is a
     * row the statement answers the same way on both sides, so a line taken without it would be
     * owed rows that prove nothing about it.
     */
    record Several(List<Part> parts) implements ComparisonAssessment {

        public Several {
            parts = List.copyOf(parts);
            if (parts.isEmpty()) {
                throw new IllegalArgumentException("several lines are some lines");
            }
        }

        /**
         * One line of the statement.
         *
         * @param id    which of the statement's lines it is
         * @param line  what that line comes to, which is what a comparison of one line comes to and
         *              never several again
         * @param cases where the statement turns on it, as cases any one of which is enough: every
         *              case where it was read, and once the way to it is taken in, the cases a row
         *              arriving there can be in
         */
        public record Part(PartOfAComparison id, ComparisonAssessment line,
                           List<Proposition> cases) {

            public Part {
                Objects.requireNonNull(id, "a line of a statement is one of its lines");
                cases = List.copyOf(cases);
                if (line == null || line instanceof Several) {
                    throw new IllegalArgumentException(
                            "a line of a statement is what one line comes to: " + line);
                }
            }

            /**
             * Each reading of the line, one for each case where it decides.
             *
             * <p>A line is looked for where it decides, and each case is somewhere a row can be
             * composed to be, so each is a reading of the line of its own — the way one comparison
             * a helper is called twice with is read once for each call. A row at any of them meets
             * the line, and the line is out of reach only where it is out of reach in all of them.
             */
            public List<WhereAPartDecides> readings() {
                return cases.stream().map(each -> new WhereAPartDecides(id, each)).toList();
            }
        }

        /**
         * The same statement, for a reader that has nowhere to carry where each line decides.
         *
         * <p>Every line it drew is said not to be drawn, and why: a reader composing rows against a
         * line with nothing that holds them where the line decides would be owed rows the statement
         * answers alike on both sides. A line that was refused keeps its own reason.
         */
        ComparisonAssessment withNoWayForItsParts() {
            SequencedMap<FilingCoordinate, BlockReason.RuleReadingStopped> why =
                    new LinkedHashMap<>();
            for (Part part : parts) {
                if (part.line() instanceof Unread unread) {
                    unread.why().forEach(why::putIfAbsent);
                } else {
                    cuttingOf(part.line()).over().forEach(at ->
                            why.putIfAbsent(at, new BlockReason.SeveralLinesInOneRule()));
                }
            }
            return new Unread(why);
        }
    }

    /**
     * Read in full, and the rules leave no input for any line to be about.
     *
     * <p>Its own answer and not {@link OutsideTheDomain}, which says the quantity exists and does
     * not run as far as this rule's line. Here nothing runs anywhere: the declarations reaching this
     * input admit no value at all, so neither this line nor any other is outside anything. Said as
     * the first, an author is sent to look at one rule for a contradiction that is not in it — two
     * clauses each admitting values are empty together, and neither of them is the one that failed.
     *
     * <p>Whose emptiness it is is the input's and not this comparison's. A quantity is a function of
     * the input, so a quantity's values are empty exactly when the input's are — asked of the
     * quantity, this would be a second reader deciding what the rules admit, and the two would
     * disagree about a model wherever one of them read a rule the other did not.
     */
    record NoFeasibleInput(EmptyInput why, Cutting cutting)
            implements ComparisonAssessment {

        public NoFeasibleInput {
            if (why == null || cutting == null) {
                throw new IllegalArgumentException(
                        "an input the rules leave empty is still a line somebody wrote");
            }
        }
    }

    /**
     * The comparison names a position and the reading of it stopped.
     *
     * <p>Only a reason that says a reading stopped, which the type is what enforces. A rule read to
     * the end that divides no one position has its own arms here, and their reasons say nothing
     * fell short — handed to this one, a comparison whose carrier could not be read was described
     * as relating two positions, and a model short of a border came back complete.
     *
     * <p>One reason per place and not one for the comparison. Where a reading stopped there is no
     * quantity for the places to be one subject of, so each of them says what stopped it there — a
     * position met inside an expression this did not take apart is told nothing about what it
     * carries, and one asked about for itself is.
     *
     * @param why where the reading was looking and what it left there. The places are diagnostic
     *            positions and never the subject of a question: what such a rule is about is the
     *            part that was not read
     */
    record Unread(SequencedMap<FilingCoordinate, BlockReason.RuleReadingStopped> why)
            implements ComparisonAssessment {

        public Unread {
            if (why == null || why.isEmpty()) {
                throw new IllegalArgumentException("a reading that stopped says where and why");
            }
            why = Collections.unmodifiableSequencedMap(new LinkedHashMap<>(why));
        }
    }

    /**
     * What {@code comparison} comes to, whoever wrote it.
     *
     * <p>The one way in. {@code applying} is the applications of the closures the comparison
     * stands inside, on each of which it is read. {@code answer} is the binding a clause calls what
     * the behavior answers, or
     * null where the comparison is written in a body and there is nothing to be the answer.
     * {@code dependencies} is what the decision table takes up of a body that stands dependencies
     * in, which a clause stands none of.
     *
     * <p><b>The arithmetic answers before anything else is asked.</b> Which positions a rule is
     * about is what the quantity it cuts is over: every atom of a form is a number of a location
     * ({@link souther.compiler.inputs.InputNumber}), so a comparison that came to a line is about
     * the positions of that line and there is nothing left to look up. What the walk over the
     * expression says a side is made of is the answer for a rule that came to no line — where it is
     * the only account there is — and asked first it would be a second reading standing in front of
     * the first, able to veto it and never to add to it: two members of a written list holding one
     * form written two ways agree as arithmetic and are made of different things, so the rule they
     * state would come back as one about no input at all.
     */
    static ComparisonAssessment of(String behavior, StatedComparison comparison, Citation at,
                                   InputReading read, InputReads reads,
                                   ClosureApplications applying,
                                   BindingId answer, WhatAnAnswerTakesUp dependencies,
                                   Arrivals answering,
                                   boolean drawnByAnInvariant, WhatConditionsState conditions) {
        // Asked first, and of the whole comparison. A rule that reads the answer anywhere in it is
        // one this reading does not put on the input space, whichever side the answer is on and
        // whatever else stands beside it: `value.n + query.offset <= 20` is about the answer and
        // about an input, and the input is no more measurable here for the input being named.
        if (readsAnswer(comparison.left(), answer) || readsAnswer(comparison.right(), answer)) {
            return new AnswerDependent();
        }
        Cutting.Read cut = Cutting.read(behavior, comparison, read, reads, applying, answering,
                conditions);
        return switch (cut) {
            case Cutting.Read.Cuts _, Cutting.Read.NoOrderToCountOn _,
                 Cutting.Read.NumberNoRatioHolds _ ->
                    aLine(cut, at, comparison, reads, read, drawnByAnInvariant);
            // One rule and a line for each relation it holds, each line read as a comparison of
            // one line is and carrying where it decides.
            case Cutting.Read.Several several -> new Several(several.parts().stream()
                    .map(part -> new Several.Part(part.id(), aLine(part.line(), at, comparison,
                            reads, read, drawnByAnInvariant), part.cases()))
                    .toList());
            // Read to the end and cutting nothing, which is a fact about the rule and not a limit
            // of this compiler: `a <= a` holds of every row. Where the comparison names no position
            // either, there is no rule about a position to say it of — `2 > 1` is a comparison of
            // constants and states nothing anywhere.
            case Cutting.Read.CutsNothing over -> over.filedAt().isEmpty()
                    ? aboutNoPosition(comparison, reads, read.newtypes())
                    : new CutsNothing(over.filedAt());
            // Where the reading stopped and the comparison is over what a dependency answered, it is
            // the decision table's. A number of an answer is no number of the input, so this reading
            // stops at it however the comparison was written, and the stop is about whose subject
            // the comparison is rather than about a form this compiler does not read.
            case Cutting.Read.Stopped _ when dependencies.comparison(comparison, reads) ->
                    new OnADependencysAnswer();
            // And where the reading stopped, its own answer for having stopped — decided where it
            // stopped rather than worked out again from the comparison afterwards — and where the
            // values a side holds came from, at each place it did not already answer. Here the walk
            // over the expression is the only account of what the rule is about, which is what it
            // is for.
            case Cutting.Read.Stopped stopped ->
                    besideWhereTheValuesCameFrom(stopped.why(), comparison, reads,
                            read.newtypes());
        };
    }

    /**
     * What one line comes to on the input space: the line, or the refusal to place it.
     *
     * <p>The one reading of a line, whether the comparison states one or a statement holds it
     * among several.
     */
    private static ComparisonAssessment aLine(Cutting.Read line, Citation at,
                                              StatedComparison comparison, InputReads reads,
                                              InputReading read, boolean drawnByAnInvariant) {
        return switch (line) {
            case Cutting.Read.Cuts cuts ->
                    onTheQuantity(at, cuts.cutting(), read.quantities(), drawnByAnInvariant);
            // And where the quantity was read and stands on no order this counts, the carrier is
            // what a reader is owed — at the quantity's own coordinates, because the quantity is
            // what such a rule is about. The word is what the reading established and not what is
            // left when several answers were absent: it says the values here carry no order to
            // draw a line on, and that is exactly what was found.
            case Cutting.Read.NoOrderToCountOn over -> over.over().isEmpty()
                    ? aboutNoPosition(comparison, reads, read.newtypes())
                    : new Unread(atEachOf(over.over(),
                            new BlockReason.UnreadComparisonDomain()));
            // And where the quantity was read, counts, and draws a line that falls at a number no
            // exact ratio holds. The same coordinates as the case above and a reason of its own:
            // what stopped it is a constant the rule is written with, and not the order beneath.
            case Cutting.Read.NumberNoRatioHolds over -> over.over().isEmpty()
                    ? aboutNoPosition(comparison, reads, read.newtypes())
                    : new Unread(atEachOf(over.over(),
                            new BlockReason.LineAtANumberNoRatioHolds()));
            case Cutting.Read.CutsNothing _, Cutting.Read.Stopped _, Cutting.Read.Several _ ->
                    throw new IllegalArgumentException("one line is drawn or refused: " + line);
        };
    }

    /**
     * The same reading, on the narrower domain the run leaves at the comparison's line.
     *
     * <p>The declarations first and the place second, because the two are different sentences and
     * the first holds wherever the comparison stands. What is asked here is the same predicate on
     * the narrower domain, not a second reading of the rule — so a line the declarations already
     * dropped is not asked about again, and what arrives cannot put one back.
     *
     * <p><b>Apart from the reading, because the two are read off different trees.</b> What the rule
     * states is read where the language's operations stand; what arrives at a place is read where
     * they are expanded, which is where a run has places at all. Asked inside the reading, the
     * reading would be one no tree could answer on its own.
     *
     * <p><b>One question, asked of everything that holds of a row there at once.</b> A row at the
     * line is in what the declarations leave, meets every condition the model states on the way,
     * and is among what arrives at the place it is watched at — so the line stands where a region
     * holding all three holds a row at it. Asked of each of them alone, a row the way holds a
     * position apart from would be one the arrival's range runs straight through, and a line
     * nothing reaches would stand.
     *
     * <p>The way is the model's and what arrives is each place's. The model states the conditions
     * once, on the tree an author wrote; the places are where the tree that runs holds the rule, and
     * what the walk of that tree established on the way to one of them is that place's alone.
     *
     * <p>Only a proof drops a line. An arrival nothing could project restricts nothing beyond what
     * the declarations and the way leave ({@link ComparisonArrival.NoProjection}) — and it is not
     * what a comparison the emitter numbered nothing for says, because that one is not asked this
     * at all.
     *
     * <p><b>A line of several is asked on the way and then in each case where it decides.</b> On
     * the way alone, a line nothing arrives at is that, as a line of one is. Then each case: the
     * ones no arriving row can be in are dropped, and a line rows arrive at where no case leaves
     * one is a line the statement never turns on, which is a fact about the statement and not
     * about the way ({@link TurnsNothing}).
     *
     * @param way         what the model states on the way to the comparison, over what the
     *                    declarations leave
     * @param wayToAPart  the same, with one case of where a line of a statement of several
     *                    decides taken in beside it
     */
    static ComparisonAssessment narrowedByWhatArrives(
            ComparisonAssessment read,
            Reachability way,
            Function<WhereAPartDecides, Reachability> wayToAPart,
            List<ComparisonArrival> arrivals,
            boolean drawnByAnInvariant) {
        if (read instanceof Several several) {
            return new Several(several.parts().stream()
                    .map(part -> aPartNarrowed(part, way, wayToAPart, arrivals,
                            drawnByAnInvariant))
                    .toList());
        }
        Cutting cutting = switch (read) {
            case AtAPosition at -> at.cutting();
            case AcrossPositions across -> across.cutting();
            // Every other reading is one the declarations settled without reaching a line, and
            // there is nothing for a narrower domain to settle differently.
            default -> null;
        };
        // A rule watched nowhere is not asked this. What the places are is
        // {@link souther.compiler.coverage.EmittedComparisonState.Instrumented}, which is never
        // empty, and a comparison the emitter numbered nothing for is the other arm of that and
        // never reaches here. Answered with none, "all of them proved nothing arrives" is true of
        // no place at all, and the line would go for want of a proof rather than by one.
        if (arrivals.isEmpty()) {
            throw new IllegalArgumentException(
                    "a rule watched at no place is not one to ask what arrives at: " + read);
        }
        if (cutting == null) {
            return read;
        }
        return arrivesAtSomePlace(cutting, way, arrivals,
                region -> cutting.reachedIn(region, drawnByAnInvariant))
                ? read : new NothingArrivesAtItsLine(cutting);
    }

    /**
     * Whether some place the rule is watched at leaves {@code asked} true of the region a row
     * arriving there is in.
     *
     * <p>A way no row takes is one no row arrives at the line by, wherever the tree that runs holds
     * the rule. Otherwise every place the rule is watched at, and the answer is no only where all of
     * them proved it. One rule may be written into the tree that runs more than once, and a run
     * through any of the copies is a run through the rule — so a proof about one of them is a proof
     * about that copy, and the line is what the model states about all of them.
     *
     * <p>Which is why one place that could not be projected leaves the question to the declarations
     * and the way: what a walk did not settle is not a proof that nothing arrives, and a line has to
     * be dropped by a proof rather than by the absence of one.
     */
    private static boolean arrivesAtSomePlace(Cutting cutting, Reachability way,
                                              List<ComparisonArrival> arrivals,
                                              Predicate<SearchRegion> asked) {
        if (!(way instanceof Reachability.Reaching reaching)) {
            return false;
        }
        for (ComparisonArrival arrival : arrivals) {
            boolean reaches = switch (arrival) {
                case ComparisonArrival.NothingArrives _ -> false;
                case ComparisonArrival.Values values ->
                        asked.test(cutting.narrowedBy(values, reaching.region()));
                case ComparisonArrival.NoProjection _ -> asked.test(reaching.region());
            };
            if (reaches) {
                return true;
            }
        }
        return false;
    }

    /** One line of a statement of several, on the way and then in each case where it decides. */
    private static Several.Part aPartNarrowed(Several.Part part, Reachability way,
                                              Function<WhereAPartDecides, Reachability> wayToAPart,
                                              List<ComparisonArrival> arrivals,
                                              boolean drawnByAnInvariant) {
        ComparisonAssessment arrived = narrowedByWhatArrives(part.line(), way, _ -> way, arrivals,
                drawnByAnInvariant);
        // Only where it is a line at all: a line refused, outside what the declarations leave, or
        // one nothing arrives at, is that whatever the cases are.
        if (!(arrived instanceof AtAPosition || arrived instanceof AcrossPositions)) {
            return new Several.Part(part.id(), arrived, part.cases());
        }
        // Each case where a row on each side of the line can stand in it. Rows on the two sides in
        // one case differ in this line alone, so the statement turns between them; a case only one
        // side has rows in is a case crossing the line leaves, and turns nothing there.
        Cutting cutting = cuttingOf(arrived);
        List<Proposition> reached = new ArrayList<>();
        for (WhereAPartDecides each : part.readings()) {
            if (arrivesAtSomePlace(cutting, wayToAPart.apply(each), arrivals,
                    cutting::crossedIn)) {
                reached.add(each.decides());
            }
        }
        return reached.isEmpty()
                ? new Several.Part(part.id(), new TurnsNothing(cutting), List.of())
                : new Several.Part(part.id(), arrived, reached);
    }

    /**
     * The line {@code line} is about, where it is one line's answer and is about one.
     */
    private static Cutting cuttingOf(ComparisonAssessment line) {
        return switch (line) {
            case AtAPosition at -> at.cutting();
            case AcrossPositions across -> across.cutting();
            case OutsideTheDomain outside -> outside.cutting();
            case NothingArrivesAtItsLine unarrived -> unarrived.cutting();
            case TurnsNothing turns -> turns.cutting();
            case NoFeasibleInput none -> none.cutting();
            case AnswerDependent _, OnADependencysAnswer _, NoInput _, CutsNothing _, Unread _,
                 Several _ -> throw new IllegalArgumentException(
                         "a reading that drew no line is about none: " + line);
        };
    }

    /**
     * One answer at every one of {@code places}, kept in the order they were given.
     *
     * <p>Sound where the places are one subject: the coordinates of one quantity, or the places a
     * statement nothing read at all names. A reading that stopped has no such subject, and its
     * places are answered one at a time where it stopped.
     */
    static <R extends BlockReason.RuleWithoutLineReason> SequencedMap<FilingCoordinate, R>
            atEachOf(List<FilingCoordinate> places, R why) {
        SequencedMap<FilingCoordinate, R> out = new LinkedHashMap<>();
        places.forEach(each -> out.putIfAbsent(each, why));
        return out;
    }

    /**
     * What a comparison naming no position of the input comes to.
     *
     * <p>Two answers and not one. A comparison of constants is about nowhere, and there is nothing
     * for a sentence about a position to be about. A comparison over values an operation answered
     * is about somewhere — the position those values came from — and what the rule says about the
     * values <em>there</em> is what would take inverting whatever the operation did. Held alike,
     * the second went out as a rule about nothing, and the position it plainly concerns came back
     * as one the model states nothing about.
     */
    private static ComparisonAssessment aboutNoPosition(StatedComparison comparison,
                                                        InputReads reads,
                                                        DeclarationNewtypes newtypes) {
        return besideWhereTheValuesCameFrom(new LinkedHashMap<>(), comparison, reads, newtypes);
    }

    /**
     * What a reading that stopped comes to: what it left at each place it was filed at, and at each
     * place the values a side holds came from that it was not.
     *
     * <p>Two facts about two places, and neither is asked to say the other. In
     * {@code c >= atLeast} with {@code c} an element of {@code Set.map(x -> x + 1, cs)}, the
     * reading is filed at {@code atLeast}, whose own values the rule is about, and what that place
     * is left with is that place's
     * ({@link souther.compiler.check.UnreadComparison#whereItStopped}). That the rule is about a
     * value made from {@code cs} is a fact about {@code cs}, and asked only where the comparison is
     * filed nowhere, it would be said of no place at all.
     *
     * <p>A place already answered keeps its answer: there is one word for a place, and the reading
     * that stopped there is what decided it.
     */
    private static ComparisonAssessment besideWhereTheValuesCameFrom(
            SequencedMap<FilingCoordinate, BlockReason.RuleReadingStopped> filed,
            StatedComparison comparison, InputReads reads, DeclarationNewtypes newtypes) {
        SequencedMap<FilingCoordinate, BlockReason.RuleReadingStopped> why =
                new LinkedHashMap<>(filed);
        GuardThresholds.cameFrom(comparison, reads, newtypes, why);
        return why.isEmpty() ? new NoInput() : new Unread(why);
    }

    /** What a line comes to on the input space, from the quantity it is on. */
    private static ComparisonAssessment onTheQuantity(
            Citation at, Cutting cutting, Quantities quantities,
            boolean drawnByAnInvariant) {
        // Whether there is an input at all, before anything is asked about where its values run.
        // A quantity is a function of the input, so where the rules admit no input they admit no
        // value of any quantity — and every question below is about one quantity's values against
        // one rule's line, which is a question about a model that has some.
        Optional<EmptyInput> empty = quantities.emptiness();
        if (empty.isPresent()) {
            return new NoFeasibleInput(empty.get(), cutting);
        }
        // The line is placed, and what stands beside it is asked here, once. A rule that could not
        // be told where the values part is neither a rule drawing nowhere nor one drawing
        // somewhere: it is one whose sides were not worked out, and it is said so at the position
        // rather than read as less. Every reader of the line below holds the seam this asked for.
        ExactAnswer<Seam> parted = cutting.seam();
        if (parted instanceof ExactAnswer.Unheld<Seam> unheld) {
            return sideNotWorkedOut(cutting, unheld.why());
        }
        // The line and not one of its points. A rule drawing where the quantity never reaches
        // divides the position into nothing, and a reader told that the rule went unread would go
        // looking for a limit of this compiler that is not there.
        if (!cutting.reachedIn(quantities.region(), drawnByAnInvariant)) {
            return new OutsideTheDomain(cutting);
        }
        ExactAnswer<Places> places = places(cutting);
        if (places instanceof ExactAnswer.Unheld<Places> unheld) {
            return sideNotWorkedOut(cutting, unheld.why());
        }
        Places kind = ((ExactAnswer.Held<Places>) places).value();
        NumericTerm.FromOnePosition divided = cutting.dividedPosition();
        if (divided == null) {
            // Named by the comparison that drew it, which is the one thing about such a place this
            // compiler can always say exactly. It is on no position, and writing it out would be as
            // much of it as a pretty-printer got.
            return new AcrossPositions(cutting, at, kind);
        }
        Seam seam = ((ExactAnswer.Held<Seam>) parted).value();
        ExactAnswer<Optional<Place>> value = cutting.singles() ? cutting.singledValue(seam)
                : ExactAnswer.held(cutting.dividedValue(seam));
        return switch (value) {
            case ExactAnswer.Unheld<Optional<Place>> unheld ->
                    sideNotWorkedOut(cutting, unheld.why());
            case ExactAnswer.Held<Optional<Place>> held ->
                    new AtAPosition(cutting, divided, held.value().orElse(null), kind);
        };
    }

    /** A rule whose line is placed and whose sides were not worked out, said at every place the
     *  quantity is filed at. */
    private static ComparisonAssessment sideNotWorkedOut(Cutting cutting, UnheldNumber why) {
        return new Unread(atEachOf(cutting.over(), new BlockReason.LineSideNotWorkedOut(why)));
    }

    /**
     * What the rule does to the quantity, from the canonical quantity and the operator together.
     *
     * <p>Not from the operator alone. {@code 2 * a == 8} names four and {@code 2 * a == 9} names no
     * whole number at all, under one operator: whether the value the rule wrote is one the quantity
     * holds is the quantity's answer, and it is asked of the quantity.
     *
     * <p>Asked of whether a value of a <em>position</em> could be written instead, a form over
     * several positions has none at all — so {@code a + b == 10}, which takes ten, came back naming
     * no value the quantity holds, alongside {@code 2 * a + 2 * b == 9}, which does not.
     */
    private static ExactAnswer<Places> places(Cutting cutting) {
        if (!cutting.singles()) {
            return ExactAnswer.held(Places.ACROSS_THE_VALUE);
        }
        return cutting.takesTheValueItNames().map(takes ->
                takes ? Places.AT_THE_VALUE : Places.AT_NO_VALUE);
    }

    /**
     * Where a reader is sent for what this leaves the positions with, or empty where it leaves them
     * nothing.
     *
     * <p><b>Whose answer it is turns on whether the quantity was reached.</b> A rule that was read
     * is about its quantity, so the positions it is filed at are the quantity's — {@code a + b - b
     * + c <= 10} is {@code a + c <= 10}, and a note at {@code b} would say the rule relates a
     * position it does not mention. A reading that stopped has no quantity to be about, so the
     * positions the walk met are the whole of what can be said, and nothing here may be read as
     * what the rule is about.
     *
     * <p>A quantity that came out empty is the third: there are no coordinates to file at, and the
     * positions the comparison names are what makes {@code a <= a} worth saying at all — the model
     * names a position there and cuts nothing.
     *
     * <p>Answered here so that no caller chooses. Chosen at the two producers, one of them reached
     * for the walk's positions because that was the helper in hand, and a rule read from end to end
     * was filed at a position its arithmetic had cancelled.
     *
     * <p>Asked of nothing. Each case was filed where it was read and holds where; a comparison, an
     * environment and the module's names are what it takes to work that out, and working it out is
     * not what happens here.
     */
    default List<FilingCoordinate> filedAt() {
        return switch (this) {
            case AcrossPositions over -> over.cutting().over();
            case OutsideTheDomain outside -> outside.cutting().over();
            case NothingArrivesAtItsLine unarrived -> unarrived.cutting().over();
            case TurnsNothing turns -> turns.cutting().over();
            // The positions its quantity is over, as every read rule's are. That the rules leave
            // the input empty says nothing about which positions this rule is about.
            case NoFeasibleInput none -> none.cutting().over();
            case Unread unread -> List.copyOf(unread.why().keySet());
            case CutsNothing cuts -> cuts.filedAt();
            // Where each of its lines is filed, each place once: one rule, and its lines are what
            // it is about.
            case Several several -> several.parts().stream()
                    .flatMap(part -> part.line().filedAt().stream())
                    .distinct()
                    .toList();
            case AtAPosition _, AnswerDependent _, OnADependencysAnswer _, NoInput _ -> List.of();
        };
    }

    /**
     * What the reading of lines leaves at each place this comparison is filed at, and empty where
     * it leaves nothing.
     *
     * <p><b>Named for the reading it is the answer of, and not for the assessment it is read
     * off.</b> What a comparison comes to is one decision; what a reading makes of it is that
     * reading's own, and the two do not agree even about one comparison — a rule relating two
     * positions is read here from end to end and places no line, and the reading that turns clauses
     * into sets of values gets nothing it can hold from the same rule. A name saying only that a
     * reason was read off an assessment would be reached for by that reader too, and the answer it
     * would take is the one that says nothing fell short.
     *
     * <p><b>Per place, and the same at every place only where the places are one subject.</b> A
     * comparison whose arithmetic reached a quantity is about that quantity, so its places are the
     * quantity's coordinates and one answer holds at all of them. A reading that stopped has no
     * quantity to be about, and each place it was left at says what stopped it there — handed one
     * answer, a position met inside an expression this did not take apart was told what another
     * position's carrier carries.
     *
     * <p>Answered once, here. Both producers of this evidence — a clause of an {@code ensures} and a
     * {@code guard}'s comparison — worked the same table out separately, so a case added to
     * {@link ComparisonAssessment} had to be answered twice and the two could disagree about one
     * comparison. That is the shape this whole type was made to have none of.
     *
     * <p><b>Once per place for a comparison of one line, and once per line for a statement of
     * several.</b> Each line of {@code Int.max(a, a + b) > 5} is its own: the one on the sum relates
     * two positions, and the one on {@code a} is never turned on — two things about one place, and
     * a place told only the first would hide a line of the rule.
     *
     * <p>Empty rather than null, and no {@code default} on the switch. A comparison that drew a
     * line, one about no position of the input, and one about what the behavior answers each leave
     * nothing for a reader to be told, and saying so with an absent value made the absence a
     * sentinel one caller had to remember to test for. An arm added is a compile error in this
     * method and in the value reading's own beside it, which is the point of neither having a
     * default.
     */
    default List<LeftAt> whatEachPlaceIsLeftWith() {
        return switch (this) {
            // Which of the two a form that divides nothing is: a line over a run is one number and
            // one line with no position under it, and a line over several positions is a relation
            // between them. Answered from what the quantity is over rather than by the count of its
            // terms, since a form of one term is either.
            case AcrossPositions across -> sameAtEachPlace(across.overARun()
                    ? new BlockReason.ComparisonOverARun()
                    : new BlockReason.ComparisonBetweenPositions());
            case CutsNothing _ -> sameAtEachPlace(new BlockReason.ComparisonCuttingNothing());
            case OutsideTheDomain _ -> sameAtEachPlace(OutsideTheDomain.leaves());
            // Not the reason above: there the declarations never run as far as the line, and here
            // they do — what stops short of it is the values that arrive at the comparison, ruled
            // out by the guards on the way. An author reading the first would look at one rule for
            // a contradiction with their declarations that is not in it.
            case NothingArrivesAtItsLine _ ->
                    sameAtEachPlace(new BlockReason.ComparisonNothingArrivesAtItsLine());
            // Nor that one: rows arrive at this line, and the statement it is a line of comes out
            // the same either side of it wherever they do.
            case TurnsNothing _ ->
                    sameAtEachPlace(new BlockReason.ComparisonLineTurningNothing());
            // What each of its lines leaves, each in its own words — and nothing at a position
            // another of its lines divides, since the rule divides it.
            case Several several -> {
                List<FilingCoordinate> divided = several.parts().stream()
                        .filter(part -> part.line() instanceof AtAPosition)
                        .flatMap(part -> cuttingOf(part.line()).over().stream())
                        .toList();
                yield several.parts().stream()
                        .flatMap(part -> part.line().whatEachPlaceIsLeftWith().stream())
                        .filter(left -> !divided.contains(left.at()))
                        .distinct()
                        .toList();
            }
            // Its own answer for having stopped, decided where it stopped and at each place it was
            // left at. Worked out again from the comparison afterwards, one whose carrier stopped
            // the reading came back as a rule that relates two positions — a sentence saying no
            // measure is short of anything, over a model missing a border.
            case Unread unread -> unread.why().entrySet().stream()
                    .map(each -> new LeftAt(each.getKey(), each.getValue()))
                    .toList();
            // Nothing about this rule fell short, and nothing about this rule is what happened. The
            // rules of the input admit no value between them, which is one fact about the behavior
            // and not one per rule at each position it names — said here, a model with two clauses
            // and four positions would be told eight times, and each time about a rule that is not
            // the one at fault.
            case NoFeasibleInput _, AtAPosition _, NoInput _, AnswerDependent _ -> List.of();
            // Read by the decision table, which owes the rows it distinguishes. Left here as a
            // place, it would be a rule that reading named reported as one nobody read.
            case OnADependencysAnswer _ -> List.of();
        };
    }

    /**
     * One place a comparison is filed at, and what the reading of lines leaves there.
     *
     * @param at  the place
     * @param why what is left there, in the words of the line that left it
     */
    record LeftAt(FilingCoordinate at, BlockReason.RuleWithoutLineReason why) {

        public LeftAt {
            Objects.requireNonNull(at, "something is left somewhere");
            Objects.requireNonNull(why, "something left somewhere is left for a reason");
        }
    }

    /** The same answer at every place this is filed at, which are one quantity's coordinates. */
    private List<LeftAt> sameAtEachPlace(BlockReason.RuleWithoutLineReason why) {
        return leftAtEachOf(filedAt(), why);
    }

    /** {@code why} at every one of {@code places}, each once, in the order they were given. */
    static List<LeftAt> leftAtEachOf(List<FilingCoordinate> places,
                                     BlockReason.RuleWithoutLineReason why) {
        return places.stream().distinct().map(at -> new LeftAt(at, why)).toList();
    }

    /**
     * Whether this line is one a border is built on.
     *
     * <p>Only where the rule orders the values around it. A value singled out has no sides — the
     * values either side of it are one class — so there is nothing for a border to owe a row away
     * from, and a rule that names a value the quantity does not hold names no place at all.
     */
    default boolean drawsABorder() {
        return switch (this) {
            case AtAPosition at -> at.places() == Places.ACROSS_THE_VALUE;
            case AcrossPositions over -> over.places() == Places.ACROSS_THE_VALUE
                    || (over.places() == Places.AT_THE_VALUE
                            && over.cutting().of().singlesWithSides());
            case Several several -> several.parts().stream()
                    .anyMatch(part -> part.line().drawsABorder());
            case AnswerDependent _, OnADependencysAnswer _, NoInput _, CutsNothing _,
                 OutsideTheDomain _, TurnsNothing _,
                 NothingArrivesAtItsLine _, NoFeasibleInput _, Unread _ -> false;
        };
    }

    /**
     * Whether anything in {@code e} reads the binding a rule calls the answer.
     *
     * <p>A mechanical predicate over the tree, and it classifies nothing by itself. Two readers ask
     * it and reach different conclusions: {@link #of} answers that the comparison raises no
     * input-coverage obligation, and {@link EnsuresThresholds} answers that a rule about the answer
     * is not one this compiler failed to read. Written twice, the two came apart — the second had
     * the predicate and the first did not — so it is written once and neither reader owns what the
     * other makes of it.
     *
     * <p>Syntactic. {@code value.n - value.n + query.limit.value <= 20} does not depend on the
     * answer once the arithmetic is read, and this answers that it does. The atoms of the canonical
     * form are the input's positions, so the arithmetic cannot see through a read of the answer at
     * all; a predicate that quietly did some of the cancelling would be a second reading of the
     * comparison, which is the shape this whole assessment is written against.
     *
     * <p>False where there is no answer to read, which is every comparison written in a body.
     */
    static boolean readsAnswer(Core e, BindingId answer) {
        if (answer == null) {
            return false;
        }
        if (e instanceof Core.Read read && answer.equals(read.binding())) {
            return true;
        }
        boolean[] found = {false};
        Core.forEachChild(e, child -> found[0] |= readsAnswer(child, answer));
        return found[0];
    }
}
