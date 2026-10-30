package souther.compiler.partition;

import souther.compiler.check.Carrier;
import souther.compiler.check.StatedComparison;
import souther.compiler.check.ComparisonClaim;
import souther.compiler.check.NonAffineOperation;
import souther.compiler.core.Core;
import souther.compiler.coverage.Arrivals;
import souther.compiler.inputs.BlockReason;
import souther.compiler.inputs.FilingCoordinate;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.InputReads;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Quantities;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.inputs.TermOrders;
import souther.compiler.inputs.TermPath;
import souther.compiler.types.ExpansionLineage;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Place;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.numeric.Towards;
import souther.compiler.meaning.AuthoredPointMapping;
import souther.compiler.meaning.AuthorsLines;
import souther.compiler.meaning.CountsWrittenOut;
import souther.compiler.meaning.DecidingCase;
import souther.compiler.meaning.DecisionAtom;
import souther.compiler.meaning.DecisionSubject;
import souther.compiler.meaning.Derivation;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.Quantity;
import souther.compiler.meaning.Relation;
import souther.compiler.meaning.Spelling;
import souther.compiler.meaning.WhereARunStops;
import souther.compiler.meaning.WhereAnApplicationIsMade;
import souther.compiler.meaning.WhereEachLineDecides;
import souther.compiler.meaning.WhyUnread;
import souther.compiler.meaning.WrittenLine;
import souther.compiler.meaning.WrittenLines;
import souther.compiler.reach.ComparisonArrival;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collections;
import java.util.EnumSet;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.SequencedMap;
import java.util.Set;
import java.util.function.Function;
import java.util.function.Supplier;
import java.util.function.UnaryOperator;
import java.util.stream.Stream;

/**
 * What one comparison cuts, and where — the one place that decides it.
 *
 * <p><b>One decision, so that a rule is read the same way wherever it is written.</b> Which quantity
 * a comparison cuts was settled in three places, each reading a little more of the language than the
 * last and each turning the form round or not on its own: a rule written {@code 48 >= 3a + 6b} drew
 * its border on {@code -3a - 6b}, and the {@code ensures} side called two of the three readings and
 * so read no form at all. That is the shape this whole reading was written to stop, one level up
 * from where it was found.
 *
 * <p><b>What the comparison states, and never how it was written.</b> The statement read once
 * ({@link Pullback#ofAComparison}) says which quantity the rule cuts — a form over the input's
 * numbers, or one number against a place on the order it stands on, which is how a date against a
 * written date and a case of an enumeration are stated — and what is left to decide here is whether
 * this compiler can realize a line on the order that quantity is on. {@code a <= a} states nothing
 * that varies, so it cuts nothing, however its operands are written.
 *
 * <p>Which levels the order has a place at is the order's own answer ({@link LevelSpace#canCutAt}).
 * Asked of the carrier instead — "do these values count" — two strings, which stand no measurable
 * distance apart and are still one above the other, were left with no line at the place they meet.
 *
 * @param of     what the rule cuts
 * @param at     where on it
 * @param claim  what the operator states about the threshold's own value
 * @param within what the rules leave the quantity itself. Three times a length is never negative,
 *               and a threshold outside where a quantity runs is one the rule draws no border at.
 *               Asked of every quantity alike, since what a quantity runs between is a question
 *               about the quantity
 * @param written the number the comparison was written against, where one of its sides is a number
 *               the same on every run and the other is not: the table bound of a lookup, before the
 *               quantity it is held against was weighed and divided into the level above
 * @param heldIn the data the number the comparison is held against is read out of, where it is
 *               read out of data: the table a helper was handed, which is written once however
 *               alike the bounds of another table are
 */
record Cutting(BorderQuantity of, Level at, ComparisonClaim claim,
               NumericDomain.Bounds within, Optional<ExactRatio> written,
               Optional<BoundHeldIn> heldIn) {

    Cutting {
        Objects.requireNonNull(written, "a number is written against, or none is");
        Objects.requireNonNull(heldIn, "a bound is held in data, or in none");
    }

    Cutting(BorderQuantity of, Level at, ComparisonClaim claim, NumericDomain.Bounds within) {
        this(of, at, claim, within, Optional.empty(), Optional.empty());
    }

    Cutting(BorderQuantity of, Level at, ComparisonClaim claim, NumericDomain.Bounds within,
            Optional<ExactRatio> written) {
        this(of, at, claim, within, written, Optional.empty());
    }

    /** This line as a comparison written against {@code level}. */
    Cutting writtenAgainst(Optional<ExactRatio> level) {
        return new Cutting(of, at, claim, within, level, heldIn);
    }

    /** This line as a comparison whose bound is held in {@code data}. */
    Cutting heldIn(Optional<BoundHeldIn> data) {
        return new Cutting(of, at, claim, within, written, data);
    }

    /**
     * What reading {@code comparison} as a line came to.
     *
     * <p>Four answers, and the three that are not a line are not one absence. A comparison whose
     * positions cancel was read from end to end and there was no line in it; one this compiler
     * could not take apart leaves whatever it states unknown; and one whose quantity was read and
     * stands on no order this counts is neither. Told apart by a {@code null}, whoever asked had to
     * work out which — and worked it out by reading the comparison a second time, which is how a
     * rule read in full came to be described as one whose spelling defeated this compiler.
     *
     * <p>Each of them says what was found rather than what came of it. An arm named for the absence
     * of a line holds every way of failing to draw one, so the next one added goes out under the
     * word the last one earned.
     */
    sealed interface Read {

        /**
         * The line it draws.
         *
         * @param authored how the line stands to the line of its author's it is a place of: the
         *                 author's line put on the input, facing the sides the comparison wrote a
         *                 known way or none, or a place the statement turns that is not shown to be
         *                 it ({@link AuthoredPointMapping}). Drawn off a relation, it is that
         *                 relation's line until the reading that took the statement apart says which
         *                 of its author's lines the relation is a place of and how
         */
        record Cuts(Cutting cutting, AuthoredPointMapping authored) implements Read {

            public Cuts {
                Objects.requireNonNull(cutting, "a comparison that cuts has a line");
                Objects.requireNonNull(authored, "and stands to its author's line some way");
            }

            /** The line, as the relation it was drawn off states it. */
            Cuts(Cutting cutting) {
                this(cutting, new AuthoredPointMapping.Proven(WrittenLine.THE_COMPARISON,
                        cutting.claim(), Derivation.AComparisonRead.Facing.NOTHING_WRITTEN, true));
            }
        }

        /**
         * Read to the end, a relation between numbers of the input and a value no position holds:
         * what the body named a value an operation looked up, an element of what a walk was
         * handed, the index a walk is at.
         *
         * <p>A fact about the rule and not a reading that stopped. Every part of what it states was
         * read, and nothing that value was made from stopped a reading; where it falls on the
         * input's numbers moves with the other value from run to run, so it divides none of them —
         * as a relation between two positions does not.
         *
         * <p>That it divides none of them is shown only where the other value reaches every value
         * at the coordinate ({@link UndividedByARelation}): {@code n == String.length(s)} is false
         * wherever {@code n} is below nought, which the length never reaches.
         *
         * @param over      the coordinates of the input's numbers it relates
         * @param relations what it states, one relation for each reading of it — a closure's
         *                  statement is read once for each application
         */
        record AgainstAnotherValue(List<FilingCoordinate> over,
                                   List<UndividedByARelation> relations) implements Read {

            public AgainstAnotherValue {
                over = List.copyOf(over);
                relations = List.copyOf(relations);
                if (over.isEmpty() || relations.isEmpty()) {
                    throw new IllegalArgumentException(
                            "a relation against another value relates some number of the input");
                }
            }
        }

        /** Read to the end, and the same answer for every row, filed where {@link #settledAt}
         *  says: {@code a - a <= 0} is about {@code a} however much of it cancelled, and
         *  {@code 2 > 1} is about nothing. */
        record CutsNothing(List<FilingCoordinate> filedAt) implements Read {

            public CutsNothing {
                filedAt = List.copyOf(filedAt);
            }
        }

        /**
         * Read to the end, and every run that reaches the comparison stops in an operation it is
         * read through, such as a division by nought: it states nothing on either side.
         *
         * <p>A fact about the rule and not a reading that stopped, and not a comparison that
         * settles the same for every row ({@link CutsNothing}): there a run gets past it, and here
         * none does.
         *
         * @param filedAt where the rule is said to answer nowhere, as it is for
         *                {@link CutsNothing}
         */
        record AnswersNowhere(List<FilingCoordinate> filedAt) implements Read {

            public AnswersNowhere {
                filedAt = List.copyOf(filedAt);
            }
        }

        /**
         * Read to the end, a statement of which case, which truth or whether a value positions of
         * the input hold, or of some element of a container the input holds meeting that, with no
         * relation of numbers anywhere in it ({@link #statesNoRelation}).
         *
         * <p>What an application stating the same is, and not a reading that stopped: there is no
         * line for it to be, and what it tells apart is the decision table's to owe rows for.
         * {@code length(filter(p, written)) == 1} over a list written out comes to some choice of
         * which of the statements about its values hold, and where those are about which cases
         * the input's elements are, the comparison states what {@code List.all} and
         * {@code List.any} written over those cases would.
         */
        record StatesNoRelation() implements Read {}

        /**
         * The arithmetic stopped, and this is what it leaves at each place it is filed at.
         *
         * <p>A map and not one reason, because the places are not one subject. Where the arithmetic
         * stopped, each place the walk met is a separate question — a position met inside an
         * expression this did not take apart says nothing about what that position carries — and
         * one answer handed to all of them told a position about the carrier of another.
         */
        record Stopped(SequencedMap<FilingCoordinate, BlockReason.RuleReadingStopped> why)
                implements Read {

            public Stopped {
                why = Collections.unmodifiableSequencedMap(new LinkedHashMap<>(why));
            }
        }

        /**
         * The quantity was read, and there is no order this compiler can realize it as a count on.
         *
         * <p><b>Named for what was found and not for what came of it.</b> "No line was built" is
         * true of every way of failing to build one, so an arm carrying that name takes the next
         * one added to it — and the word a document then prints was decided by whichever answers
         * happened to be absent rather than by anything anybody established.
         *
         * <p>What is established here is one thing: some term of the form stands on no order, or on
         * one whose values do not count, so a sum over the terms has nothing to be spaced by
         * ({@link AffineReading#carriers}). A line on a single position and a distance between two
         * are asked before this and reach orders this does not — two strings stand no measurable
         * distance apart and are still one above the other — so what is left here is the general
         * form, and the general form is what needs every term to count.
         *
         * <p>Its own answer and not {@link Stopped}. Nothing about the form fell short — it is
         * right here — so the quantity is the subject and the places are its own, which is what
         * every read comparison's are. Said as a reading that stopped, the places would come from a
         * walk over the operands, and which of two authorities a comparison's places came from
         * would turn on which producer built the answer.
         *
         * @param over the coordinates of the quantity, which is where a reader is sent
         */
        record NoOrderToCountOn(List<FilingCoordinate> over) implements Read {

            public NoOrderToCountOn {
                over = List.copyOf(over);
            }
        }

        /**
         * The rule states a line, and a number that line is read through has no representation
         * here: the coefficients over what they share, or the place the line falls at in the
         * quantity's own units, stand past the far end of the exponents a ratio holds.
         *
         * <p>Its own answer beside {@link NoOrderToCountOn}. Nothing about the quantity's order
         * fell short — it counts, and the rule is read to the end — so the order is not what a
         * reader is told about, and a line placed at a number this compiler cannot name is not one
         * it can be said to have drawn.
         *
         * @param over the coordinates of the quantity, which is where a reader is sent
         */
        record NumberNoRatioHolds(List<FilingCoordinate> over) implements Read {

            public NumberNoRatioHolds {
                over = List.copyOf(over);
            }
        }

        /**
         * Read to the end, and several relations held together: one rule, with a line for each.
         *
         * <p>Each line is one this compiler draws only where the statement turns on it, and where
         * that is is carried with the line ({@link Part#cases}) rather than worked out by whoever
         * meets it: it is read off what the statement states, and what meets a line afterwards
         * holds the line and not the statement.
         */
        record Several(List<Part> parts) implements Read {

            public Several {
                parts = List.copyOf(parts);
                if (parts.isEmpty()) {
                    throw new IllegalArgumentException("several lines are some lines");
                }
            }

            /**
             * One relation of the statement.
             *
             * @param id    which of the author's lines it is a place of, and which place
             * @param line  the line it draws, or the refusal to place it; or, where the relation is
             *              no line, what it relates the input's numbers to
             *              ({@link AgainstAnotherValue}); or, where it is a line and a row cannot
             *              be asked whether it is somewhere the line decides, the line not drawn
             *              ({@link Stopped}, at the line's places)
             * @param cases where the statement turns on it, as cases any one of which is enough;
             *              empty where it turns on it nowhere, and for what is no line drawn or
             *              refused. A relation to another value draws no line of its own, and has
             *              cases where the lines parting the values that settle it may be drawn
             *              ({@link #isReadInCases}); empty, none is
             * @param working what the reading of the comparison told of the operations a row of
             *              this line gets past, together over every application that drew it
             */
            record Part(PlaceOfALine id, Read line, List<DecidingCase> cases,
                        UndividedByARelation.Working working) {

                /** A line whose reading is not known to have told of the operations a row of it
                 *  gets past: no row of it is shown computed. */
                public Part(PlaceOfALine id, Read line, List<DecidingCase> cases) {
                    this(id, line, cases, UndividedByARelation.Working.UNREAD);
                }

                public Part {
                    Objects.requireNonNull(id, "a line of a statement is one of its lines");
                    Objects.requireNonNull(working, "what the line's reading told, or that"
                            + " nothing is known");
                    cases = DecidingCase.eachByItsOwnCondition(cases);
                    if (!isALine(line) && !(line instanceof AgainstAnotherValue
                            || line instanceof Stopped)) {
                        throw new IllegalArgumentException("a relation of a statement read to the"
                                + " end is a line, drawn or refused, or relates another value: "
                                + line);
                    }
                    if (!isReadInCases(line) && !cases.isEmpty()) {
                        throw new IllegalArgumentException(
                                "what is no line is read in no case: " + line);
                    }
                }

                /** Whether {@code line} is a line, drawn or refused. */
                static boolean isALine(Read line) {
                    return line instanceof Cuts || line instanceof NoOrderToCountOn
                            || line instanceof NumberNoRatioHolds;
                }

                /** Whether {@code line} is read in the cases where the statement turns on it: a
                 *  line, or a relation to another value, whose settling values are parted by
                 *  lines there. */
                static boolean isReadInCases(Read line) {
                    return isALine(line) || line instanceof AgainstAnotherValue;
                }
            }
        }
    }

    /**
     * Whether the line itself can be placed: the quantity's own coefficients and the place the line
     * falls at, in the quantity's own units, are numbers an exact ratio holds.
     *
     * <p>Asked once, where the line is drawn, so that what reads a line afterwards is never handed
     * one it has no place for. Both are divided by how much of the quantity the rule wrote, and
     * either division can pass the exponents a ratio holds when the rule is written at their ends.
     *
     * <p>Only the line. The values beside it are a separate question ({@link #seam}), because a line
     * that is placed is a line the rule drew whether or not the values beside it were worked out.
     */
    boolean lineIsPlaced() {
        return of.identity() != null && CutPosition.holdsWhereItFalls(at, per());
    }

    /**
     * Whether this line's quantity rises where {@code relation}'s form does, or falls — or nothing
     * where the two are not over a number this can hold them against each other on.
     *
     * <p>Asked of one number both are over, which is enough: the line was drawn off the relation,
     * so its quantity is the form, turned or not, with the constant moved out.
     */
    Optional<Boolean> risesWith(Relation relation) {
        // A term against a place on its order rises as the term does, which is the position's own
        // values where the line is on them.
        if (relation instanceof Relation.Ordered(DecisionAtom.OfTheInput(var term), var _, var _)
                && of instanceof BorderQuantity.OfACoordinate coordinate) {
            return coordinate.term().equals(term) ? Optional.of(true) : Optional.empty();
        }
        if (!(relation instanceof Relation.Affine affine)) {
            return Optional.empty();
        }
        // A count, what a division leaves, or what two numbers come to multiplied, rises as that
        // number does: the line is drawn on the number itself, and the relation weighs it by its
        // coefficient.
        if (of instanceof BorderQuantity.HowMany || of instanceof BorderQuantity.RemainderOfAForm
                || of instanceof BorderQuantity.RemainderOfAPair
                || of instanceof BorderQuantity.ProductOfAPair) {
            for (Map.Entry<Quantity, ExactRatio> each : affine.form().coefs().entrySet()) {
                if (((each.getKey() instanceof Quantity.HowManyMeet
                        || each.getKey() instanceof Quantity.HowManyDifferentMeet)
                        && of instanceof BorderQuantity.HowMany)
                        || (each.getKey() instanceof Quantity.RemainderOfADividend
                                && of instanceof BorderQuantity.RemainderOfAForm)
                        || (each.getKey() instanceof Quantity.RemainderByAnInput
                                && of instanceof BorderQuantity.RemainderOfAPair)
                        || (each.getKey() instanceof Quantity.ProductOfTwo
                                && of instanceof BorderQuantity.ProductOfAPair)) {
                    return each.getValue().signum() == 0 ? Optional.empty()
                            : Optional.of(each.getValue().signum() > 0);
                }
            }
            return Optional.empty();
        }
        Map<NumericTerm, ExactRatio> mine = switch (of) {
            case BorderQuantity.OfACoordinate coordinate -> Map.of(coordinate.term(), ExactRatio.ONE);
            case BorderQuantity.OverAForm form -> form.form().coefs();
            default -> Map.of();
        };
        for (Map.Entry<NumericTerm, ExactRatio> each : mine.entrySet()) {
            ExactRatio theirs = affine.form().coefs().get(new DecisionAtom.OfTheInput(each.getKey()));
            if (theirs != null && theirs.signum() != 0 && each.getValue().signum() != 0) {
                return Optional.of(theirs.signum() == each.getValue().signum());
            }
        }
        return Optional.empty();
    }

    /**
     * {@code drawn}, said to stand to the line of its author's as {@code mapping} says, and facing
     * the sides the comparison wrote the way its own quantity faces them: the relation it was drawn
     * off faces them as {@code mapping} has it, and the quantity faces the relation as
     * {@link #risesWith} says.
     */
    private static Read authored(Read drawn, AuthoredPointMapping mapping,
                                 Proposition.Compared relation) {
        if (!(drawn instanceof Read.Cuts cuts)) {
            return drawn;
        }
        AuthoredPointMapping faced = mapping;
        if (mapping instanceof AuthoredPointMapping.Proven(
                var line, var claims, var facing, var itsOwn)) {
            Optional<Boolean> rises = facing == Derivation.AComparisonRead.Facing.NOTHING_WRITTEN
                    ? Optional.empty() : cuts.cutting().risesWith(relation.relation());            // A line the comparison's own relation draws claims what the comparison wrote. One
            // something else written in its definition draws — how an arm is selected, a
            // comparison written inside it, what a law says — has no two sides of the
            // comparison's written for it, and claims what this reading drew, as the comparison
            // holds or fails across it there.
            boolean selects = !line.arms().isEmpty() && line.arms().getLast().selects();
            boolean drawsItsOwn = itsOwn && !selects;
            faced = new AuthoredPointMapping.Proven(line, drawsItsOwn ? claims
                    : AuthoredPointMapping.facedTheOneWay(cuts.cutting().claim()),
                    !drawsItsOwn || rises.isEmpty()
                            ? Derivation.AComparisonRead.Facing.NOTHING_WRITTEN
                            : Derivation.AComparisonRead.Facing.of(rises.get()
                                    != (facing == Derivation.AComparisonRead.Facing.AS_WRITTEN)),
                    drawsItsOwn);
        }
        return new Read.Cuts(cuts.cutting(), faced);
    }

    /** The line, or the refusal to place it when the number it falls at has no representation. */
    private static Read cutsOrRefused(Cutting cutting) {
        return cutting.lineIsPlaced()
                ? new Read.Cuts(cutting)
                : new Read.NumberNoRatioHolds(cutting.of().filedAt());
    }

    /**
     * The same, said as which of the four it is.
     *
     * <p><b>What the comparison states, put on the input space, and nothing else.</b> What a
     * comparison states is read once ({@link Pullback#ofAComparison}), and a line is drawn only
     * where that statement is one line over the input's own numbers: a form of them against a
     * threshold, or one of them against a place on the order it stands on. Nothing here reads the
     * operands for a line of its own, so a line is never drawn where the statement is something
     * else — and where the statement is read further than the operands are, through what an
     * operation's law says its answer comes to, the line is drawn there too.
     *
     * <p>A statement of several relations held together is one rule with a line for each
     * ({@link Read.Several}), and so is a comparison inside a closure handed the values a
     * container was written with, read on each application ({@code applying}). A statement one of
     * whose parts is no relation over the input's own numbers is read and not drawn
     * ({@link BlockReason.SeveralLinesInOneRule}). A statement none of whose parts is a relation
     * of numbers, only which cases, truths and values the input's positions hold, is what an
     * application stating it is: no line, and no reading that stopped
     * ({@link Read.StatesNoRelation}).
     *
     * <p>The reason a reading stopped is settled here, where it stopped, and not asked for
     * afterwards by whoever met the absence.
     *
     * @param writtenIn the copy of its body the comparison stands in, where it is a comparison a
     *                  body wrote: what tells the lines its author drew from the places a call put
     *                  them ({@link PartOfAComparison}). Nothing for a clause, whose several lines
     *                  are not drawn
     */
    static Read read(String behavior, StatedComparison comparison,
                     InputReading read, InputReads reads, ClosureApplications applying,
                     Arrivals answering, WhatConditionsState conditions,
                     Optional<ExpansionLineage> writtenIn) {
        List<ClosureApplications.Application> each = switch (applying) {
            case ClosureApplications.Each(var made) -> made;
            // A comparison inside a closure no run applies is read on no application, and comes
            // out the same — not at all — on every row.
            case ClosureApplications.None _ -> List.of();
            case ClosureApplications.Outside _, ClosureApplications.NotSaid _ -> null;
        };
        if (each == null) {
            return readOnce(behavior, comparison, read, reads, answering,
                    conditions.comparison(comparison, reads, read), writtenIn);
        }
        Read drawn = onEachApplication(behavior, comparison, read, reads, each, answering,
                conditions, writtenIn);
        // Where an application is made, and where a line decides on it, is part of what the line
        // is; said in anything but what a row's own numbers answer, a row could not be asked
        // whether it is somewhere the line decides, and none of the lines is drawn.
        return drawn instanceof Read.Several several && several.parts().stream()
                .anyMatch(part -> !part.cases().stream()
                        .allMatch(one -> AStatementAtARow.askable(one.condition())))
                ? severalNotDrawn(comparison, read, reads, answering)
                : drawn;
    }

    /**
     * Where a run stops in the comparison, or null where none does: the rows on which an operation
     * it is read through ends the run, so that it states nothing on either side.
     *
     * <p>Independent of the line it draws. A comparison whose ways divide by nought on some of them
     * draws its line on the others, and the ways that stop are no part of that line; they are said
     * as what they are, and whether a row reaches them is asked of the way to the comparison
     * ({@link ComparisonAssessment#someRowArrives}). Asked of each application a closure is
     * made on, where that application is made, since a run that never makes one is not stopped by
     * it.
     */
    static Proposition whereTheRunStops(StatedComparison comparison, InputReading read,
                                        InputReads reads, ClosureApplications applying,
                                        WhatConditionsState conditions) {
        List<WhereARunStops.OnOneReading> readings = new ArrayList<>();
        switch (applying) {
            case ClosureApplications.Each(var made) -> made.forEach(one -> readings.add(
                    new WhereARunStops.OnOneReading(one.reached(),
                            conditions.comparison(comparison, one.reads(), read).stated()
                                    .meaning())));
            case ClosureApplications.None _ -> { }
            case ClosureApplications.Outside _, ClosureApplications.NotSaid _ ->
                    readings.add(new WhereARunStops.OnOneReading(null,
                            conditions.comparison(comparison, reads, read).stated().meaning()));
        }
        return WhereARunStops.across(readings);
    }

    /**
     * One line an application of a closure draws: which of the author's lines it is a place of,
     * and what reading it came to there.
     *
     * <p>Both, because each answers a different half of whether two applications drew one line.
     * The drawing is a quantity cut at a level, and two of the author's lines can be cut at one
     * level of one quantity; which of them it is, is what the line is owed for
     * ({@link PartOfAComparison}), and one of them drawn two ways is two readings to keep rather
     * than one to choose between.
     */
    private record ALineRead(PlaceOfALine id, Read read) {}

    /**
     * What a comparison inside a closure states on each application it is handed: one rule, with
     * a line for each line some application draws.
     *
     * <p>A line two applications draw is one line, read on each of them, and where it decides is
     * where it decides on one of them, met where a run makes that one
     * ({@link WhereAnApplicationIsMade#decidesOn}). Drawn on every application where it decides
     * everywhere, it is the line a comparison outside every closure would be.
     *
     * <p>One line is one of the author's lines, drawn the same way ({@link ALineRead}). The values
     * the closure is applied to are the caller's, so the places they put one of the author's lines
     * are readings of that line.
     *
     * <p>Every application's statement is a line or none of them is drawn, as with the relations of
     * one statement: where one application's reading stopped, the comparison stops there with that
     * application's reasons, at that application's places. An application on which the comparison
     * comes out the same for every row draws nothing.
     *
     * <p>Of the applications a run makes on some row. One made on no row — an operation that has
     * stopped on an answer before it on every row — is not read: nothing it states is part of the
     * comparison, and a reading of it that stopped would stop the applications that are made.
     */
    private static Read onEachApplication(String behavior, StatedComparison comparison,
                                          InputReading read, InputReads reads,
                                          List<ClosureApplications.Application> each,
                                          Arrivals answering, WhatConditionsState conditions,
                                          Optional<ExpansionLineage> writtenIn) {
        SequencedMap<FilingCoordinate, BlockReason.RuleReadingStopped> stopped =
                new LinkedHashMap<>();
        List<FilingCoordinate> settled = new ArrayList<>();
        List<FilingCoordinate> answeringNowhere = new ArrayList<>();
        List<FilingCoordinate> against = new ArrayList<>();
        List<UndividedByARelation> relations = new ArrayList<>();
        Map<ALineRead, List<WhereAnApplicationIsMade.OnOne>> lines = new LinkedHashMap<>();
        Map<ALineRead, List<UndividedByARelation.Working>> workings = new HashMap<>();
        InputReads statingNoRelation = null;
        for (ClosureApplications.Application one : each) {
            if (one.reached() instanceof Proposition.Always(boolean made) && !made) {
                continue;
            }
            Pullback.OnTheInput onTheInput = conditions.comparison(comparison, one.reads(), read);
            switch (readOnce(behavior, comparison, read, one.reads(), answering, onTheInput,
                    writtenIn)) {
                case Read.Stopped alone -> alone.why().forEach(stopped::putIfAbsent);
                case Read.StatesNoRelation _ -> {
                    if (statingNoRelation == null) {
                        statingNoRelation = one.reads();
                    }
                }
                case Read.CutsNothing alone -> alone.filedAt().forEach(at -> {
                    if (!settled.contains(at)) {
                        settled.add(at);
                    }
                });
                case Read.AnswersNowhere alone -> alone.filedAt().forEach(at -> {
                    if (!answeringNowhere.contains(at)) {
                        answeringNowhere.add(at);
                    }
                });
                case Read.AgainstAnotherValue alone -> {
                    alone.over().forEach(at -> {
                        if (!against.contains(at)) {
                            against.add(at);
                        }
                    });
                    relations.addAll(alone.relations());
                }
                case Read.Several several -> several.parts().forEach(part -> {
                    ALineRead key = new ALineRead(part.id(), part.line());
                    lines.computeIfAbsent(key, _ -> new ArrayList<>())
                            .add(new WhereAnApplicationIsMade.OnOne(part.cases(), one.reached()));
                    workings.computeIfAbsent(key, _ -> new ArrayList<>()).add(part.working());
                });
                case Read line -> {
                    ALineRead key = new ALineRead(new PlaceOfALine(
                            line instanceof Read.Cuts cuts
                                    ? PartOfAComparison.of(cuts.authored().line())
                                    : THE_COMPARISON,
                            spelled(onTheInput.stated().proposition())), line);
                    lines.computeIfAbsent(key, _ -> new ArrayList<>())
                            .add(WhereAnApplicationIsMade.OnOne.wherever(one.reached()));
                    workings.computeIfAbsent(key, _ -> new ArrayList<>())
                            .add(workingOf(onTheInput));
                }
            }
        }
        if (!stopped.isEmpty()) {
            return new Read.Stopped(stopped);
        }
        // Every application's statement is a line or none of them is drawn, and one that relates
        // the input to another value is no line.
        if (!against.isEmpty()) {
            return new Read.AgainstAnotherValue(against, relations);
        }
        // A statement of no relation on some application is no line there, and the lines the
        // others draw would be drawn as though the comparison were only them.
        if (statingNoRelation != null) {
            return lines.isEmpty() ? new Read.StatesNoRelation()
                    : severalNotDrawn(comparison, read, statingNoRelation, answering);
        }
        if (lines.isEmpty()) {
            return settled.isEmpty() && !answeringNowhere.isEmpty()
                    ? new Read.AnswersNowhere(answeringNowhere)
                    : new Read.CutsNothing(settled);
        }
        Read tooMany = linesOnOneQuantityPastTheFigure(lines.keySet(), comparison, read, reads,
                answering);
        if (tooMany != null) {
            return tooMany;
        }
        List<Read.Several.Part> parts = new ArrayList<>();
        // A relation of a statement that is no line, and relates no other value, is read in no
        // case on any application.
        lines.forEach((line, readings) -> parts.add(new Read.Several.Part(line.id(), line.read(),
                Read.Several.Part.isReadInCases(line.read())
                        ? WhereAnApplicationIsMade.decidesOn(readings) : List.of(),
                UndividedByARelation.Working.together(workings.get(line)))));
        // One line on every application is the line of the comparison itself, which a caller
        // reads the operations of from the comparison: so only where that is what the
        // applications told.
        if (parts.size() == 1 && WhereAnApplicationIsMade.everywhere(parts.getFirst().cases())
                && parts.getFirst().working().equals(
                        workingOf(conditions.comparison(comparison, reads, read)))) {
            return parts.getFirst().line();
        }
        return new Read.Several(parts);
    }

    /**
     * That where each of {@code lines} decides is not worked out, where some one quantity is cut
     * by more of them than {@link CompositionBudget#READINGS_OF_ONE_CONDITION} allows readings of
     * one condition — or null where none is.
     *
     * <p>Counted here and not along the readings that drew them. The readings of a value no
     * application is handed are shared by all the applications
     * ({@link souther.compiler.inputs.InputReads#readingsASplitIsOneOf}), so how many readings
     * there are says nothing of how many lines come of them, and the work of saying where each
     * decides grows faster than the lines on one quantity do. Past the figure it is not done,
     * which is what the readings were held to before they were shared.
     */
    private static Read linesOnOneQuantityPastTheFigure(Set<ALineRead> lines,
                                                        StatedComparison comparison,
                                                        InputReading read, InputReads reads,
                                                        Arrivals answering) {
        CompositionBudget figure = CompositionBudget.READINGS_OF_ONE_CONDITION;
        Map<BorderQuantity, Integer> onOne = new HashMap<>();
        for (ALineRead each : lines) {
            if (each.read() instanceof Read.Cuts cuts
                    && onOne.merge(cuts.cutting().of(), 1, Integer::sum) > figure.maximum()) {
                return new Read.Stopped(ComparisonAssessment.atEachOf(
                        GuardThresholds.filedAt(comparison, read, reads, answering),
                        new BlockReason.WhereALineDecidesNotWorkedOut(figure.figure())));
            }
        }
        return null;
    }

    /** The comparison as its author drew it, where its definition chooses nothing on the way. */
    private static final PartOfAComparison THE_COMPARISON =
            PartOfAComparison.of(WrittenLine.THE_COMPARISON);

    /** A statement that is one line, as the place of a line it is: the relation, held. */
    private static String spelled(Proposition stated) {
        return (stated instanceof Proposition.Compared compared ? compared.heldSpelling()
                : stated.spelling()).toString();
    }

    /**
     * The line a relation over how many elements of a container meet something draws — or null
     * where the relation is no such thing: a form weighing one count and nothing else, of a
     * statement a row's own numbers answer.
     *
     * <p>The count against a number. Against another of the input's numbers — {@code count == n}
     * — the line would be where the count and that number meet, which is two numbers held apart
     * and no line on a count.
     */
    private static Read onACount(String behavior, Relation.Affine affine, boolean holds,
                                 InputReading read) {
        if (affine.form().coefs().size() != 1) {
            return onACountAndNumbers(behavior, affine, holds, read);
        }
        Map.Entry<Quantity, ExactRatio> only = affine.form().coefs().entrySet().iterator().next();
        CountedElements counted = countedAs(behavior, only.getKey(), read);
        if (counted == null) {
            return null;
        }
        // The constant over the count's weight is where the line is. The weight is above nought: a
        // relation faces the one way, its first weight positive, and the count is its only atom.
        ExactRatio weight = only.getValue();
        ExactAnswer<ExactRatio> at = affine.form().constant().negated().dividedBy(weight);
        if (!(at instanceof ExactAnswer.Held<ExactRatio>(ExactRatio level))) {
            return null;
        }
        ComparisonClaim claim = ComparisonClaim.stating(
                holds ? affine.proposition() : affine.proposition().denied());
        BorderQuantity.HowMany of =
                new BorderQuantity.HowMany(counted, HowManyCanMeet.of(counted, read));
        Cutting drawn = made(of, new Level.OfTheQuantity(level), claim, read.quantities());
        return drawn == null ? null : cutsOrRefused(drawn);
    }

    /**
     * What {@code quantity} counts, as {@code behavior} reads it at rows — or null where it is no
     * count a row can be asked: how many elements meet a statement, or how many different values
     * the elements meeting one hold, of a statement a row's own numbers answer.
     *
     * <p>What an element meeting the statement is held to is the same for either count: it is a
     * statement about one element, whatever is counted of the elements meeting it. One asked of
     * what the elements holding a value come to is asked of each of them alike.
     */
    private static CountedElements countedAs(String behavior, Quantity quantity,
                                             InputReading read) {
        return (quantity instanceof Quantity.HowManyMeet
                || quantity instanceof Quantity.HowManyDifferentMeet)
                && AStatementAtARow.askable(AStatementAtARow.meetingOf(quantity))
                ? CountedElements.of(behavior, quantity, read.quantities(),
                        DemandReading.anElementMeeting(AStatementAtARow.elementsOf(quantity),
                                read))
                : null;
    }

    /** {@code first} where it drew a line, and what {@code otherwise} draws where it did not. */
    private static Read firstDrawn(Read first, Supplier<Read> otherwise) {
        return first != null ? first : otherwise.get();
    }

    /**
     * The line a relation over what a division leaves of a form of the input's numbers draws — or
     * null where the relation is no such thing: the remainder alone against a number, over numbers
     * each of which is counted.
     *
     * <p>A line on the remainder, which runs from nought to one below the divisor, and not on the
     * form: the values the form takes at the remainder come round every divisor, so what a row is
     * at is which remainder its values leave.
     */
    private static Read onARemainder(String behavior, Relation.Affine affine, boolean holds,
                                     InputReading read) {
        Quantity.RemainderOfADividend remainder = AStatementAtARow.remainderOfADividendIn(affine);
        if (remainder == null) {
            return null;
        }
        // The sum of the remainder and the other numbers is the quantity, the remainder weighed
        // once: scaled so, `c == r`, `r == c` and `2 * c == 2 * r` are one quantity and one line.
        if (!(ExactRatio.ONE.dividedBy(affine.form().coefs().get(remainder))
                instanceof ExactAnswer.Held<ExactRatio> scale)
                || !(affine.form().times(scale.value())
                        instanceof ExactAnswer.Held<LinearForm<Quantity>>(
                                LinearForm<Quantity> scaled))) {
            return null;
        }
        LinearForm<NumericTerm> added = AStatementAtARow.otherNumbersWithTheRemainder(scaled);
        BorderQuantity.RemainderOfAForm of =
                remainderOf(behavior, remainder, added, read.quantities());
        if (of == null) {
            return null;
        }
        ComparisonClaim claim = ComparisonClaim.stating(
                holds ? affine.proposition() : affine.proposition().denied());
        Cutting drawn = made(of, new Level.OfTheQuantity(scaled.constant().negated()),
                scale.value().signum() < 0 ? claim.turned() : claim, read.quantities());
        return drawn == null ? null : cutsOrRefused(drawn);
    }

    /**
     * What a row is asked to work {@code remainder} out of — or null where it is read at none.
     * The same remainder a line on it is drawn on ({@link #remainderOf}), so that what is
     * accepted as a remainder is the same for a line and for a row.
     */
    static DividedForm remainderAtARow(String behavior, Quantity.RemainderOfADividend remainder,
                                       Quantities quantities) {
        BorderQuantity.RemainderOfAForm of = remainderOf(behavior, remainder,
                new LinearForm<>(ExactRatio.ZERO, Map.of()), quantities);
        return of == null ? null : of.dividedForm();
    }

    /**
     * The remainder {@code remainder} is, read at the numbers of its form — or null where it is
     * read at none: a number of the form whose values are not counted, or a constant that is no
     * whole number to move the form by.
     *
     * <p>The one place a remainder of a form becomes a quantity.
     */
    private static BorderQuantity.RemainderOfAForm remainderOf(String behavior,
                                                       Quantity.RemainderOfADividend remainder,
                                                       LinearForm<NumericTerm> added,
                                                       Quantities quantities) {
        if (!(remainder.dividend().constant().floor()
                instanceof ExactAnswer.Held<BigInteger> shift)) {
            return null;
        }
        Map<NumericTerm, TermOrders> on = new LinkedHashMap<>();
        for (NumericTerm term : remainder.dividend().coefs().keySet()) {
            TermOrders orders = quantities.ordersOf(term);
            if (orders == null || orders.answered() == null || !orders.answered().counts()) {
                return null;
            }
            on.put(term, orders);
        }
        Map<NumericTerm, TermOrders> addedOn = new LinkedHashMap<>();
        for (NumericTerm term : added.coefs().keySet()) {
            TermOrders orders = quantities.ordersOf(term);
            if (orders == null || orders.answered() == null || !orders.answered().counts()) {
                return null;
            }
            addedOn.put(term, orders);
        }
        return new BorderQuantity.RemainderOfAForm(behavior,
                new BorderQuantity.OverAForm(behavior,
                        new LinearForm<>(ExactRatio.ZERO, remainder.dividend().coefs()), on),
                shift.value(), remainder.divisor(), added, addedOn);
    }

    /**
     * The line on {@code term} alone where it stands to {@code at} as {@code relation}, as a
     * comparison of the term against that number draws it — or null where it draws none there.
     *
     * <p>For a line a reading worked out rather than one a comparison wrote: where the values of a
     * term that settle a relation end ({@link UndividedByARelation}).
     */
    static Cutting onOneTerm(String behavior, NumericTerm term, ExactRatio at, Rel relation,
                             Quantities quantities) {
        return realized(behavior, new AffineReading(
                new LinearForm<>(ExactRatio.ZERO, Map.of(term, ExactRatio.ONE)), at,
                ComparisonClaim.stating(relation)), quantities)
                instanceof Read.Cuts(Cutting cutting, AuthoredPointMapping _) ? cutting : null;
    }

    /**
     * The line a relation over what one whole number of the input leaves of another divided by it
     * draws — or null where the relation is no such thing: the remainder alone against a number.
     *
     * <p>A line on the remainder and on neither number: which pair leaves it turns on both, so what
     * a row is at is the remainder its two numbers leave.
     */
    private static Read onARemainderByAnInput(String behavior, Relation.Affine affine,
                                              boolean holds, InputReading read) {
        Quantity.RemainderByAnInput remainder = AStatementAtARow.remainderByAnInputIn(affine);
        if (remainder == null) {
            return null;
        }
        ExactRatio weight = affine.form().coefs().get(remainder);
        if (!(affine.form().constant().negated().dividedBy(weight)
                instanceof ExactAnswer.Held<ExactRatio>(ExactRatio level))) {
            return null;
        }
        Map<NumericTerm, TermOrders> on = new LinkedHashMap<>();
        Map<NumericTerm, ExactRatio> each = new LinkedHashMap<>();
        for (NumericTerm number : remainder.operands()) {
            TermOrders orders = read.quantities().ordersOf(number);
            if (orders == null || !(orders.answered() instanceof Carrier.Whole)) {
                return null;
            }
            on.put(number, orders);
            each.put(number, ExactRatio.ONE);
        }
        // Over the remainder's weight, which turns the relation round where it is below nought.
        ComparisonClaim claim = ComparisonClaim.stating(
                holds ? affine.proposition() : affine.proposition().denied());
        BorderQuantity.RemainderOfAPair of = new BorderQuantity.RemainderOfAPair(behavior,
                new BorderQuantity.OverAForm(behavior, new LinearForm<>(ExactRatio.ZERO, each),
                        on), remainder.dividend(), remainder.divisor());
        Cutting drawn = made(of, new Level.OfTheQuantity(level),
                weight.signum() < 0 ? claim.turned() : claim, read.quantities());
        return drawn == null ? null : cutsOrRefused(drawn);
    }

    /**
     * The line a relation over what two whole numbers of the input come to multiplied draws — or
     * null where the relation is no such thing: the product alone against a number.
     *
     * <p>A line on the product and on neither factor: where the product is the level turns on both,
     * so what a row is at is what its two numbers multiply to.
     */
    private static Read onAProduct(String behavior, Relation.Affine affine, boolean holds,
                                   InputReading read) {
        Quantity.ProductOfTwo product = AStatementAtARow.productIn(affine);
        if (product == null) {
            return null;
        }
        ExactRatio weight = affine.form().coefs().get(product);
        if (!(affine.form().constant().negated().dividedBy(weight)
                instanceof ExactAnswer.Held<ExactRatio>(ExactRatio level))) {
            return null;
        }
        Map<NumericTerm, TermOrders> on = new LinkedHashMap<>();
        Map<NumericTerm, ExactRatio> each = new LinkedHashMap<>();
        for (NumericTerm factor : product.factors()) {
            on.put(factor, read.quantities().ordersOf(factor));
            each.put(factor, ExactRatio.ONE);
        }
        // Over the product's weight, which turns the relation round where it is below nought.
        ComparisonClaim claim = ComparisonClaim.stating(
                holds ? affine.proposition() : affine.proposition().denied());
        BorderQuantity.ProductOfAPair of = new BorderQuantity.ProductOfAPair(behavior,
                new BorderQuantity.OverAForm(behavior, new LinearForm<>(ExactRatio.ZERO, each),
                        on));
        Cutting drawn = made(of, new Level.OfTheQuantity(level),
                weight.signum() < 0 ? claim.turned() : claim, read.quantities());
        return drawn == null ? null : cutsOrRefused(drawn);
    }

    /**
     * The line a relation over how many elements of a container meet something and numbers of the
     * input draws — or null where the relation is no such thing: one count, and nothing but numbers
     * of the input beside it.
     *
     * <p>The sum of the count and the form is the quantity, weighed once. A relation is written
     * with whatever weight on the count, and its sign and size say nothing about where the rows
     * fall, so it is scaled to weigh the count by one — turned over where that takes a negative —
     * and then {@code count >= n}, {@code 2 * count >= 2 * n} and {@code n <= count} are one
     * quantity and one line.
     */
    private static Read onACountAndNumbers(String behavior, Relation.Affine affine,
                                           boolean holds, InputReading read) {
        Quantity count = null;
        ExactRatio weight = null;
        for (Map.Entry<Quantity, ExactRatio> each : affine.form().coefs().entrySet()) {
            if (each.getKey() instanceof Quantity.HowManyMeet
                    || each.getKey() instanceof Quantity.HowManyDifferentMeet) {
                if (count != null) {
                    return null;
                }
                count = each.getKey();
                weight = each.getValue();
            } else if (each.getKey() instanceof DecisionAtom.OfTheInput(NumericTerm term)) {
                TermOrders orders = read.quantities().ordersOf(term);
                if (orders == null || orders.answered() == null || !orders.answered().counts()) {
                    return null;
                }
            } else {
                return null;
            }
        }
        CountedElements counted = count == null ? null : countedAs(behavior, count, read);
        if (counted == null) {
            return null;
        }
        if (!(ExactRatio.ONE.dividedBy(weight) instanceof ExactAnswer.Held<ExactRatio>(
                ExactRatio scale))
                || !(affine.form().times(scale) instanceof ExactAnswer.Held<LinearForm<Quantity>>(
                        LinearForm<Quantity> scaled))) {
            return null;
        }
        Map<NumericTerm, ExactRatio> added = new LinkedHashMap<>();
        Map<NumericTerm, TermOrders> on = new LinkedHashMap<>();
        for (Map.Entry<Quantity, ExactRatio> each : scaled.coefs().entrySet()) {
            if (each.getKey() instanceof DecisionAtom.OfTheInput(NumericTerm term)) {
                added.put(term, each.getValue());
                on.put(term, read.quantities().ordersOf(term));
            }
        }
        ComparisonClaim claim = ComparisonClaim.stating(
                holds ? affine.proposition() : affine.proposition().denied());
        BorderQuantity.HowMany of = new BorderQuantity.HowMany(counted,
                new LinearForm<>(ExactRatio.ZERO, added), on, Optional.empty());
        Cutting drawn = made(of, new Level.OfTheQuantity(scaled.constant().negated()),
                scale.signum() < 0 ? claim.turned() : claim, read.quantities());
        return drawn == null ? null : cutsOrRefused(drawn);
    }

    /**
     * What {@code comparison} states read once, in {@code reads}, with each line it draws named as
     * the line of its author's it is a place of.
     *
     * <p>A statement that is one relation is one line, and still a place of each line the author
     * drew that it was reached under: {@code Int.max(x, y) <= g} called on {@code p} and {@code p}
     * states {@code p <= g} alone, and that is where both of the author's lines landed.
     *
     * @param onTheInput what the comparison states there, put on the input
     */
    private static Read readOnce(String behavior, StatedComparison comparison,
                                 InputReading read, InputReads reads, Arrivals answering,
                                 Pullback.OnTheInput onTheInput,
                                 Optional<ExpansionLineage> writtenIn) {
        Pullback.TheBound bound = Pullback.boundOf(comparison, read, reads,
                writtenIn.orElse(null) instanceof ExpansionLineage.Expansion);
        return heldIn(writtenAgainst(
                readOnceAsDrawn(behavior, comparison, read, reads, answering, onTheInput,
                        writtenIn),
                bound.written()), bound.heldIn());
    }

    /** {@code drawn}, every line of it noted as the comparison written against {@code level}. */
    private static Read writtenAgainst(Read drawn, Optional<ExactRatio> level) {
        return switch (drawn) {
            // Only a line on a value derived from several positions, which is what a bound is
            // looked up against. A line on one position that the reading draws as well — a filter
            // the value is made of — is cut where that filter put it, and the bound of the table
            // is no bound of it.
            case Read.Cuts cuts -> cuts.cutting().of().derivedFromSeveralPositions().isPresent()
                    ? new Read.Cuts(cuts.cutting().writtenAgainst(level), cuts.authored())
                    : cuts;
            case Read.Several several -> new Read.Several(several.parts().stream()
                    .map(part -> new Read.Several.Part(part.id(),
                            writtenAgainst(part.line(), level), part.cases(), part.working()))
                    .toList());
            default -> drawn;
        };
    }

    /**
     * {@code drawn}, every line of it noted as held against the data {@code data} names.
     *
     * <p>Every line the comparison draws and not only one on a derived value: a bound read out of
     * a table is written in the table whatever the line is cut on.
     */
    private static Read heldIn(Read drawn, Optional<BoundHeldIn> data) {
        return switch (drawn) {
            case Read.Cuts cuts -> new Read.Cuts(cuts.cutting().heldIn(data), cuts.authored());
            case Read.Several several -> new Read.Several(several.parts().stream()
                    .map(part -> new Read.Several.Part(part.id(), heldIn(part.line(), data),
                            part.cases(), part.working()))
                    .toList());
            default -> drawn;
        };
    }

    private static Read readOnceAsDrawn(String behavior, StatedComparison comparison,
                                        InputReading read, InputReads reads, Arrivals answering,
                                        Pullback.OnTheInput onTheInput,
                                        Optional<ExpansionLineage> writtenIn) {
        Pullback.Pulled stated = onTheInput.stated();
        Supplier<Optional<AuthorsLines>> lines =
                new Pullback.Once<>(() -> writtenIn.map(at -> WrittenLines.of(
                        stated.meaning().how(), at, Optional.empty(),
                        Optional.of(comparison.claim()))));
        Read drawn = readAsAWhole(behavior, comparison, read, reads, answering, onTheInput, lines);
        if (writtenIn.isEmpty() || !(stated.proposition() instanceof Proposition.Compared compared)
                || !(drawn instanceof Read.Cuts || drawn instanceof Read.NoOrderToCountOn
                        || drawn instanceof Read.NumberNoRatioHolds)) {
            return drawn;
        }
        AuthorsLines authors = lines.get().orElseThrow();
        Map<PartOfAComparison, AuthoredPointMapping> of =
                authorsLines(authors, List.of(compared), comparison.claim());
        // A place of one of the author's lines is that line's one reading here, whichever line it
        // is; the line it is a place of is carried with it. A place of several is a line of each,
        // deciding where a row takes the arms that line is under.
        if (of.size() == 1) {
            return authored(drawn, of.values().iterator().next(), compared);
        }
        List<Read.Several.Part> parts = new ArrayList<>();
        of.forEach((line, mapping) -> parts.add(new Read.Several.Part(
                new PlaceOfALine(line, compared.heldSpelling().toString()),
                authored(drawn, mapping, compared),
                WhereEachLineDecides.takenWhere(
                        List.of(DecidingCase.alone(WhereAnApplicationIsMade.nothingAsked())),
                        authors.takenWhere(mapping.line())),
                workingOf(onTheInput))));
        return new Read.Several(parts);
    }

    /** What the comparison on {@code onTheInput} is told to work out: what the rule that read it
     *  tells where it tells more, and otherwise what the reading of it told. */
    private static UndividedByARelation.Working workingOf(Pullback.OnTheInput onTheInput) {
        return onTheInput.working().get();
    }

    /**
     * Which of the author's lines a relation is a place of, and how it stands to each, as
     * {@code lines} says: the comparison itself where nothing the derivation made it under was the
     * author's choice, and not shown to be its line where no step was seen making it at all.
     *
     * @param scales  the relation at every scale the statement wrote it at, its own first: a step
     *                that made it at any of them made it, and where two say how it stands to one
     *                line, the first says
     * @param written what the comparison claims, as its author wrote it
     */
    private static Map<PartOfAComparison, AuthoredPointMapping> authorsLines(
            AuthorsLines lines, List<Proposition.Compared> scales, ComparisonClaim written) {
        Map<PartOfAComparison, AuthoredPointMapping> out = new LinkedHashMap<>();
        for (Proposition.Compared relation : scales) {
            Map<WrittenLine, AuthoredPointMapping> under =
                    lines.of(relation.heldSpelling().toString());
            if (under != null) {
                under.forEach((line, mapping) ->
                        out.putIfAbsent(PartOfAComparison.of(line), mapping));
            }
        }
        if (out.isEmpty()) {
            out.put(THE_COMPARISON,
                    new AuthoredPointMapping.Undetermined(WrittenLine.THE_COMPARISON, written));
        }
        return out;
    }

    /** What {@code comparison} states read once, in {@code reads}, as the reading drew it. */
    private static Read readAsAWhole(String behavior, StatedComparison comparison,
                                     InputReading read, InputReads reads, Arrivals answering,
                                     Pullback.OnTheInput onTheInput,
                                     Supplier<Optional<AuthorsLines>> lines) {
        Pullback.Pulled stated = onTheInput.stated();
        Read line = stated.proposition() instanceof Proposition.Compared(
                Relation.Affine affine, boolean holds, Spelling _)
                ? lineOn(behavior, affine, holds, comparison.left(), read, reads) : null;
        List<FilingCoordinate> related = line == null
                ? relatedToAnotherValue(stated.proposition()) : null;
        return switch (stated.proposition()) {
            case Proposition.Always _ -> new Read.CutsNothing(
                    settledAt(stated, comparison, read, reads, answering));
            case Proposition.WhereItAnswers nowhere when Proposition.answersNowhere(nowhere) ->
                    new Read.AnswersNowhere(settledAt(stated, comparison, read, reads, answering));
            case Proposition.Compared _ when line != null -> line;
            case Proposition.Compared _ when related != null ->
                    against(related, stated.proposition());
            case Proposition.Some some
                    when valuesItRelates(some) instanceof List<FilingCoordinate> values ->
                    against(values, some);
            case Proposition.OnAnApplication applied
                    when againstAnotherValueOnEach(applied) instanceof Read.AgainstAnotherValue
                    each -> each;
            case Proposition.Compared(Relation.Ordered(
                    DecisionAtom.OfTheInput(NumericTerm term), Place at, Rel proposition),
                    boolean holds, Spelling _) when term.atOnePosition() != null ->
                    onAnOrder(behavior, term.atOnePosition(), at,
                            holds ? proposition : proposition.denied(), read.quantities());
            // A number the statement names has no representation, which is a line placed at a
            // number nothing holds: nothing about the order fell short.
            case Proposition.Unread unread when unread.why() instanceof WhyUnread.ANumberNotHeld ->
                    new Read.NumberNoRatioHolds(
                            GuardThresholds.filedAt(comparison, read, reads, answering));
            // Which cases, truths and values the input's positions hold, and no relation of
            // numbers: what an application stating it is ({@link #ofAnApplication}).
            case Proposition.All _, Proposition.Any _, Proposition.SoManyHold _,
                 Proposition.Some _, Proposition.InCases _, Proposition.Truth _,
                 Proposition.Present _, Proposition.WhereItAnswers _
                    when statesNoRelation(stated.proposition()) -> new Read.StatesNoRelation();
            // A statement read where an operation in it answers is the lines of what it states,
            // each deciding only where the operation answers ({@link WhereEachLineDecides}).
            case Proposition.All _, Proposition.Any _, Proposition.SoManyHold _,
                 Proposition.WhereItAnswers _
                    when !Proposition.leavesSomethingUnread(stated.proposition()) ->
                    asLines(behavior, comparison, stated.proposition(), onTheInput.arithmetic(),
                            onTheInput.working(), onTheInput.workingOfRelation(), read, reads,
                            answering, lines.get());
            // Some element meeting several parts, which is the parts read of that element: a
            // lookup's answer compared as a whole is its entry under the key meeting the
            // comparison, and the line is the comparison's on the entry. Inside an either-or it is
            // the same parts, read there. No element meeting them is the same parts as well, each
            // turning what is said of an element either way round: the greatest of some values at
            // or below a number is no value above it, and its line is the line on a value.
            case Proposition.Some some when !Proposition.leavesSomethingUnread(some) ->
                    asLines(behavior, comparison, some, onTheInput.arithmetic(),
                            onTheInput.working(), onTheInput.workingOfRelation(), read, reads,
                            answering, lines.get());
            default -> noLine(comparison, stated.proposition(),
                    Proposition.stopsIn(stated.proposition()), Set.of(), onTheInput.arithmetic(),
                    read, reads, answering);
        };
    }

    /**
     * A comparison whose statement is no line on the input, at each place it is filed at — or, where
     * it names no position, at each place the values it compares came from.
     *
     * <p>Which kind of thing kept it from being a line is read off the statement
     * ({@link #whatItStates}). Where that is a form nothing takes apart, an operation's answer or a
     * value the terms name no position for, the word a place is left with is the place's: the
     * carrier of a position whose own values the rule is about says whether a line could be drawn
     * on it at all, and where the values came from says whether an operation made them
     * ({@link GuardThresholds#whatEachPlaceIsLeftWith}). Every other kind is the statement's, and
     * the same at each place.
     *
     * <p>A relation read to the end against another value is no reading that stopped, and is said
     * before this is asked ({@link #relatedToAnotherValue}).
     *
     * @param stops         what stopped the readings under its parts: the parts nothing read, or,
     *                      of a statement of several relations, what stopped under those that drew
     *                      no line
     * @param beyondTheForm of a statement of several relations, the arithmetic in those that drew
     *                      no line that no line is drawn through, which is decided as a stop of
     *                      the arithmetic is
     */
    private static Read noLine(StatedComparison comparison, Proposition stated,
                               List<WhyUnread> stops, Set<NonAffineOperation> beyondTheForm,
                               Supplier<AffineReading.OfAComparison> arithmetic,
                               InputReading read, InputReads reads, Arrivals answering) {
        // A part the arithmetic met a shape it has no term for in is a stop whose reason was
        // decided where it was met. Which positions it is filed at is still asked of the
        // comparison, and the reason is not asked again of where the values came from.
        BlockReason.RuleReadingStopped decided = decidedByTheArithmetic(stops, beyondTheForm);
        if (decided != null) {
            List<FilingCoordinate> at = GuardThresholds.filedAt(comparison, read, reads, answering);
            if (!at.isEmpty()) {
                return new Read.Stopped(ComparisonAssessment.atEachOf(at, decided));
            }
            SequencedMap<FilingCoordinate, BlockReason.RuleReadingStopped> from =
                    new LinkedHashMap<>();
            GuardThresholds.cameFrom(comparison, reads, read.newtypes(), from);
            from.replaceAll((place, was) -> decided);
            return new Read.Stopped(from);
        }
        BlockReason.WhatItStatesIsNoLine said = whatItStates(stated, stops);
        // A number no position holds is all the statement says of what it relates. Which number
        // that is — one the body worked out, what a dependency answered, what an operation did —
        // is what the arithmetic over the input met where it stopped, and the place says it.
        boolean placeWords = said == null
                || said.why() == BlockReason.WhatItStatesIsNoLine.Why.A_NUMBER_NO_POSITION_HOLDS;
        if (placeWords
                && arithmetic.get() instanceof AffineReading.OfAComparison.Stopped stopped) {
            return new Read.Stopped(GuardThresholds.whatEachPlaceIsLeftWith(
                    comparison, stopped, read, reads, answering));
        }
        BlockReason.WhatItStatesIsNoLine why = said != null ? said
                : new BlockReason.WhatItStatesIsNoLine(
                        BlockReason.WhatItStatesIsNoLine.Why.A_PART_NOT_READ);
        List<FilingCoordinate> filed =
                GuardThresholds.filedAt(comparison, read, reads, answering);
        if (!filed.isEmpty()) {
            return new Read.Stopped(ComparisonAssessment.atEachOf(filed, why));
        }
        // Where the values came from, and which of several containers' elements a value may be,
        // which is a fact about where the rule is filed and stays as that. A value filed where it
        // came from was made from what stands there, so a part that stood nowhere says less than
        // that does, and the statement's own reason is taken only where it says more.
        SequencedMap<FilingCoordinate, BlockReason.RuleReadingStopped> out =
                new LinkedHashMap<>();
        GuardThresholds.cameFrom(comparison, reads, read.newtypes(), out);
        out.replaceAll((at, was) -> was instanceof BlockReason.RuleAboutADerivedValue
                && why.why() != BlockReason.WhatItStatesIsNoLine.Why.A_PART_NOT_READ ? why : was);
        return new Read.Stopped(out);
    }

    /**
     * Where {@code stated}, which draws no line, relates the input's values to another value, read
     * to the end, the coordinates it is filed at — or null where it is no such relation.
     *
     * <p>Asked in one place for a comparison that states it alone and for each relation of
     * several. Two kinds are such a relation: numbers about how the input's values stand to one
     * another ({@link #heldOverValuesRelatedToOneAnother}), and numbers of the input against a value
     * no position holds ({@link #heldAgainstAnotherValue}). No relation is both.
     */
    private static List<FilingCoordinate> relatedToAnotherValue(Proposition stated) {
        List<FilingCoordinate> related = heldOverValuesRelatedToOneAnother(stated);
        return related != null ? related : heldAgainstAnotherValue(stated);
    }

    /**
     * Where {@code stated} relates numbers of the input to a value no position holds, read to the
     * end, the coordinates of those numbers — or null where it is no such relation.
     *
     * <p>Read to the end means every part of it, and the other value too: a value bound to a name
     * whose making a reading stopped at is a number this compiler could not follow back, and what
     * is owed there is that reading's stop. A value nothing was made from — what an operation
     * looked up, an element a walk was handed, the index it is at — is all there is to read.
     *
     * <p>One of those may be what a dependency answered, which a row stands in; whose relation it
     * is then is the decision table's, asked where the reading is assessed
     * ({@link ComparisonAssessment#of}).
     *
     * <p>Or what an operation answers of the input, filed at the numbers it is made of. Such an
     * answer is read only as one side of a relation between values made of positions apart
     * ({@code Pullback}), so a statement over one relates those positions as {@code d == s} does
     * and divides none of them.
     */
    private static List<FilingCoordinate> heldAgainstAnotherValue(Proposition stated) {
        if (!(stated instanceof Proposition.Compared(Relation.Affine affine, boolean _, Spelling _))
                || Proposition.leavesSomethingUnread(stated)) {
            return null;
        }
        List<NumericTerm> input = new ArrayList<>();
        boolean another = false;
        for (Quantity each : affine.form().coefs().keySet()) {
            switch (each) {
                case DecisionAtom.OfTheInput(NumericTerm term) -> input.add(term);
                case Quantity.OfABinding bound when bound.madeOf().isEmpty() -> another = true;
                case Quantity.WhatAnOperationAnswers answers -> {
                    input.addAll(answers.positionsItIsMadeOf());
                    another = true;
                }
                case Quantity.APieceOf piece -> {
                    input.addAll(piece.positionsItIsMadeOf());
                    another = true;
                }
                case Quantity.ThePieceAt piece -> {
                    input.addAll(piece.positionsItIsMadeOf());
                    another = true;
                }
                case Quantity.IsAmongThePieces among -> {
                    input.addAll(among.positionsItIsMadeOf());
                    another = true;
                }
                default -> {
                    return null;
                }
            }
        }
        return input.isEmpty() || !another ? null : AffineReading.filedAt(input);
    }

    /**
     * Why {@code relation}, which draws no line and relates the input to no other value, is none:
     * what stopped the reading under its terms, and what arithmetic in them no line is drawn
     * through, in the order its terms are kept — or read to the end, where neither is so.
     *
     * <p>A value bound in the body whose making a reading stopped at is no number of the input
     * because of that stop, as {@link #heldAgainstAnotherValue} reads it, and the stop is the
     * reading's. What two numbers come to multiplied was read, and is a line only against a
     * number: against anything else it is a product of two values that are not constants, which
     * no line is drawn through. Every other term stopped at nothing: it was read, and the relation
     * is no line for what it is.
     */
    private static TheParts.NotDrawn whyNoLine(Proposition.Compared relation) {
        if (!(relation.relation() instanceof Relation.Affine affine)) {
            return TheParts.READ_TO_THE_END;
        }
        List<WhyUnread> stops = new ArrayList<>();
        Set<NonAffineOperation> beyondTheForm = EnumSet.noneOf(NonAffineOperation.class);
        for (Quantity each : affine.form().coefs().keySet()) {
            switch (each) {
                case Quantity.OfABinding bound -> bound.madeOf().ifPresent(stops::add);
                case Quantity.ProductOfTwo _ ->
                        beyondTheForm.add(NonAffineOperation.PRODUCT_OF_NON_CONSTANT_VALUES);
                case Quantity.RemainderByAnInput _ ->
                        beyondTheForm.add(NonAffineOperation.REMAINDER_BY_NON_CONSTANT_VALUE);
                case DecisionAtom.OfTheInput _, DecisionAtom.OfAnAnswer _,
                     DecisionAtom.TakenOfAnAnswer _, DecisionAtom.ComputedOverAnAnswer _,
                     Quantity.HowManyMeet _,
                     Quantity.HowManyHold _, Quantity.HowManyDifferent _,
                     Quantity.HowManyDifferentMeet _,
                     Quantity.HowManyDifferentBelow _, Quantity.HowManyDifferentAcross _,
                     Quantity.SumOver _,
                     Quantity.CodePointsOfAPiece _, Quantity.RemainderOfADividend _,
                     Quantity.WhatAnOperationAnswers _, Quantity.APieceOf _,
                     Quantity.ThePieceAt _, Quantity.IsAmongThePieces _ -> { }
                case Quantity.HowManyCarried carried -> throw carried.reachedAReader();
                case Quantity.TheKeptTotal kept -> throw kept.reachedAReader();
            }
        }
        return new TheParts.NotDrawn(stops, beyondTheForm);
    }

    /**
     * Where {@code stated} weighs numbers that are about how the values of the input stand to one
     * another, read to the end, the coordinates of those values — or null where it is no such
     * relation.
     *
     * <p>Two kinds of number are about that. How many elements of one container are, or are not,
     * one of the elements of another is what the size of a union, an intersection or a difference
     * of two sets comes to ({@link Quantity.HowManyMeet} over a statement that two values are
     * one); and how many different values a container holds is a number of the values against one
     * another and of none of them alone ({@link Quantity.HowManyDifferent}). Neither is a number a
     * position holds, so no line is drawn on one, and nothing in either stopped a reading: the
     * numbers of the input beside them are the ones a line could be drawn on, and which side of it
     * a row falls on moves with the other values.
     */
    private static List<FilingCoordinate> heldOverValuesRelatedToOneAnother(Proposition stated) {
        if (!(stated instanceof Proposition.Compared(Relation.Affine affine, boolean _,
                                                     Spelling _))) {
            return null;
        }
        List<NumericTerm> input = new ArrayList<>();
        List<FilingCoordinate> related = new ArrayList<>();
        for (Quantity each : affine.form().coefs().keySet()) {
            switch (each) {
                case DecisionAtom.OfTheInput(NumericTerm term) -> input.add(term);
                case Quantity.HowManyMeet count
                        when valuesItRelates(count.ofTheElement()) instanceof List<FilingCoordinate>
                        values -> related.addAll(values);
                case Quantity.HowManyDifferent different -> different.ofTheElement().heldAt()
                        .forEach(at -> related.add(FilingCoordinate.at(at)));
                case Quantity.HowManyDifferentAcross across -> related.add(
                        FilingCoordinate.at(across.ofTheOccurrence().inputPosition()));
                // The values the nodes reached collect are the ones relating: the position of
                // the key a node looks its entry up by, the key that entry is filed under, and the
                // value taken of it. No coordinate of the map's own entries is claimed.
                case Quantity.HowManyDifferentBelow below -> {
                    related.add(FilingCoordinate.at(below.keyOfTheRoot()));
                    related.add(FilingCoordinate.at(below.map().key()));
                    related.add(FilingCoordinate.at(below.valueOfAnEntry()));
                }
                default -> {
                    return null;
                }
            }
        }
        // Asked last: the walk of the whole statement is the dear part, and most comparisons
        // are dropped above for weighing something that is neither.
        if (related.isEmpty() || Proposition.leavesSomethingUnread(stated)) {
            return null;
        }
        List<FilingCoordinate> out = new ArrayList<>(AffineReading.filedAt(input));
        for (FilingCoordinate each : related) {
            if (!out.contains(each)) {
                out.add(each);
            }
        }
        return out;
    }

    /**
     * What the arithmetic said of the parts a statement stopped at, where every part stopped at
     * arithmetic no form says — or null where some part stopped for anything else.
     *
     * <p>One operation is that operation, wherever the closure that holds it is reached from. Two
     * different ones are no operation: naming the first would say of the second that it was not
     * there, so the statement is a part not read, which is all they have in common.
     *
     * <p>And a part that stopped for something else leaves this null, so that what is said is what
     * would be said without it. The arithmetic's reason is the reason for the parts it stopped, and
     * it is not the statement's where others did not stop there.
     *
     * <p>Arithmetic that was read and that no line is drawn through ({@code beyondTheForm}) is
     * counted with the operations the reading stopped at: a product no line is drawn through is the
     * product a reading stopped at, to an author.
     */
    private static BlockReason.RuleReadingStopped decidedByTheArithmetic(
            List<WhyUnread> stops, Set<NonAffineOperation> beyondTheForm) {
        Set<NonAffineOperation> operations = EnumSet.noneOf(NonAffineOperation.class);
        operations.addAll(beyondTheForm);
        for (WhyUnread each : stops) {
            if (!(each instanceof WhyUnread.OutsideTheLinearFragment(var operation))) {
                return null;
            }
            operations.add(operation);
        }
        return switch (operations.size()) {
            case 0 -> null;
            case 1 -> new BlockReason.NonAffineArithmetic(operations.iterator().next());
            default -> new BlockReason.WhatItStatesIsNoLine(
                    BlockReason.WhatItStatesIsNoLine.Why.A_PART_NOT_READ);
        };
    }

    /**
     * Why {@code stated}, which the cases above draw no line of, is no line on the input — or null
     * where a part of it stopped at something each place it is filed at words for itself.
     *
     * <p>A part the place words is asked first: where one is in the statement, an author is sent to
     * it before a step this compiler has not taken beside it. Then a part declined at a figure, in
     * the order the words for them are declared, since a run allowed more may read any of them;
     * and then any other part.
     *
     * @throws IllegalStateException where a part stopped at a figure no word says, which would
     *                               otherwise be said as a part no wider run reads
     */
    static BlockReason.WhatItStatesIsNoLine whatItStates(Proposition stated,
                                                         List<WhyUnread> stops) {
        if (stops.stream().anyMatch(Cutting::wordedByThePlace)) {
            return null;
        }
        for (BlockReason.WhatItStatesIsNoLine.Why each
                : BlockReason.WhatItStatesIsNoLine.Why.values()) {
            if (each.says() != null && stops.contains(each.says())) {
                return new BlockReason.WhatItStatesIsNoLine(each);
            }
        }
        stops.stream().filter(why -> why.figure().isPresent()).findFirst().ifPresent(why -> {
            throw new IllegalStateException("no word says a part stopped at " + why);
        });
        if (!stops.isEmpty()) {
            return new BlockReason.WhatItStatesIsNoLine(
                    BlockReason.WhatItStatesIsNoLine.Why.A_PART_NOT_READ);
        }
        return new BlockReason.WhatItStatesIsNoLine(switch (stated) {
            case Proposition.Compared _ ->
                    BlockReason.WhatItStatesIsNoLine.Why.A_NUMBER_NO_POSITION_HOLDS;
            case Proposition.Always _, Proposition.Unread _, Proposition.Truth _,
                 Proposition.InCases _, Proposition.Present _, Proposition.InTheStrings _,
                 Proposition.SameValue _, Proposition.StringInside _, Proposition.LastToHold _,
                 Proposition.All _, Proposition.Any _,
                 Proposition.SoManyHold _, Proposition.Some _, Proposition.OnAnApplication _,
                 Proposition.SomeReachable _, Proposition.WhereItAnswers _,
                 Proposition.OfTheWays _ ->
                    BlockReason.WhatItStatesIsNoLine.Why.NO_RELATION_OF_NUMBERS;
            case Proposition.Carried carried -> throw carried.handedToAReader();
        });
    }

    /**
     * Whether a part that stopped for {@code why} is worded by each place the rule is filed at: a
     * form nothing takes apart, what an operation answered, or a value the terms name no position
     * for. The rest are a step of the reading, a figure of its work or something a call or an
     * invariant holds, and say the same at every place.
     */
    private static boolean wordedByThePlace(WhyUnread why) {
        return switch (why) {
            case WhyUnread.OutsideTheLinearFragment _, WhyUnread.NotArithmetic _,
                 WhyUnread.NoNumberOnARun _,
                 WhyUnread.TwoElementsOfOneContainer _, WhyUnread.NoLawFor _,
                 WhyUnread.NoWordsFor _, WhyUnread.NotProvedOfItsBody _,
                 WhyUnread.NoFormOfWhatItAnswers _,
                 WhyUnread.ANumberOfWhatAnOperationAnswers _,
                 WhyUnread.CodePointsOfWhatAnOperationAnswers _,
                 WhyUnread.WhatARecursiveHelperAnswers _, WhyUnread.AtNoPosition _,
                 WhyUnread.NoMeasureOfItsSize _, WhyUnread.WhichElementARunStopsAt _ -> true;
            case WhyUnread.MoreReadingsThanAreMade _, WhyUnread.MoreTotalReadingsThanAreMade _,
                 WhyUnread.MorePartsThanAreConcluded _, WhyUnread.MoreWaysThanAreWrittenOut _,
                 WhyUnread.MoreElementsThanAreWrittenOut _, WhyUnread.SeveralValuesNotGoneInto _, WhyUnread.ANumberNotHeld _,
                 WhyUnread.AClauseOfAnInvariant _, WhyUnread.AnInvariantNotReached _,
                 WhyUnread.InACalledBody _, WhyUnread.CopiesStateDifferentThings _,
                 WhyUnread.NotMetByTheReading _ -> false;
        };
    }

    /**
     * A statement of several lines read to the end and not taken apart, at each place the
     * comparison names.
     */
    private static Read severalNotDrawn(StatedComparison comparison, InputReading read,
                                        InputReads reads, Arrivals answering) {
        return new Read.Stopped(ComparisonAssessment.atEachOf(
                GuardThresholds.filedAt(comparison, read, reads, answering),
                new BlockReason.SeveralLinesInOneRule()));
    }

    /**
     * {@code stated}, read to the end, as the several lines it draws, each with where it decides —
     * every count of statements in it read as a count, where it stands outside the element of a
     * container, and written out as the choices of which hold inside one, all of them held to one
     * figure ({@link CountsWrittenOut}). Past that figure where its lines decide was not worked
     * out, and where none are drawn it is several lines not drawn, at each place the comparison is
     * filed at.
     *
     * <p>Unless a reading under a relation that drew no line stopped. The statement is then no line
     * for what stopped there, said as a statement holding a part nothing read is ({@link #noLine}).
     *
     * @param arithmetic what the comparison's own arithmetic came to, which words a stop each place
     *                   words for itself
     * @param working    what the rule that read the comparison tells of the operations its rows get
     *                   past
     * @param workingOfRelation what a relation read under an arm of a choice works out, or null
     *                   for one that was not
     */
    private static Read asLines(String behavior, StatedComparison comparison, Proposition stated,
                                Supplier<AffineReading.OfAComparison> arithmetic,
                                Supplier<UndividedByARelation.Working> working,
                                Function<Relation, UndividedByARelation.Working> workingOfRelation,
                                InputReading read, InputReads reads, Arrivals answering,
                                Optional<AuthorsLines> authors) {
        return switch (CountsWrittenOut.outsideElementsOf(stated)) {
            case CountsWrittenOut.PastAFigure(CompositionBudget figure) ->
                    new Read.Stopped(ComparisonAssessment.atEachOf(
                            GuardThresholds.filedAt(comparison, read, reads, answering),
                            new BlockReason.WhereALineDecidesNotWorkedOut(figure.figure())));
            case CountsWrittenOut.Written(Proposition written) ->
                    switch (several(behavior, comparison.left(), written, read, reads, authors,
                            relation -> {
                                UndividedByARelation.Working own = relation == null ? null
                                        : workingOfRelation.apply(relation);
                                return own != null ? own : working.get();
                            })) {
                        case TheParts.Drawn(Read.Several lines) -> lines;
                        case TheParts.NotDrawn none when none.readToTheEnd() ->
                                severalNotDrawn(comparison, read, reads, answering);
                        case TheParts.NotDrawn(var stops, var beyondTheForm) -> noLine(comparison,
                                stated, stops, beyondTheForm, arithmetic, read, reads, answering);
                    };
        };
    }

    /**
     * What a statement of several relations comes to as lines: a line for each, or none drawn.
     *
     * <p>None drawn is said with why the relations that drew no line are none. A relation over a
     * value bound in the body, whose making a reading stopped at, is no line because of that stop,
     * and a relation over what two numbers come to multiplied, held against anything but a number,
     * because no line is drawn through a product. Where some relation that drew no line is neither,
     * it was read to the end, and so is the statement: several lines held together, whatever the
     * others stopped at, since naming their stop would say of that relation that it was not there.
     */
    private sealed interface TheParts {

        /** None drawn, and every relation read to the end. */
        NotDrawn READ_TO_THE_END = new NotDrawn(List.of(), Set.of());

        /** A line for each relation, drawn or refused, or some line drawn beside the rest. */
        record Drawn(Read.Several lines) implements TheParts {}

        /**
         * No line drawn.
         *
         * @param stops         what stopped the readings under the relations that drew no line, in
         *                      the order the relations are held
         * @param beyondTheForm the arithmetic in them, read, that no line is drawn through
         */
        record NotDrawn(List<WhyUnread> stops, Set<NonAffineOperation> beyondTheForm)
                implements TheParts {

            public NotDrawn {
                stops = List.copyOf(stops);
                beyondTheForm = Set.copyOf(beyondTheForm);
            }

            /** Whether nothing stopped under any relation and none of them is arithmetic no line
             *  is drawn through. */
            boolean readToTheEnd() {
                return stops.isEmpty() && beyondTheForm.isEmpty();
            }

            /** This and {@code other} together, each kept in its order. */
            NotDrawn and(NotDrawn other) {
                List<WhyUnread> allStops = new ArrayList<>(stops);
                allStops.addAll(other.stops);
                Set<NonAffineOperation> allBeyond = EnumSet.noneOf(NonAffineOperation.class);
                allBeyond.addAll(beyondTheForm);
                allBeyond.addAll(other.beyondTheForm);
                return new NotDrawn(allStops, allBeyond);
            }
        }
    }

    /**
     * What an application of an operation answering a truth states, read to the end, on the input:
     * the lines its relations draw, or the values it relates — or null where it is neither.
     *
     * <p>A rule of its own, as a comparison is. {@code List.all(l -> o.floor > 3, o.lines)} holds
     * where {@code o.lines} is empty or {@code o.floor} is above three, and the first of those is
     * stated by the application and by nothing else written there; the second is the comparison's,
     * and the application states it again, as a comparison over a choice states what the choice
     * turned on.
     *
     * <p>And {@code Set.contains(p, s)} holds where some element of {@code s} is {@code p}, which
     * relates the values at two positions and divides neither ({@link #valuesItRelates}).
     *
     * @param authors which of the lines the author of the application drew each relation it states
     *                is a place of, and how it stands to each ({@link WrittenLines})
     */
    static Read ofAnApplication(String behavior, Core application, Proposition stated,
                                InputReading read, InputReads reads,
                                AuthorsLines authors) {
        // A statement holding counts whose choices are past their figure is no rule of the
        // application's own, as one holding a part nothing read is not: what it reads is read
        // where its comparisons are written, each on its own.
        if (CountsWrittenOut.outsideElementsOf(stated)
                instanceof CountsWrittenOut.Written(Proposition written)
                && several(behavior, application, written, read, reads, Optional.of(authors),
                        _ -> UndividedByARelation.Working.UNREAD)
                        instanceof TheParts.Drawn(Read.Several lines)) {
            return lines;
        }
        List<FilingCoordinate> related = valuesItRelates(stated);
        return related == null ? null : against(related, stated);
    }

    /** The numbers of the input the string {@code quantity} is made of: itself where it is one,
     *  or those the operation that answered it was handed — or null where it is neither. */
    private static List<NumericTerm> stringsOf(Quantity quantity) {
        return switch (quantity) {
            case DecisionAtom.OfTheInput(NumericTerm term) -> List.of(term);
            case Quantity.WhatAnOperationAnswers answers -> answers.positionsItIsMadeOf();
            default -> null;
        };
    }

    /**
     * A relation {@code stated} that relates the input at {@code over}, as the relations it is
     * made of.
     *
     * <p>A form is held as the form it is, and a count in it as what it counts: how many elements
     * of one container are one of another's holds the two elements as one value, and how many
     * different values a container holds holds its elements against one another. A statement that
     * two values are one, some element of a container being one or not, is held as the two values
     * of its one such part; one of several such parts holds the values it relates to the others as
     * well, and nothing here shows what the whole of them leaves undivided.
     */
    private static Read.AgainstAnotherValue against(List<FilingCoordinate> over,
                                                    Proposition stated) {
        List<UndividedByARelation> relations = new ArrayList<>();
        if (stated instanceof Proposition.Compared(Relation.Affine affine, boolean _, Spelling _)) {
            relations.add(UndividedByARelation.ofAForm(affine.form(), affine.proposition()));
            for (Quantity each : affine.form().coefs().keySet()) {
                switch (each) {
                    case Quantity.HowManyMeet count -> relations.add(oneValue(count.ofTheElement()));
                    case Quantity.HowManyDifferent different -> different.ofTheElement().heldAt()
                            .forEach(at -> relations.add(UndividedByARelation.amongTheValuesAt(at)));
                    case Quantity.HowManyDifferentAcross across -> relations.add(
                            UndividedByARelation.amongTheValuesAt(
                                    across.ofTheOccurrence().inputPosition()));
                    // The values collected are held against one another, and so are the keys that
                    // pick them: a key is only asked to be, or not to be, the key of an entry.
                    // Neither is put in order, so no line is drawn on either, and no equality of
                    // two of them is a rule here.
                    case Quantity.HowManyDifferentBelow below -> relations.add(
                            UndividedByARelation.amongTheValuesAt(List.of(below.keyOfTheRoot(),
                                    below.map().key(), below.valueOfAnEntry())));
                    default -> { }
                }
            }
        } else {
            relations.add(oneValue(stated));
        }
        return new Read.AgainstAnotherValue(over, relations);
    }

    /**
     * What a statement made on each of the values a name stands for relates, where every statement
     * relates the input to another value: the relation of each, read on the rows its value is the
     * name's — as the applications of a closure are — or null where one of them is anything else.
     */
    private static Read.AgainstAnotherValue againstAnotherValueOnEach(
            Proposition.OnAnApplication applied) {
        List<FilingCoordinate> over = new ArrayList<>();
        List<UndividedByARelation> relations = new ArrayList<>();
        for (Proposition each : applied.each()) {
            List<FilingCoordinate> related =
                    each instanceof Proposition.Compared ? relatedToAnotherValue(each) : null;
            if (related == null) {
                return null;
            }
            related.stream().filter(at -> !over.contains(at)).forEach(over::add);
            relations.addAll(against(related, each).relations());
        }
        return new Read.AgainstAnotherValue(over, relations);
    }

    /**
     * {@code stated} held as the two values of its one statement that two values are one, or the
     * two strings of its one statement that one string stands inside another.
     */
    private static UndividedByARelation oneValue(Proposition stated) {
        List<Proposition.SameValue> same = new ArrayList<>();
        sameValuesIn(stated, same);
        if (same.size() == 1 && same.getFirst() instanceof Proposition.SameValue(
                DecisionSubject.AnInput(TermPath one), DecisionSubject.AnInput(TermPath other),
                boolean _, Spelling _)) {
            return UndividedByARelation.ofTwoPositions(one, other);
        }
        List<Proposition.StringInside> inside = new ArrayList<>();
        stringsInsideIn(stated, inside);
        return same.isEmpty() && inside.size() == 1
                ? UndividedByARelation.ofAStringInside(inside.getFirst().inner(),
                        inside.getFirst().outer(), inside.getFirst().where())
                : UndividedByARelation.SHOWING_NOTHING;
    }

    /** Every statement of one string standing inside another {@code stated} is made of. */
    private static void stringsInsideIn(Proposition stated, List<Proposition.StringInside> out) {
        switch (stated) {
            case Proposition.StringInside inside -> out.add(inside);
            case Proposition.Some some -> stringsInsideIn(some.ofTheElement(), out);
            case Proposition.All all -> all.parts().forEach(each -> stringsInsideIn(each, out));
            case Proposition.Any any -> any.parts().forEach(each -> stringsInsideIn(each, out));
            case Proposition.SoManyHold counted ->
                    counted.statements().forEach(each -> stringsInsideIn(each, out));
            case Proposition.WhereItAnswers where -> {
                stringsInsideIn(where.answers(), out);
                stringsInsideIn(where.states(), out);
            }
            default -> { }
        }
    }

    /** Every statement of two values being one {@code stated} is made of. */
    private static void sameValuesIn(Proposition stated, List<Proposition.SameValue> out) {
        switch (stated) {
            case Proposition.SameValue same -> out.add(same);
            case Proposition.Some some -> sameValuesIn(some.ofTheElement(), out);
            case Proposition.All all -> all.parts().forEach(each -> sameValuesIn(each, out));
            case Proposition.Any any -> any.parts().forEach(each -> sameValuesIn(each, out));
            case Proposition.SoManyHold counted ->
                    counted.statements().forEach(each -> sameValuesIn(each, out));
            case Proposition.WhereItAnswers where -> {
                sameValuesIn(where.answers(), out);
                sameValuesIn(where.states(), out);
            }
            default -> { }
        }
    }

    /**
     * Whether {@code stated} says only which case, which truth or whether a value positions of the
     * input hold, or that some element of a container the input holds meets that, joined: no
     * relation of numbers and nothing about what a dependency answered anywhere in it.
     */
    static boolean statesNoRelation(Proposition stated) {
        return switch (stated) {
            case Proposition.InCases cases -> cases.of() instanceof DecisionSubject.AnInput;
            case Proposition.Truth truth -> truth.of() instanceof DecisionSubject.AnInput;
            case Proposition.Present present -> present.of() instanceof DecisionSubject.AnInput;
            case Proposition.Some some -> some.container() instanceof DecisionSubject.AnInput
                    && statesNoRelation(some.ofTheElement());
            case Proposition.All all -> all.parts().stream().allMatch(Cutting::statesNoRelation);
            case Proposition.Any any -> any.parts().stream().allMatch(Cutting::statesNoRelation);
            case Proposition.SoManyHold counted ->
                    counted.statements().stream().allMatch(Cutting::statesNoRelation);
            case Proposition.WhereItAnswers where ->
                    statesNoRelation(where.answers()) && statesNoRelation(where.states());
            case Proposition.OfTheWays ways -> statesNoRelation(ways.written());
            // Settled, a relation, two values being one, or something nobody read: each is read
            // as what it is ({@link #readOnce}). And which strings a string is one of, which is
            // read where the rules about a position's strings are, and is no line of numbers.
            case Proposition.Always _, Proposition.Compared _, Proposition.SameValue _,
                 Proposition.StringInside _, Proposition.Unread _, Proposition.LastToHold _,
                 Proposition.OnAnApplication _, Proposition.SomeReachable _,
                 Proposition.InTheStrings _ -> false;
            case Proposition.Carried carried -> throw carried.handedToAReader();
        };
    }

    /**
     * Where every part of {@code stated} says that two values of the input are one value — some
     * element of a container being one, or not — the places of those values; null otherwise.
     *
     * <p>Two values being one is a relation between them, and a class of a position is a set of
     * that position's values: the statement divides neither, whichever way it comes out.
     */
    static List<FilingCoordinate> valuesItRelates(Proposition stated) {
        List<FilingCoordinate> out = new ArrayList<>();
        return relates(stated, out) && !out.isEmpty() ? List.copyOf(out) : null;
    }

    private static boolean relates(Proposition stated, List<FilingCoordinate> out) {
        return switch (stated) {
            case Proposition.SameValue(DecisionSubject.AnInput(TermPath one),
                                       DecisionSubject.AnInput(TermPath other), boolean _,
                                       Spelling _) -> {
                for (TermPath each : List.of(one, other)) {
                    if (!out.contains(FilingCoordinate.at(each))) {
                        out.add(FilingCoordinate.at(each));
                    }
                }
                yield true;
            }
            // A string inside another relates the strings, and each is a value of the input or
            // what an operation answers of one: the places it is made of are the places related.
            case Proposition.StringInside inside -> {
                List<NumericTerm> inner = stringsOf(inside.inner());
                List<NumericTerm> outer = stringsOf(inside.outer());
                if (inner == null || outer == null) {
                    yield false;
                }
                for (NumericTerm each : Stream.concat(inner.stream(), outer.stream()).toList()) {
                    if (!out.contains(FilingCoordinate.of(each))) {
                        out.add(FilingCoordinate.of(each));
                    }
                }
                yield true;
            }
            case Proposition.Some some -> relates(some.ofTheElement(), out);
            // Which of the elements holding a value is the one meant names no place beside the
            // value's own, which the sameness has already filed.
            case Proposition.LastToHold _ -> true;
            case Proposition.All all -> all.parts().stream().allMatch(each -> relates(each, out));
            case Proposition.Any any -> any.parts().stream().allMatch(each -> relates(each, out));
            case Proposition.SoManyHold counted ->
                    counted.statements().stream().allMatch(each -> relates(each, out));
            case Proposition.WhereItAnswers where ->
                    relates(where.answers(), out) && relates(where.states(), out);
            default -> false;
        };
    }

    /**
     * The lines a statement of several relations draws, each with where it decides — or none drawn
     * where one of the relations is something this reading has no word for, where none of them is
     * drawn beside a relation that is no line, or where there is none.
     *
     * <p>One rule, read as many lines as it holds relations, each named by this reading and nothing
     * else: as each line of its author's it is a place of ({@link PartOfAComparison}). Where each
     * decides is part of what the line is: a row at {@code a = g} under {@code Int.max(a, b) <= g}
     * with {@code b} above {@code g} is answered the same way on both sides of the line, so it is
     * no row for it.
     *
     * <p>A relation that is a place of two of the author's lines is drawn for each, deciding where
     * the statement turns on it and a row takes the arms that line is under: a row there meets
     * both, and each is owed its own row.
     *
     * <p>Where each line decides is read off the whole statement, every relation in it, so a line
     * drawn beside a relation that is no line is drawn where the statement turns on it and not as
     * though the statement were only the lines. {@code Option.withDefault(0, List.find(p, xs)) >=
     * q} holds where some element meets {@code p} and the value found is at least {@code q}, or
     * where none does and {@code q} is at most nought: the line on {@code q} decides where no
     * element meets {@code p}, which a row says, and the value found is no position's, so the
     * relation on it is {@code q} related to another value ({@link Read.AgainstAnotherValue}). The
     * line on the elements decides where the two arms differ, which turns on the value found, and
     * no row can be asked that of its own values; it is said not drawn, at its own places.
     *
     * <p>A relation over what a dependency answered is the decision table's, and a relation over
     * anything else this has no word for leaves the statement undrawn. A part a row answers of its
     * own values and that is no relation — whether a position is true, whether it holds a value — is
     * no line, and is where the lines decide; any other part leaves it undrawn too.
     *
     * <p>Undrawn, it carries why every relation that drew no line is none ({@link #whyNoLine}), so
     * that none of them is said for the others; and where one of them is none for nothing that
     * stopped, it is several lines read to the end, and the others' stops are not said for it.
     *
     * @param written the construct the rule is written as, asked only which position it names
     *                first, which is the way each line is faced
     * @param authors which of the author's lines each relation is a place of, how it stands to
     *                each and where a row takes each one's arms ({@link WrittenLines}); nothing
     *                for a clause, which no body wrote and whose lines are its own relations
     * @param working what a line works out, which its rows get past: what the reading of the
     *                comparison the statement is of told, or what was read of the line itself
     *                where it was read under an arm of a choice
     */
    private static TheParts several(String behavior, Core written,
                                    Proposition stated, InputReading read, InputReads reads,
                                    Optional<AuthorsLines> authors,
                                    Function<Relation, UndividedByARelation.Working> working) {
        if (!onlyRelations(stated)
                && !(holdsARelation(stated)
                        && AStatementAtARow.askableBesideItsRelations(stated))) {
            return TheParts.READ_TO_THE_END;
        }
        List<WhereEachLineDecides.Decides> lines = WhereEachLineDecides.in(stated);
        if (lines.isEmpty()) {
            return TheParts.READ_TO_THE_END;
        }
        List<Read.Several.Part> parts = new ArrayList<>();
        // Why the relations that drew no line are none, from the first of them on.
        TheParts.NotDrawn undrawn = null;
        for (WhereEachLineDecides.Decides each : lines) {
            Read line = lineOf(behavior, each.line(), written, read, reads);
            PlaceOfALine alone = new PlaceOfALine(THE_COMPARISON,
                    each.line().spelling().toString());
            if (line == null) {
                // A relation of the input's values to another value is that, beside the lines,
                // read as one comparison stating it alone is. One over what a dependency answered
                // is the decision table's, and anything else is no part this reading has a word
                // for: nothing is drawn.
                List<FilingCoordinate> against = Proposition.aboutAnAnswer(each.line()) ? null
                        : relatedToAnotherValue(each.line());
                if (against == null) {
                    TheParts.NotDrawn why = whyNoLine(each.line());
                    if (why.readToTheEnd()) {
                        return TheParts.READ_TO_THE_END;
                    }
                    undrawn = undrawn == null ? why : undrawn.and(why);
                } else if (undrawn == null) {
                    // Where it decides is carried only if a row can be asked to be there.
                    parts.add(new Read.Several.Part(alone, against(against, each.line()),
                            each.cases().stream().allMatch(
                                    one -> AStatementAtARow.askable(one.condition()))
                                    ? each.cases() : List.of()));
                }
                continue;
            }
            // Past a relation that leaves the statement undrawn, the rest are drawn only to see
            // whether one of them is no line for nothing that stopped.
            if (undrawn != null) {
                continue;
            }
            // The line is the input's, and where it decides turns on a relation to a value no
            // position holds, which a row cannot be asked of its own values. Rows at it could not
            // be held to where it decides, so it is said not to be drawn, at its own places.
            if (line instanceof Read.Cuts cuts && !each.cases().stream()
                    .allMatch(one -> AStatementAtARow.askable(one.condition()))) {
                parts.add(new Read.Several.Part(alone, new Read.Stopped(ComparisonAssessment
                        .atEachOf(cuts.cutting().over(), new BlockReason.SeveralLinesInOneRule())),
                        List.of()));
                continue;
            }
            if (authors.isEmpty()) {
                parts.add(new Read.Several.Part(alone, line, each.cases(),
                        workingOf(working, each.line())));
                continue;
            }
            authorsLines(authors.get(), each.scales(), WrittenLines.claimOf(each.line()))
                    .forEach((of, mapping) -> parts.add(
                    new Read.Several.Part(new PlaceOfALine(of, each.line().spelling().toString()),
                            authored(line, mapping, each.line()),
                            WhereEachLineDecides.takenWhere(each.cases(),
                                    authors.get().takenWhere(mapping.line())),
                            workingOf(working, each.line()))));
        }
        // Read as its parts where each is a line on the input, drawn or refused, or where some line
        // is drawn beside what is no line. With no line drawn and some part no line, nothing of it
        // is on the input to be taken apart, and it is several lines not drawn at the places the
        // comparison is filed at.
        if (undrawn != null) {
            return undrawn;
        }
        boolean drawn = parts.stream().anyMatch(part -> part.line() instanceof Read.Cuts);
        boolean allLines = parts.stream().allMatch(part -> Read.Several.Part.isALine(part.line()));
        return drawn || allLines ? new TheParts.Drawn(new Read.Several(parts))
                : TheParts.READ_TO_THE_END;
    }

    /** What the rows of {@code line} work out, as {@code working} says of its relation. */
    private static UndividedByARelation.Working workingOf(
            Function<Relation, UndividedByARelation.Working> working, Proposition line) {
        return working.apply(line instanceof Proposition.Compared compared ? compared.relation()
                : null);
    }

    /**
     * The quantity a row is read at to say whether {@code form} holds there: the form's own terms
     * with the constant left out, each on the order it stands on.
     *
     * <p>Decided here, where every other quantity a relation is over is decided: a reader of where
     * a line decides holds the relation and asks this for what to read.
     *
     * <p>A sum where every order has numbers under it, and the two positions apart where they are
     * two held against each other on an order with none: two strings stand no measurable distance
     * apart and are still one above the other, which is how {@link #readOnce} reads the same pair.
     *
     * @return null where some order has no numbers under it and the form is not two positions held
     *         against each other: a form no quantity reads a row at, which a reader of rows says it
     *         could not read rather than answering for
     */
    static LinearQuantity readAt(String behavior, LinearForm<NumericTerm> form,
                                 Quantities quantities) {
        Map<NumericTerm, TermOrders> on = new LinkedHashMap<>();
        form.coefs().keySet().forEach(term -> on.put(term, quantities.ordersOf(term)));
        return readAt(behavior, form, on);
    }

    /**
     * The same, with each of the form's terms already on the orders the reading gave it — held to
     * the form here, since which quantity it is turns on those orders and a map about other terms
     * would decide it for them.
     */
    static LinearQuantity readAt(String behavior, LinearForm<NumericTerm> form,
                                 Map<NumericTerm, TermOrders> on) {
        if (!on.keySet().equals(form.coefs().keySet())) {
            throw new IllegalArgumentException("a form is read on the orders of its own terms: "
                    + form + " against " + on.keySet());
        }
        on.forEach((term, orders) -> orders.areOf(term));
        if (on.values().stream().allMatch(orders -> orders.answered().counts())) {
            return new BorderQuantity.OverAForm(behavior,
                    new LinearForm<>(ExactRatio.ZERO, form.coefs()), on);
        }
        return heldAgainstEachOther(behavior, form, on);
    }

    /**
     * The two positions {@code form} holds against each other ({@link AffineReading#twoCoordinates})
     * on orders a value of one stands somewhere on — or null where it is no such pair.
     */
    private static BorderQuantity.Apart heldAgainstEachOther(String behavior,
                                                             LinearForm<NumericTerm> form,
                                                             Map<NumericTerm, TermOrders> on) {
        NumericTerm[] pair = AffineReading.twoCoordinates(form);
        if (pair == null) {
            return null;
        }
        TermOrders here = on.get(pair[0]);
        TermOrders there = on.get(pair[1]);
        here.areOf(pair[0]);
        there.areOf(pair[1]);
        if (here.term().atOnePosition() == null || there.term().atOnePosition() == null
                || !here.answered().standsAgainst(there.answered())) {
            return null;
        }
        return new BorderQuantity.Apart(behavior, here, there);
    }

    /** The same, for one position held against a place on the order it stands on. */
    static LinearQuantity readAt(String behavior, NumericTerm.FromOnePosition term,
                                 Quantities quantities) {
        return new BorderQuantity.OfACoordinate(behavior, term, quantities.ordersOf(term));
    }

    /**
     * Whether {@code stated} holds a relation joined with nothing a row cannot be asked about its
     * own values: {@code List.length(c.items) > 0 && c.open} is a line on how many items a cart
     * holds, deciding where the cart is open, and a row says whether it is.
     */
    static boolean drawsLines(Proposition stated) {
        return AStatementAtARow.askable(stated) && holdsARelation(stated);
    }

    private static boolean holdsARelation(Proposition stated) {
        return switch (stated) {
            case Proposition.Compared _ -> true;
            case Proposition.All all -> all.parts().stream().anyMatch(Cutting::holdsARelation);
            case Proposition.Any any -> any.parts().stream().anyMatch(Cutting::holdsARelation);
            case Proposition.SoManyHold counted ->
                    counted.statements().stream().anyMatch(Cutting::holdsARelation);
            // Some element meeting it or none: the relation turns what is said of an element
            // either way round.
            case Proposition.Some some -> holdsARelation(some.ofTheElement());
            // Where it answers is no line of it.
            case Proposition.WhereItAnswers where -> holdsARelation(where.states());
            default -> false;
        };
    }

    /** Whether every part {@code stated} joins is a relation. */
    static boolean onlyRelations(Proposition stated) {
        return switch (stated) {
            case Proposition.All all -> all.parts().stream().allMatch(Cutting::onlyRelations);
            case Proposition.Any any -> any.parts().stream().allMatch(Cutting::onlyRelations);
            case Proposition.SoManyHold counted ->
                    counted.statements().stream().allMatch(Cutting::onlyRelations);
            case Proposition.WhereItAnswers where ->
                    onlyRelations(where.answers()) && onlyRelations(where.states());
            case Proposition.Compared _ -> true;
            default -> false;
        };
    }

    /**
     * The line one relation draws on the input, or the refusal to place it — or null where the
     * relation is over something that is not the input's.
     */
    private static Read lineOf(String behavior, Proposition.Compared line, Core written,
                               InputReading read, InputReads reads) {
        return switch (line.relation()) {
            case Relation.Affine affine -> lineOn(behavior, affine, true, written, read, reads);
            case Relation.Ordered(DecisionAtom.OfTheInput(NumericTerm term), Place at, Rel rel)
                    when term.atOnePosition() != null ->
                    onAnOrder(behavior, term.atOnePosition(), at, rel, read.quantities());
            case Relation.Ordered _ -> null;
        };
    }

    /**
     * The line a relation of numbers draws on the input, or the refusal to place it — or null
     * where it is over nothing a line is drawn on.
     *
     * <p>Every way such a relation is a line, asked in one place for a comparison that states it
     * alone and for each relation of several. A form of the input's numbers is asked first; then
     * how many elements meet something, what a division leaves of a form, and what two numbers come
     * to multiplied, each a line on that number.
     *
     * @param holds whether the relation is stated or denied
     */
    private static Read lineOn(String behavior, Relation.Affine affine, boolean holds,
                               Core written, InputReading read, InputReads reads) {
        LinearForm<NumericTerm> over = WhatTheDeclarationsLeave.ofTheInput(affine.form());
        if (over != null) {
            return realized(behavior, AffineReading.stating(over,
                    holds ? affine.proposition() : affine.proposition().denied(),
                    written, reads, read), read.quantities());
        }
        return onANumberNoPositionHolds(behavior, affine, holds, read);
    }

    /**
     * The line a relation draws on a number of the input no position holds — how many elements
     * meet something, what a division leaves of a form, what two numbers come to multiplied — or
     * null where it is over none of them.
     *
     * <p>Every way such a relation is a line, for {@link #lineOn} and for what a case of where a
     * line decides leaves the line's own number ({@link #leftBy}).
     */
    private static Read onANumberNoPositionHolds(String behavior, Relation.Affine affine,
                                                 boolean holds, InputReading read) {
        return firstDrawn(onACount(behavior, affine, holds, read),
                () -> firstDrawn(onARemainder(behavior, affine, holds, read),
                        () -> firstDrawn(onARemainderByAnInput(behavior, affine, holds, read),
                                () -> onAProduct(behavior, affine, holds, read))));
    }

    /**
     * Where a comparison read to the end and the same for every row is said to cut nothing.
     *
     * <p>At the numbers of the input it was read over where a form of them cancelled, whether or
     * not they survived: {@code a - a <= 0} is about {@code a}, and a rule about a length that
     * cancels is about the length and not the string's own values. Where it was settled without a
     * number of the input being read — a law, the bounds of a sign, a value written out — at the
     * positions the comparison mentions, since that is all it was read over.
     */
    private static List<FilingCoordinate> settledAt(Pullback.Pulled stated,
                                                    StatedComparison comparison,
                                                    InputReading read, InputReads reads,
                                                    Arrivals answering) {
        return Derivation.Restated.through(stated.meaning().how())
                instanceof Derivation.ACutThatCutsNothing cut
                && !cut.named().isEmpty()
                ? AffineReading.filedAt(cut.named())
                : GuardThresholds.filedAt(comparison, read, reads, answering);
    }

    /**
     * The line a statement of one term against a place on its order draws, or the refusal to place
     * it: a date against a written date, a case of an enumeration.
     */
    private static Read onAnOrder(String behavior, NumericTerm.FromOnePosition term, Place at,
                                  Rel stated, Quantities quantities) {
        Cutting drawn = atAPosition(behavior, new ComparedLine(term, at, quantities.ordersOf(term),
                ComparisonClaim.stating(stated)), quantities);
        if (drawn == null) {
            throw new IllegalStateException("a statement on the order " + term + " stands on placed"
                    + " a line the order has no place for: " + at);
        }
        return cutsOrRefused(drawn);
    }

    /**
     * The same line, on the quantity taken at another position — or null where the quantity cannot
     * be taken there.
     *
     * <p>For a name that stands at more than one position. The comparison is read once and stays one
     * comparison; what moves is where its quantity is taken, and it is taken under each case a value
     * of the sum can turn out to be.
     *
     * <p>What the quantity runs between is worked out again here and not carried over. It is what
     * the rules leave the quantity, so a quantity taken somewhere else runs between whatever the
     * rules leave it there — kept as it was, a line would be held inside the values of the position
     * it came from.
     */
    Cutting movedTo(NumericTerm from, NumericTerm to, Quantities quantities) {
        // What the term it moves to is measured on, asked of the reading that is here anyway. Taken
        // as an argument beside the term, the two were free to be about two terms — and the reading
        // that would have settled it was being handed over in the same call.
        // A term moved is a term of a form; a quantity that is no form has none to move.
        if (!(of instanceof LinearQuantity form)) {
            return null;
        }
        LinearQuantity moved = form.movedTo(from, quantities.ordersOf(to));
        if (moved == null || !moved.levels().canCutAt(at)) {
            return null;
        }
        return new Cutting(moved, at, claim, quantities.runsBetween(moved.direction()), written,
                heldIn);
    }

    /**
     * Whether the rows {@code region} holds reach this line, which is what makes it a line the rule
     * draws.
     *
     * <p>One question wherever a line is asked about, and the region is what differs: what the
     * rules leave where the comparison is read and at every position filing moves the line to
     * ({@link #movedTo}), and what also arrives at the comparison where a body is walked to it. The
     * move takes the quantity somewhere the rules may leave it less room: a case whose invariant
     * stops short of the line is a quantity the line does not reach, however far the name it was
     * written at runs. Asked one way at all of them, the reading, the filing and the walk cannot
     * come to disagree about one line.
     *
     * <p>Two questions, and {@link Border#reaches} says which a rule asks ({@link Border.Values}).
     * How far the quantity runs inside the region is a question about its extent, and the region's
     * projection answers it. Whether a row stands at a value is a question about one equation, and
     * it is asked as one: the line taken in beside everything else the region holds and the region
     * asked whether anything is left. Read off the projection instead, a value the way holds the
     * quantity apart from would be inside the ends of everything around it — the ends of
     * everything but five are the ends of everything.
     *
     * @param drawnByAnInvariant whether a clause of a value's own declarations drew the line, which
     *                           has no far side for anything to stand on
     */
    boolean reachedIn(SearchRegion region, boolean drawnByAnInvariant) {
        return reachedBy(valuesIn(region), drawnByAnInvariant);
    }

    /**
     * {@link #reachedIn}, of what a region was already read to leave this quantity
     * ({@link #valuesIn}) — null where it leaves nothing.
     */
    boolean reachedBy(Border.Values values, boolean drawnByAnInvariant) {
        return values != null
                && Border.reaches(at, this::seam, claim, drawnByAnInvariant, values);
    }

    /**
     * Whether the rows some regions hold between them stand on both sides of a line — at the value
     * a rule names and beside it, for a rule that names one — taken in a region at a time, so that
     * no region is read once both sides are found.
     *
     * <p>What a line of a statement of several is asked in each case of where it decides. A case is
     * other relations holding or failing, and a row on one side of the line and a row on the other,
     * both in the case, differ in this relation alone — so the statement comes out differently for
     * them. Asked of one side only, a case could hold of the rows on one side and of none on the
     * other: {@code Int.min(a, 11 - a) > 5} decides on {@code 11 - a > 5} where {@code a > 5}, and
     * crossing from six to five takes {@code a > 5} with it, so the statement never turns there.
     *
     * <p>Each side is asked of every region and the two sides need not be found in one. The rows are
     * every row any region holds, so a row in one and a row in another differ in this line as two
     * rows of one do; and the values between the regions are no row's, so the regions are not put
     * together into one that spans them.
     *
     * <p>A side that was not worked out is not a proof that no row stands on it, as it is not in
     * {@link #reachedIn}.
     *
     * <p>Two sides for each claim. A line that cuts has the values below it and the values above
     * it. A line that names a value has the value and a row beside it on either side: with the
     * value put above the seam, the seam parts it from what is below; put below, from what is
     * above.
     */
    static final class Sides {

        private final Cutting line;

        private boolean one;

        private boolean other;

        Sides(Cutting line) {
            this.line = line;
        }

        /**
         * Takes in what one more region leaves the quantity ({@link #valuesIn}, null for
         * nothing), and answers whether the rows taken in so far stand on both sides.
         */
        boolean add(Border.Values values) {
            if (values != null) {
                switch (line.claim) {
                    case ComparisonClaim.Cut _ -> {
                        one = one || Border.standsBeside(line.at, line.seam(), Towards.BELOW,
                                values);
                        other = other || Border.standsBeside(line.at, line.seam(), Towards.ABOVE,
                                values);
                    }
                    case ComparisonClaim.Singled _ -> {
                        one = one || values.holdAt(line.at);
                        other = other
                                || Border.standsBeside(line.at,
                                        Seam.where(line.of, line.at, Towards.ABOVE),
                                        Towards.BELOW, values)
                                || Border.standsBeside(line.at,
                                        Seam.where(line.of, line.at, Towards.BELOW),
                                        Towards.ABOVE, values);
                    }
                }
            }
            return one && other;
        }
    }

    /**
     * What a region's values ({@link #valuesIn}) come to for the rows in {@code where}, a case of
     * where this line decides — the values themselves where the case says nothing more of this
     * line's quantity than the region does. What {@link Sides} takes in, in that case.
     *
     * <p>The region is what the way and the case leave the input's own numbers, and it says
     * nothing about a number no position holds. A case of where a line on such a number decides is
     * mostly other relations over that same number: {@code Int.max(0, a * b) <= 3} turns on where
     * the product is nought only where it is above three, and the region is the same on both sides
     * of nought whatever the case says. So what the case leaves this line's own quantity
     * ({@link #leftBy}) is asked beside the region, and a line no row crosses inside it turns
     * nothing there.
     *
     * <p>The two are asked apart, each for values on both sides, and not for one row meeting both:
     * a region holds nothing of the quantity's own values, so all it can say of them is a run. So
     * this answers that a row on each side is not ruled out, which is what keeps a case, and never
     * that one stands there — a product of ten and another number is three nowhere, though the
     * run and the case both hold three. Whether a row stands at each point is the search's, which
     * proves the points nothing can stand at, as it does for any line on the product.
     *
     * <p>Read off the case once, and asked of every region the case is put to: what the case
     * leaves the quantity is the same whatever arrives.
     */
    UnaryOperator<Border.Values> keptTo(Proposition where, InputReading read) {
        LevelRegion onIt = leftBy(where, read);
        return onIt == null ? UnaryOperator.identity()
                : values -> values == null ? null : keptTo(values, onIt);
    }

    private Border.Values keptTo(Border.Values values, LevelRegion onIt) {
        return new Border.Values() {
            @Override
            public boolean extendTo(Level level) {
                return values.extendTo(level) && onIt.parts().stream().anyMatch(part ->
                        new LevelInterval(withItsEnd(part.low()), withItsEnd(part.high()))
                                .contains(level));
            }

            @Override
            public boolean holdAt(Level level) {
                return values.holdAt(level) && onIt.contains(level);
            }

            @Override
            public boolean holdOnSide(Level level, Towards side, boolean including) {
                Bound end = Bound.at(level, including);
                LevelRegion past = LevelRegion.of(side == Towards.ABOVE
                        ? new LevelInterval(end, null) : new LevelInterval(null, end));
                // A run the order could not say anything of is no proof that nothing is there.
                return values.holdOnSide(level, side, including)
                        && onIt.meet(past).parts().stream().anyMatch(run -> {
                            Occupancy held = of.levels().inspect(run);
                            return held instanceof Occupancy.NotWorkedOut || held.any();
                        });
            }
        };
    }

    /** {@code end} keeping the value at its place, or no end. */
    private static Bound withItsEnd(Bound end) {
        return end == null ? null : new Bound(end.at(), true);
    }

    /**
     * What {@code where} leaves this line's own quantity, where it is a number no position holds:
     * every value each relation of it on that quantity leaves, read as a line on it would be — or
     * null where none of it is about the quantity, or where the quantity is a form of the input's
     * own numbers, which the region already holds every relation over.
     *
     * <p>Read the way the line itself was, by the reading that draws a line on such a number
     * ({@link #onANumberNoPositionHolds}). A relation that comes to a line on this same quantity
     * leaves it the values on the side it holds on; anything else in the case leaves it whatever it
     * had.
     */
    private LevelRegion leftBy(Proposition where, InputReading read) {
        if (of instanceof LinearQuantity) {
            return null;
        }
        return switch (where) {
            case Proposition.All all -> joined(all.parts(), read, true);
            case Proposition.Any any -> joined(any.parts(), read, false);
            case Proposition.Compared compared
                    when compared.relation() instanceof Relation.Affine affine
                    && onANumberNoPositionHolds(of.behavior(), affine, compared.holds(), read)
                            instanceof Read.Cuts(Cutting on, AuthoredPointMapping _)
                    && on.of().equals(of) -> on.holdsOn();
            default -> null;
        };
    }

    /**
     * What {@code parts} leave this quantity together: what every one of them leaves where
     * {@code every}, and what any one leaves where not — null where they leave it whatever it had.
     */
    private LevelRegion joined(List<Proposition> parts, InputReading read, boolean every) {
        LevelRegion out = null;
        for (Proposition part : parts) {
            LevelRegion one = leftBy(part, read);
            if (one == null) {
                if (every) {
                    continue;
                }
                return null;
            }
            if (out == null) {
                out = one;
            } else if (every) {
                out = out.meet(one);
            } else {
                List<LevelInterval> either = new ArrayList<>(out.parts());
                either.addAll(one.parts());
                out = new LevelRegion(either);
            }
        }
        return out;
    }

    /** The values of this quantity the comparison holds at. */
    private LevelRegion holdsOn() {
        return switch (claim.statedRelation()) {
            case EQ -> LevelRegion.point(at);
            case NE -> LevelRegion.EVERYTHING.without(at);
            case GE -> LevelRegion.of(new LevelInterval(Bound.at(at, true), null));
            case GT -> LevelRegion.of(new LevelInterval(Bound.at(at, false), null));
            case LE -> LevelRegion.of(new LevelInterval(null, Bound.at(at, true)));
            case LT -> LevelRegion.of(new LevelInterval(null, Bound.at(at, false)));
        };
    }

    /**
     * What {@code region} leaves this quantity, as the two questions a line asks of it — or null
     * where it leaves the quantity nothing at all.
     */
    Border.Values valuesIn(SearchRegion region) {
        NumericDomain.FormProjection runs = of.projectedIn(region);
        if (runs instanceof NumericDomain.FormProjection.NothingIsLeft) {
            return null;
        }
        Border.Values extent = Border.Values.within(
                runs instanceof NumericDomain.FormProjection.Within(NumericDomain.Bounds range)
                        ? range : null);
        // What the declarations hold a position's value to inside where it runs, which a value is
        // refused by before the region is asked anything: a position held to "a" or "b" takes no
        // value at "a0", whatever the region says of the strings — and a form over that one
        // position takes no value none of them comes to. A side of a line is not asked it: the
        // side runs to an end of the range, and the range ends at a value the declarations leave.
        HeldValues held = of.heldIn(region);
        // And what the language holds of it, which is no rule and so is in no region: asked of a
        // level and a side as the run the region leaves is, and drawn into no class.
        HeldByTheLanguage language = of.heldByTheLanguage();
        return new Border.Values() {
            @Override
            public boolean extendTo(Level level) {
                return language.admits(level) && extent.extendTo(level);
            }

            @Override
            public boolean holdAt(Level level) {
                if (held.refuses(level) || !language.admits(level)) {
                    return false;
                }
                // Whether a row stands at the value is asked of a value the quantity takes. One
                // it never takes is the order's answer and not the rows': `2 * a == 9` names
                // nothing an integer is twice, under any rules, and the line is the order's to
                // place (`Places.AT_NO_VALUE`). Asked of a region, that is a region holding no
                // row at a value no row could ever hold.
                if (!Boolean.TRUE.equals(of.levels().attainable(level).orNull())) {
                    return extent.extendTo(level);
                }
                // An equation this region cannot carry is no proof that nothing stands there. What
                // the quantity runs between is asked first and settles it where the value is past
                // either end: a form taken into a region is taken in without what its numbers
                // guarantee of themselves, so the equation of an hour of thirty is one it finds
                // nothing wrong with.
                //
                // Only a value, and not the sides of a line. Whether the rule turns at a line is
                // asked of the region as it is, so that a line drawn at the floor of a number is
                // still a line the author drew: how often a key occurs is never below one, and a
                // rule at one is read as a line with its far side excluded rather than as none.
                return extent.extendTo(level) && atTheLevel(region, level)
                        .map(there -> there.emptiness().isEmpty()).orElse(true);
            }

            @Override
            public boolean holdOnSide(Level level, Towards side, boolean including) {
                // The region with the quantity held on that side of the level, asked whether
                // anything is left. A relation it cannot carry is no proof that nothing is there.
                Rel past = side == Towards.ABOVE ? (including ? Rel.GE : Rel.GT)
                        : (including ? Rel.LE : Rel.LT);
                return language.holdsOnSide(level, side, including)
                        && against(region, level, past)
                                .map(there -> there.emptiness().isEmpty()).orElse(true);
            }
        };
    }

    /**
     * {@code region} with what arrives at the comparison taken in, where what arrives is about a
     * position this quantity is over.
     *
     * <p>A range of one position is a constraint on that position and is taken in as one, so it
     * narrows the quantity whatever form of the position it is — the position itself, a multiple
     * of it, or a sum it is a term of. A range of a position the quantity is not over says nothing
     * about this line, and the region is not asked to name a position it may hold no rules for.
     *
     * <p>An end the region cannot carry narrows nothing, which still holds every row that arrives.
     */
    SearchRegion narrowedBy(ComparisonArrival.Values arriving, SearchRegion region) {
        NumericTerm.FromOnePosition position = new NumericTerm.ValueOf(arriving.path());
        if (!(of instanceof LinearQuantity form) || !form.direction().coefs().containsKey(position)) {
            return region;
        }
        NumericDomain.Bounds bounds = arriving.bounds();
        SearchRegion out = region;
        if (bounds.min() != null) {
            out = taking(out, position, bounds.min(), bounds.min().inclusive() ? Rel.GE : Rel.GT);
        }
        if (bounds.max() != null) {
            out = taking(out, position, bounds.max(), bounds.max().inclusive() ? Rel.LE : Rel.LT);
        }
        return out;
    }

    /** {@code region} with {@code position rel end} taken in, in the vocabulary its place is in. */
    private static SearchRegion taking(SearchRegion region, NumericTerm.FromOnePosition position,
                                       Endpoint end, Rel rel) {
        if (!(end.at() instanceof Count count)) {
            return region.assuming(position, end.at(), rel);
        }
        return region.assuming(LinearForm.<NumericTerm>atomMinusConstant(position, count.exactly()),
                rel) instanceof SearchRegion.Assumption.Taken(SearchRegion narrower)
                ? narrower : region;
    }

    /**
     * {@code region} with this quantity taken to stand at {@code level}: the line as an equation,
     * in whichever vocabulary the level is in.
     *
     * <p>A number is a level of the form the rule wrote, so the equation is the form less it — over
     * one position or several, weighed or not. A level that is no number is a place on an order
     * that counts nothing, which only one position's own value stands on, and the equation is that
     * position at that place.
     *
     * <p>Empty where the equation cannot be said: the form less the level past what the exact
     * arithmetic holds, or a region with no way to carry it.
     */
    private Optional<SearchRegion> atTheLevel(SearchRegion region, Level level) {
        return against(region, level, Rel.EQ);
    }

    /**
     * {@code region} with this quantity taken to stand {@code rel} {@code level}, in whichever
     * vocabulary the level is in — or empty where that cannot be said, as {@link #atTheLevel} is.
     */
    private Optional<SearchRegion> against(SearchRegion region, Level level, Rel rel) {
        // A region holds relations over a row's numbers, and a quantity that is no form of them is
        // one no relation it holds is about.
        if (!(of instanceof LinearQuantity written)) {
            return Optional.empty();
        }
        LinearForm<NumericTerm> direction = written.direction();
        ExactRatio number = level.asANumber();
        if (number != null) {
            LinearForm<NumericTerm> form = direction.minus(LinearForm.constant(number)).orNull();
            return form != null
                    && region.assuming(form, rel)
                            instanceof SearchRegion.Assumption.Taken(SearchRegion there)
                    ? Optional.of(there) : Optional.empty();
        }
        if (direction.coefs().size() != 1 || direction.constant().signum() != 0) {
            return Optional.empty();
        }
        Map.Entry<NumericTerm, ExactRatio> only = direction.coefs().entrySet().iterator().next();
        NumericTerm.FromOnePosition position = only.getKey().atOnePosition();
        return position == null || !only.getValue().equals(ExactRatio.ONE) ? Optional.empty()
                : Optional.of(region.assuming(position, level.asAPlace(), rel));
    }

    /**
     * The line the canonical quantity draws, or the reading stopping on the order it is on.
     *
     * <p>Three shapes and one order among them, which is the arithmetic's: one position's own
     * values, two positions held apart, and a form over several. Nothing here reads the comparison
     * again — what each of them is handed is the form the reading already came to.
     *
     * <p><b>A shape declining and a recognised shape failing to draw are two different things.</b>
     * A recogniser answers nothing where the form is not its shape and where the orders that shape
     * would need are not there. The second of those is a fact about the model — an order is missing,
     * and that is worth saying — but it is not this reading's to classify, because a reading further
     * down may still answer: a form on an order that counts nothing is turned away by both narrower
     * shapes and gets its line from neither, and what it is left with is settled at the one place
     * that knows it has run out of readings.
     *
     * <p>What must not happen is the other one: a shape that was recognised and then could not be
     * realized falling to the next reading, where whatever that reading is short of becomes the
     * reason. So a recogniser is asked first and its answer decides which reading owns the form,
     * and only then is a line built.
     *
     * <p>And that one place is after the narrower shapes, not before them. They reach orders this
     * counts nothing on: two strings stand no measurable distance apart and the place they meet is
     * still a line, so a reader asking for counting orders first refuses lines the model draws.
     */
    private static Read realized(String behavior, AffineReading read,
                                 Quantities quantities) {
        // Which shape this quantity is, asked narrowest first, and each answered before anything is
        // built. A recogniser answering nothing is this form not being that shape, and the next
        // shape is asked; a recogniser that answered and a line that then could not be built are
        // two facts about one shape, and falling from the second to the next shape is how the
        // first came to be reported as the last one's absence.
        ComparedLine line = ComparedLine.fromTheForm(read, quantities);
        if (line != null) {
            return cutsOrRefused(realizedAt(atAPosition(behavior, line, quantities),
                    "a line on one position", read));
        }
        ComparedTerms pair = ComparedTerms.fromTheForm(read, quantities);
        if (pair != null) {
            return cutsOrRefused(realizedAt(apart(behavior, pair, read.claim(), quantities),
                    "a distance between two positions", read));
        }
        // And what the general form needs, asked once and here. Not before the two above: they
        // reach orders that do not count — two strings stand no measurable distance apart and the
        // place they meet is a line — so a reader asking this first would refuse lines the model
        // draws.
        Map<NumericTerm, TermOrders> on = read.carriers(quantities);
        if (on == null) {
            return new Read.NoOrderToCountOn(
                    AffineReading.filedAt(read.form().coefs().keySet()));
        }
        return cutsOrRefused(overAForm(behavior, read, on, quantities));
    }

    /**
     * The line a recognised shape draws, which is one it draws.
     *
     * <p>What is watched here is a shape this reading recognised and could not put a line on. Only
     * one thing refuses past recognition — an order with no place at the level the rule wrote
     * ({@link LevelSpace#canCutAt}) — and it is a fact about the model rather than a limit of this
     * compiler: a rule holding two strings three apart asks for a line at a distance the order has
     * no place for at all, and there is none to find.
     *
     * <p>Unreachable while the language admits no arithmetic over an order that counts nothing, so
     * a distance on such an order is only ever the place the two meet, which every such order has.
     * That is a fact about what can be written and not about these types, so it stops here rather
     * than falling to the reading below — where a shape that was recognised would have been
     * answered for by whether the general form's orders were there, and gone out as values nothing
     * draws a line on.
     */
    private static Cutting realizedAt(Cutting drawn, String shape, AffineReading read) {
        if (drawn == null) {
            throw new IllegalStateException("this reading recognised " + shape
                    + " and its order has no place at the level the rule wrote: "
                    + read.form() + " at " + read.cut());
        }
        return drawn;
    }

    /** One position's own values, cut where the reading found the line, or null where that reading
     *  found none and where the order has no place for the one it found. */
    private static Cutting atAPosition(String behavior, ComparedLine drawn,
                                       Quantities quantities) {
        if (drawn == null) {
            return null;
        }
        return made(new BorderQuantity.OfACoordinate(behavior, drawn.term(), drawn.orders()),
                new Level.OnACarrier(drawn.orders().answered(), drawn.value()), drawn.claim(),
                quantities);
    }

    /** How far two positions stand apart, cut where the reading found the line, or null on the same
     *  two counts. */
    private static Cutting apart(String behavior, ComparedTerms drawn, ComparisonClaim claim,
                                 Quantities quantities) {
        if (drawn == null) {
            return null;
        }
        return made(new BorderQuantity.Apart(behavior, drawn.on(), drawn.against()),
                new Level.OfTheQuantity(drawn.stepsApart().exactly()), claim, quantities);
    }

    /**
     * One line, with what the rules leave the quantity it is on.
     *
     * <p>Asked of every quantity and not of the one shape that used to ask. What a quantity runs
     * between is a question about the quantity, which {@link BorderQuantity#runsWithin} answers for
     * every quantity alike; asked only where the quantity was a form, a rule cutting a length at a negative drew a
     * border where a length never goes, and a row was owed at a value no row can carry.
     *
     * <p>Asked of the reading of the input rather than composed from what each of the form's
     * positions runs between: a product of per-position answers cannot carry a rule relating them,
     * so two fields a record holds at five together came to ten and a border was drawn where the
     * model has nothing.
     */
    private static Cutting made(BorderQuantity of, Level at, ComparisonClaim claim,
                                Quantities quantities) {
        // Whether the order has a place at that level for a line to be, which is the order's answer
        // and not the carrier's. An order whose only number is where two positions meet has one
        // place and no others; every order that counts is parted anywhere, whether or not it takes
        // the level itself.
        if (!of.levels().canCutAt(at)) {
            return null;
        }
        return new Cutting(of, at, claim, of.runsWithin(quantities));
    }

    /**
     * The line an arithmetic form over several positions draws.
     *
     * <p>Read where neither of the narrower readings could be, and about the same comparison. This
     * is the case domain testing exists for — a partition defined by a condition over more than one
     * variable — and the four sides of the box its positions sit in are not it.
     *
     * <p>Each position on the order it is written back on, which the reading answers per position.
     * The orders are the parameter and not something asked for here: a position with no number is
     * one a sum has nothing to add, and whether every term has one is what the caller settled
     * before choosing this shape at all. So this draws a line and never declines — left able to,
     * the next refusal added to it would arrive where a missing order is reported and be described
     * as one.
     *
     * <p><b>Whatever the operator states, and not orders alone.</b> {@code 2 * a == 8} names four
     * and {@code a + b == 10} names the place their sum reaches ten, and both are quantities this
     * reads. Refused here for not ordering its values, an equality over a form was reported as a
     * rule written in a form this compiler cannot take apart — a sentence about this compiler, and
     * the form is right here.
     */
    private static Cutting overAForm(String behavior, AffineReading read,
                                     Map<NumericTerm, TermOrders> on,
                                     Quantities quantities) {
        Cutting drawn = made(new BorderQuantity.OverAForm(behavior, read.form(), on),
                new Level.OfTheQuantity(read.cut()), read.claim(), quantities);
        if (drawn == null) {
            // What this watches: `OverAForm.levels()` answers `steppingBy` or `overFiniteDecimals`,
            // and neither of those parts anywhere but everywhere — the one order that names a
            // single place is the one two values meet on, and every term here counts, so that order
            // is not reachable from this shape. An override added to either of those two is what
            // would bring it here, and it should stop rather than be reported as a rule about
            // values nothing draws a line on, which is the opposite of what would have happened.
            throw new IllegalStateException(
                    "a form over orders that count produced a line its order has no place for: "
                            + read.form() + " at " + read.cut());
        }
        return drawn;
    }

    /**
     * What this cuts, as a name a map can hold ({@link BorderQuantity#identity}).
     *
     * <p>Asked of the quantity rather than of which variant of quantity it is. A rule written
     * {@code 2 * n > 40} arrives as a form over twice a position and cuts the position, and a
     * reading that told those apart by the shape it was holding reported the model as drawing one
     * line through {@code n} where it draws two.
     */
    String quantity() {
        String named = of.identity();
        if (named == null) {
            throw new IllegalStateException(
                    "a quantity with no smallest form was taken as one a line is drawn on: " + of);
        }
        return named;
    }

    /** How much of the quantity this rule wrote, which is what a level of one reads as on the
     *  other. */
    ExactRatio per() {
        return of.per();
    }

    /**
     * Where it parts that quantity's values, in the quantity's own units.
     *
     * <p>Found on the order the rule was written on, which is the order that knows which levels the
     * written form attains — {@code 2 * n <= 9} cuts the even numbers and nine is not one of them,
     * so the two sides part between eight and ten. Read back afterwards, which is exact: a level the
     * written form attains is a multiple of how much of the quantity it wrote.
     *
     * <p>Unheld where a value beside the line was not worked out — the exact arithmetic ran out of
     * room for it, or it has no representation. The line is still the rule's, so this is asked of a
     * line that {@link #lineIsPlaced} has already answered for, and the caller says what a side it
     * could not work out means to its own question.
     */
    ExactAnswer<Seam> seam() {
        return Seam.where(of, at, claim);
    }

    /**
     * Every place it parts that quantity's values, in the quantity's own units.
     *
     * <p>A rule that names a value parts the values on both sides of it, and {@link #seam} answers
     * one of them. Asked where the question is whether the line's sides were worked out at all.
     */
    ExactAnswer<List<Seam>> seams() {
        return Seam.eachOf(claim, this::seamTowards);
    }

    /** Where the values part on {@code side} of this line, in the quantity's own units. */
    ExactAnswer<Seam> seamTowards(Towards side) {
        return Seam.where(of, at, side);
    }

    /**
     * The position this cuts, where what it cuts is one position's own values. Null for every other
     * quantity, which is what tells a caller whether an axis is divided by this rule.
     *
     * <p><b>Asked of the canonical quantity and not of the shape the comparison arrived as.</b>
     * {@code 2 * n > 40} reaches this as a form over twice a position and divides that position at
     * twenty; read off the shape, it divided nothing, and a report counted two equivalence
     * partitions where the model states three.
     *
     * <p>Whether the line falls on a value of the position is a different question and not this
     * one. {@code 3 * d <= 1} cuts at a third, which no decimal this language writes, and the
     * behavior still answers one way below it and another way above — so the position has two
     * classes and no number to name the line by. Asked here, that answer made an equivalence
     * partition a thing this compiler can write a boundary for rather than a thing the model
     * distinguishes (issue #880).
     */
    NumericTerm.FromOnePosition dividedPosition() {
        // A position is divided by a form that is a multiple of it, and a quantity that is no form
        // divides no position.
        if (!(of instanceof LinearQuantity form)) {
            return null;
        }
        Map<NumericTerm, ExactRatio> direction = QuantityKey.of(form.direction()).direction();
        // And only where one position answers that number. A quantity read from somewhere else
        // divides no position however few terms it is over, so there is nothing here for a class
        // to be a class of.
        return direction.size() == 1
                ? direction.keySet().iterator().next().atOnePosition() : null;
    }

    /**
     * The one value of the position this rule names, or null where the position has none there.
     *
     * <p>Apart from {@link #dividedValue}, and the two are different questions that one answer had
     * been serving. A rule that orders the values around its line owes a row at the value beside the
     * line — {@code 2 * n <= 9} cuts between four and five and the row is written at four. A rule
     * that names a value names the line itself, and {@code 2 * n == 9} names no whole number at all
     * because nine halved is not one. Answered as the value beside the line, such a rule would put
     * four in a class of its own and four does not satisfy it.
     *
     * <p>Which is a fact about the position and not about the rule: that the canonical quantity is
     * one coordinate says the rule cuts that position, and whether the position has a value where
     * the line falls is asked of the order it sits on.
     */
    ExactAnswer<Optional<Place>> singledValue(Seam parts) {
        // On the order the position it divides is written on. A quantity used to answer with one
        // order for everything under it; a form may now be over positions written back differently,
        // and the value named here is a value of one of them.
        NumericTerm divides = dividedPosition();
        return parts.at().asAValueOf(divides == null ? null : of.writtenBackOn());
    }

    /**
     * The value of that position the classes either side of this line meet at.
     *
     * <p>Read off the seam rather than off the threshold, so a rule that wrote a multiple of the
     * position names a value the position holds: {@code 2 * n <= 9} parts the whole numbers between
     * four and five, and nine halved is not a whole number at all. Which of the two the classes meet
     * at is which side the threshold's own value belongs to, and that is the rule's to say.
     */
    Optional<Place> dividedValue(Seam parts) {
        ComparisonClaim.Cut order = ordering();
        if (order == null) {
            throw new IllegalStateException("which value a rule divides at, asked of one that names"
                    + " a value and divides at neither side of it: " + at);
        }
        Level side = order.valueBelongs() == Towards.BELOW ? parts.below() : parts.above();
        return side instanceof Level.OnACarrier on
                ? Optional.<Place>of(on.at()) : Optional.<Place>empty();
    }

    /**
     * Whether the quantity takes the level this rule names.
     *
     * <p>Asked of the quantity, which is what knows. {@code 2 * a == 8} names four and takes it;
     * {@code 2 * a == 9} takes the even numbers and nine is not one, so it names no value the
     * quantity holds; {@code a + b == 10} takes ten and {@code 2 * a + 2 * b == 9} does not. One
     * question, and the same answer whether the quantity is one position's own values or a form
     * over several.
     *
     * <p>Read off whether a value of a <em>position</em> could be written instead, this was the
     * wrong question wearing the right answer: a form over several positions has no value of a
     * position at all, so every rule singling one out on such a quantity came back naming nothing —
     * which is true of {@code 2 * a + 2 * b == 9} and false of {@code a + b == 10}.
     */
    ExactAnswer<Boolean> takesTheValueItNames() {
        return of.levels().attainable(at);
    }

    /**
     * The positions the canonical quantity is over, as a reader is sent to them.
     *
     * <p>What a rule that was read is filed at. The quantity is what the rule is about, so a
     * position the arithmetic cancelled is not one it says anything about: {@code a + b - b + c <=
     * 10} is {@code a + c <= 10}, and a note filed at {@code b} would say the rule relates a
     * position it does not mention.
     */
    List<FilingCoordinate> over() {
        // Where a reading that reached the numbers files them, which is one answer for every such
        // reading ({@link AffineReading#filedAt}): the terms themselves, in the order a document
        // names them. Written out here, a reader that reached the numbers by another way would
        // write it out again, and the two would file one rule at two coordinates.
        return of.filedAt();
    }

    /** Whether the rule singles a value out rather than ordering the values around it. */
    boolean singles() {
        return claim instanceof ComparisonClaim.Singled;
    }

    /**
     * The order this rule placed on the values either side of its line, or null where it placed
     * none.
     *
     * <p>Which side the value it wrote belongs to is an order's answer and only an order's. A rule
     * that names a value parts that value from every other one and has no side of its own, so a
     * caller wanting one is holding a line whose shape it has to have established.
     */
    ComparisonClaim.Cut ordering() {
        return claim instanceof ComparisonClaim.Cut cut ? cut : null;
    }

    /** The line this draws, as a border reads it. */
    BoundaryTarget target() {
        return BoundaryTarget.at(of, at);
    }
}
