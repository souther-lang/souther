package souther.compiler.partition;

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
import souther.compiler.meaning.DecidingCase;
import souther.compiler.meaning.DecisionAtom;
import souther.compiler.meaning.DecisionSubject;
import souther.compiler.meaning.Derivation;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.Quantity;
import souther.compiler.meaning.Relation;
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
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.SequencedMap;
import java.util.Set;
import java.util.function.Supplier;

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
 */
record Cutting(BorderQuantity of, Level at, ComparisonClaim claim,
               NumericDomain.Bounds within) {

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
             * One line of the statement.
             *
             * @param id    which of the author's lines it is a place of, and which place
             * @param line  the line it draws, or the refusal to place it; never a reading that
             *              stopped, since the statement was read to the end
             * @param cases where the statement turns on it, as cases any one of which is enough;
             *              empty where it turns on it nowhere
             */
            record Part(PlaceOfALine id, Read line, List<DecidingCase> cases) {

                public Part {
                    Objects.requireNonNull(id, "a line of a statement is one of its lines");
                    cases = DecidingCase.eachByItsOwnCondition(cases);
                    if (!(line instanceof Cuts || line instanceof NoOrderToCountOn
                            || line instanceof NumberNoRatioHolds)) {
                        throw new IllegalArgumentException(
                                "a line of a statement read to the end is drawn or refused: " + line);
                    }
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
        // A count, or what a division leaves, rises as that number does: the line is drawn on the
        // number itself, and the relation weighs it by its coefficient.
        if (of instanceof BorderQuantity.HowMany || of instanceof BorderQuantity.RemainderOfAForm) {
            for (Map.Entry<Quantity, ExactRatio> each : affine.form().coefs().entrySet()) {
                if ((each.getKey() instanceof Quantity.HowManyMeet
                        && of instanceof BorderQuantity.HowMany)
                        || (each.getKey() instanceof Quantity.RemainderOfADividend
                                && of instanceof BorderQuantity.RemainderOfAForm)) {
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
        Read drawn = onEachApplication(behavior, comparison, read, each, answering, conditions,
                writtenIn);
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
                                          InputReading read,
                                          List<ClosureApplications.Application> each,
                                          Arrivals answering, WhatConditionsState conditions,
                                          Optional<ExpansionLineage> writtenIn) {
        SequencedMap<FilingCoordinate, BlockReason.RuleReadingStopped> stopped =
                new LinkedHashMap<>();
        List<FilingCoordinate> settled = new ArrayList<>();
        List<FilingCoordinate> against = new ArrayList<>();
        List<UndividedByARelation> relations = new ArrayList<>();
        Map<ALineRead, List<WhereAnApplicationIsMade.OnOne>> lines = new LinkedHashMap<>();
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
                case Read.AgainstAnotherValue alone -> {
                    alone.over().forEach(at -> {
                        if (!against.contains(at)) {
                            against.add(at);
                        }
                    });
                    relations.addAll(alone.relations());
                }
                case Read.Several several -> several.parts().forEach(part -> lines
                        .computeIfAbsent(new ALineRead(part.id(), part.line()),
                                _ -> new ArrayList<>())
                        .add(new WhereAnApplicationIsMade.OnOne(part.cases(), one.reached())));
                case Read line -> lines.computeIfAbsent(new ALineRead(new PlaceOfALine(
                                        line instanceof Read.Cuts cuts
                                                ? PartOfAComparison.of(cuts.authored().line())
                                                : THE_COMPARISON,
                                        spelled(onTheInput.stated().proposition())),
                                        line), _ -> new ArrayList<>())
                        .add(WhereAnApplicationIsMade.OnOne.wherever(one.reached()));
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
            return new Read.CutsNothing(settled);
        }
        List<Read.Several.Part> parts = new ArrayList<>();
        lines.forEach((line, readings) -> parts.add(new Read.Several.Part(line.id(), line.read(),
                WhereAnApplicationIsMade.decidesOn(readings))));
        if (parts.size() == 1 && WhereAnApplicationIsMade.everywhere(parts.getFirst().cases())) {
            return parts.getFirst().line();
        }
        return new Read.Several(parts);
    }

    /** The comparison as its author drew it, where its definition chooses nothing on the way. */
    private static final PartOfAComparison THE_COMPARISON =
            PartOfAComparison.of(WrittenLine.THE_COMPARISON);

    /** A statement that is one line, as the place of a line it is: the relation, held. */
    private static String spelled(Proposition stated) {
        return stated instanceof Proposition.Compared compared ? compared.heldKey() : stated.key();
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
        if (!(only.getKey() instanceof Quantity.HowManyMeet count)
                || !AStatementAtARow.askable(count.ofTheElement())) {
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
        CountedElements counted = CountedElements.of(behavior, count, read.quantities(),
                DemandReading.anElementMeeting(count, read));
        BorderQuantity.HowMany of =
                new BorderQuantity.HowMany(counted, HowManyCanMeet.of(counted, read));
        Cutting drawn = made(of, new Level.OfTheQuantity(level), claim, read.quantities());
        return drawn == null ? null : cutsOrRefused(drawn);
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
        if (affine.form().coefs().size() != 1
                || !(affine.form().coefs().entrySet().iterator().next().getKey()
                        instanceof Quantity.RemainderOfADividend remainder)) {
            return null;
        }
        ExactRatio weight = affine.form().coefs().get(remainder);
        if (!(affine.form().constant().negated().dividedBy(weight)
                instanceof ExactAnswer.Held<ExactRatio>(ExactRatio level))
                || !(remainder.dividend().constant().floor()
                        instanceof ExactAnswer.Held<BigInteger> shift)) {
            return null;
        }
        Map<NumericTerm, TermOrders> on = new LinkedHashMap<>();
        for (NumericTerm term : remainder.dividend().coefs().keySet()) {
            TermOrders orders = read.quantities().ordersOf(term);
            if (orders == null || orders.answered() == null || !orders.answered().counts()) {
                return null;
            }
            on.put(term, orders);
        }
        ComparisonClaim claim = ComparisonClaim.stating(
                holds ? affine.proposition() : affine.proposition().denied());
        BorderQuantity.RemainderOfAForm of = new BorderQuantity.RemainderOfAForm(behavior,
                new BorderQuantity.OverAForm(behavior,
                        new LinearForm<>(ExactRatio.ZERO, remainder.dividend().coefs()), on),
                shift.value(), remainder.divisor());
        Cutting drawn = made(of, new Level.OfTheQuantity(level), claim, read.quantities());
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
        Quantity.HowManyMeet count = null;
        ExactRatio weight = null;
        for (Map.Entry<Quantity, ExactRatio> each : affine.form().coefs().entrySet()) {
            if (each.getKey() instanceof Quantity.HowManyMeet counted) {
                if (count != null) {
                    return null;
                }
                count = counted;
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
        if (count == null || !AStatementAtARow.askable(count.ofTheElement())) {
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
        BorderQuantity.HowMany of = new BorderQuantity.HowMany(CountedElements.of(behavior, count,
                read.quantities(), DemandReading.anElementMeeting(count, read)),
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
                authorsLines(authors, compared, comparison.claim());
        // A place of one of the author's lines is that line's one reading here, whichever line it
        // is; the line it is a place of is carried with it. A place of several is a line of each,
        // deciding where a row takes the arms that line is under.
        if (of.size() == 1) {
            return authored(drawn, of.values().iterator().next(), compared);
        }
        List<Read.Several.Part> parts = new ArrayList<>();
        of.forEach((line, mapping) -> parts.add(new Read.Several.Part(
                new PlaceOfALine(line, compared.heldKey()), authored(drawn, mapping, compared),
                WhereEachLineDecides.takenWhere(
                        List.of(DecidingCase.alone(WhereAnApplicationIsMade.nothingAsked())),
                        authors.takenWhere(mapping.line())))));
        return new Read.Several(parts);
    }

    /**
     * Which of the author's lines {@code relation} is a place of, and how it stands to each, as
     * {@code lines} says: the comparison itself where nothing the derivation made it under was the
     * author's choice, and not shown to be its line where no step was seen making it at all.
     *
     * @param written what the comparison claims, as its author wrote it
     */
    private static Map<PartOfAComparison, AuthoredPointMapping> authorsLines(
            AuthorsLines lines, Proposition.Compared relation, ComparisonClaim written) {
        Map<WrittenLine, AuthoredPointMapping> under = lines.of(relation.heldKey());
        Map<PartOfAComparison, AuthoredPointMapping> out = new LinkedHashMap<>();
        if (under == null || under.isEmpty()) {
            out.put(THE_COMPARISON,
                    new AuthoredPointMapping.Undetermined(WrittenLine.THE_COMPARISON, written));
        } else {
            under.forEach((line, mapping) -> out.put(PartOfAComparison.of(line), mapping));
        }
        return out;
    }

    /** What {@code comparison} states read once, in {@code reads}, as the reading drew it. */
    private static Read readAsAWhole(String behavior, StatedComparison comparison,
                                     InputReading read, InputReads reads, Arrivals answering,
                                     Pullback.OnTheInput onTheInput,
                                     Supplier<Optional<AuthorsLines>> lines) {
        Pullback.Pulled stated = onTheInput.stated();
        // A form put on the input's numbers, where what is stated is one over them.
        LinearForm<NumericTerm> overTheInput =
                stated.proposition() instanceof Proposition.Compared(
                        Relation.Affine affine, boolean _, String _)
                        ? WhatTheDeclarationsLeave.ofTheInput(affine.form()) : null;
        // And a count of the elements meeting something, where what is stated is one over that.
        Read counted = overTheInput == null && stated.proposition() instanceof Proposition.Compared(
                Relation.Affine affine, boolean holds, String _)
                ? onACount(behavior, affine, holds, read) : null;
        // And what a division leaves of a form of them, which is a line on the remainder.
        Read remainder = overTheInput == null && counted == null
                && stated.proposition() instanceof Proposition.Compared(
                        Relation.Affine affine, boolean holds, String _)
                ? onARemainder(behavior, affine, holds, read) : null;
        // And numbers about how its values stand to one another, which no position holds.
        List<FilingCoordinate> related = overTheInput == null && counted == null
                && remainder == null
                ? heldOverValuesRelatedToOneAnother(stated.proposition()) : null;
        return switch (stated.proposition()) {
            case Proposition.Always _ -> new Read.CutsNothing(
                    settledAt(stated, comparison, read, reads, answering));
            case Proposition.Compared(Relation.Affine affine, boolean holds, String _)
                    when overTheInput != null ->
                    realized(behavior, AffineReading.stating(overTheInput,
                            holds ? affine.proposition() : affine.proposition().denied(),
                            comparison.left(), reads, read.rules()), read.quantities());
            case Proposition.Compared _ when counted != null -> counted;
            case Proposition.Compared _ when remainder != null -> remainder;
            case Proposition.Compared _ when related != null ->
                    against(related, stated.proposition());
            case Proposition.Some some
                    when valuesItRelates(some) instanceof List<FilingCoordinate> values ->
                    against(values, some);
            case Proposition.Compared(Relation.Ordered(
                    DecisionAtom.OfTheInput(NumericTerm term), Place at, Rel proposition),
                    boolean holds, String _) when term.atOnePosition() != null ->
                    onAnOrder(behavior, term.atOnePosition(), at,
                            holds ? proposition : proposition.denied(), read.quantities());
            // A number the statement names has no representation, which is a line placed at a
            // number nothing holds: nothing about the order fell short.
            case Proposition.Unread unread when unread.why() instanceof WhyUnread.ANumberNotHeld ->
                    new Read.NumberNoRatioHolds(
                            GuardThresholds.filedAt(comparison, read, reads, answering));
            // Which cases, truths and values the input's positions hold, and no relation of
            // numbers: what an application stating it is ({@link #ofAnApplication}).
            case Proposition.All _, Proposition.Any _, Proposition.Some _, Proposition.InCases _,
                 Proposition.Truth _, Proposition.Present _
                    when statesNoRelation(stated.proposition()) -> new Read.StatesNoRelation();
            case Proposition.All _, Proposition.Any _
                    when !Proposition.leavesSomethingUnread(stated.proposition()) -> {
                Read several = several(behavior, comparison.left(), stated.proposition(), read,
                        reads, lines.get());
                yield several != null ? several
                        : severalNotDrawn(comparison, read, reads, answering);
            }
            // Some element meeting several parts, which is the parts read of that element: a
            // lookup's answer compared as a whole is its entry under the key meeting the
            // comparison, and the line is the comparison's on the entry. Inside an either-or it is
            // the same parts, read there.
            case Proposition.Some some when some.holds()
                    && !Proposition.leavesSomethingUnread(some) -> {
                Read several = several(behavior, comparison.left(), some, read, reads,
                        lines.get());
                yield several != null ? several
                        : severalNotDrawn(comparison, read, reads, answering);
            }
            default -> noLine(comparison, stated.proposition(), onTheInput.arithmetic(), read,
                    reads, answering);
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
     * <p>Except a relation read to the end against a value no position holds, which is no reading
     * that stopped and is said at the input's numbers it relates ({@link #heldAgainstAnotherValue}).
     */
    private static Read noLine(StatedComparison comparison, Proposition stated,
                               Supplier<AffineReading.OfAComparison> arithmetic,
                               InputReading read, InputReads reads, Arrivals answering) {
        List<FilingCoordinate> against = heldAgainstAnotherValue(stated);
        if (against != null) {
            return against(against, stated);
        }
        // A part the arithmetic met a shape it has no term for in is a stop whose reason was
        // decided where it was met. Which positions it is filed at is still asked of the
        // comparison, and the reason is not asked again of where the values came from.
        List<WhyUnread> stops = Proposition.stopsIn(stated);
        BlockReason.RuleReadingStopped decided = decidedByTheArithmetic(stops);
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
        if (!(stated instanceof Proposition.Compared(Relation.Affine affine, boolean _, String _))
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
                default -> {
                    return null;
                }
            }
        }
        return input.isEmpty() || !another ? null : AffineReading.filedAt(input);
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
                                                     String _))) {
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
                case Quantity.HowManyDifferent different ->
                        related.add(FilingCoordinate.at(different.ofTheElement().inputPosition()));
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
     */
    private static BlockReason.RuleReadingStopped decidedByTheArithmetic(List<WhyUnread> stops) {
        Set<NonAffineOperation> operations = EnumSet.noneOf(NonAffineOperation.class);
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
                 Proposition.InCases _, Proposition.Present _, Proposition.SameValue _,
                 Proposition.LastToHold _, Proposition.All _, Proposition.Any _,
                 Proposition.Some _, Proposition.OnAnApplication _, Proposition.SomeReachable _ ->
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
                 WhyUnread.WhatARecursiveHelperAnswers _, WhyUnread.AtNoPosition _,
                 WhyUnread.NoMeasureOfItsSize _ -> true;
            case WhyUnread.MoreReadingsThanAreMade _, WhyUnread.MoreTotalReadingsThanAreMade _,
                 WhyUnread.MorePartsThanAreConcluded _,
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
        if (several(behavior, application, stated, read, reads, Optional.of(authors))
                instanceof Read.Several lines) {
            return lines;
        }
        List<FilingCoordinate> related = valuesItRelates(stated);
        return related == null ? null : against(related, stated);
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
        if (stated instanceof Proposition.Compared(Relation.Affine affine, boolean _, String _)) {
            relations.add(UndividedByARelation.ofAForm(affine.form(), affine.proposition()));
            for (Quantity each : affine.form().coefs().keySet()) {
                switch (each) {
                    case Quantity.HowManyMeet count -> relations.add(oneValue(count.ofTheElement()));
                    case Quantity.HowManyDifferent different -> relations.add(
                            UndividedByARelation.amongTheValuesAt(
                                    different.ofTheElement().inputPosition()));
                    default -> { }
                }
            }
        } else {
            relations.add(oneValue(stated));
        }
        return new Read.AgainstAnotherValue(over, relations);
    }

    /** {@code stated} held as the two values of its one statement that two values are one. */
    private static UndividedByARelation oneValue(Proposition stated) {
        List<Proposition.SameValue> same = new ArrayList<>();
        sameValuesIn(stated, same);
        return same.size() == 1 && same.getFirst() instanceof Proposition.SameValue(
                DecisionSubject.AnInput(TermPath one), DecisionSubject.AnInput(TermPath other),
                boolean _, String _)
                ? UndividedByARelation.ofTwoPositions(one, other)
                : UndividedByARelation.SHOWING_NOTHING;
    }

    /** Every statement of two values being one {@code stated} is made of. */
    private static void sameValuesIn(Proposition stated, List<Proposition.SameValue> out) {
        switch (stated) {
            case Proposition.SameValue same -> out.add(same);
            case Proposition.Some some -> sameValuesIn(some.ofTheElement(), out);
            case Proposition.All all -> all.parts().forEach(each -> sameValuesIn(each, out));
            case Proposition.Any any -> any.parts().forEach(each -> sameValuesIn(each, out));
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
            // Settled, a relation, two values being one, or something nobody read: each is read
            // as what it is ({@link #readOnce}).
            case Proposition.Always _, Proposition.Compared _, Proposition.SameValue _,
                 Proposition.Unread _, Proposition.LastToHold _, Proposition.OnAnApplication _,
                 Proposition.SomeReachable _ -> false;
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
                                       String _) -> {
                for (TermPath each : List.of(one, other)) {
                    if (!out.contains(FilingCoordinate.at(each))) {
                        out.add(FilingCoordinate.at(each));
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
            default -> false;
        };
    }

    /**
     * The lines a statement of several relations draws, each with where it decides — or null where
     * one of the relations is no line on the input, or there is none.
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
     * <p>Every relation of the statement is a line or none of them is drawn. A relation over
     * something no row writes — what a dependency answered — has no line on the input to be; the
     * lines of the others would be drawn as though the statement were only them. A part a row
     * answers of its own values and that is no relation — whether a position is true, whether it
     * holds a value — is no line, and is where the lines decide. And where a line decides is said
     * over the statement's other parts, so with every part one a row answers, a row's own values
     * say whether it is somewhere the line decides — how many elements meet something among them,
     * which a row's elements say.
     *
     * @param written the construct the rule is written as, asked only which position it names
     *                first, which is the way each line is faced
     * @param authors which of the author's lines each relation is a place of, how it stands to
     *                each and where a row takes each one's arms ({@link WrittenLines}); nothing
     *                for a clause, which no body wrote and whose lines are its own relations
     */
    private static Read several(String behavior, Core written,
                                Proposition stated, InputReading read, InputReads reads,
                                Optional<AuthorsLines> authors) {
        if (!onlyRelations(stated) && !drawsLines(stated)) {
            return null;
        }
        List<WhereEachLineDecides.Decides> lines = WhereEachLineDecides.in(stated);
        if (lines.isEmpty()) {
            return null;
        }
        List<Read.Several.Part> parts = new ArrayList<>();
        for (WhereEachLineDecides.Decides each : lines) {
            Read line = lineOf(behavior, each.line(), written, read, reads);
            if (line == null) {
                return null;
            }
            if (authors.isEmpty()) {
                parts.add(new Read.Several.Part(new PlaceOfALine(THE_COMPARISON,
                        each.line().key()), line, each.cases()));
                continue;
            }
            authorsLines(authors.get(), each.line(), WrittenLines.claimOf(each.line()))
                    .forEach((of, mapping) -> parts.add(
                    new Read.Several.Part(new PlaceOfALine(of, each.line().key()),
                            authored(line, mapping, each.line()),
                            WhereEachLineDecides.takenWhere(each.cases(),
                                    authors.get().takenWhere(mapping.line())))));
        }
        return new Read.Several(parts);
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
            case Proposition.Some some -> some.holds() && holdsARelation(some.ofTheElement());
            default -> false;
        };
    }

    /** Whether every part {@code stated} joins is a relation. */
    static boolean onlyRelations(Proposition stated) {
        return switch (stated) {
            case Proposition.All all -> all.parts().stream().allMatch(Cutting::onlyRelations);
            case Proposition.Any any -> any.parts().stream().allMatch(Cutting::onlyRelations);
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
            case Relation.Affine affine -> {
                LinearForm<NumericTerm> over = WhatTheDeclarationsLeave.ofTheInput(affine.form());
                // A relation over no form of the input's numbers may be one over how many elements
                // meet something, which is a line too.
                yield over == null ? firstDrawn(onACount(behavior, affine, true, read),
                        () -> onARemainder(behavior, affine, true, read))
                        : realized(behavior, AffineReading.stating(over, affine.proposition(),
                                written, reads, read.rules()), read.quantities());
            }
            case Relation.Ordered(DecisionAtom.OfTheInput(NumericTerm term), Place at, Rel rel)
                    when term.atOnePosition() != null ->
                    onAnOrder(behavior, term.atOnePosition(), at, rel, read.quantities());
            case Relation.Ordered _ -> null;
        };
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
        return stated.meaning().how() instanceof Derivation.ACutThatCutsNothing cut
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
        return new Cutting(moved, at, claim, quantities.runsBetween(moved.direction()));
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
        Border.Values values = valuesIn(region);
        return values != null
                && Border.reaches(at, this::seam, claim, drawnByAnInvariant, values);
    }

    /**
     * Whether the rows {@code region} holds stand on both sides of this line — at the value a rule
     * names and beside it, for a rule that names one.
     *
     * <p>What a line of a statement of several is asked in each case of where it decides. A case is
     * other relations holding or failing, and a row on one side of the line and a row on the other,
     * both in the case, differ in this relation alone — so the statement comes out differently for
     * them. Asked of one side only, a case could hold of the rows on one side and of none on the
     * other: {@code Int.min(a, 11 - a) > 5} decides on {@code 11 - a > 5} where {@code a > 5}, and
     * crossing from six to five takes {@code a > 5} with it, so the statement never turns there.
     *
     * <p>A side that was not worked out is not a proof that no row stands on it, as it is not in
     * {@link #reachedIn}.
     */
    boolean crossedIn(SearchRegion region) {
        Border.Values values = valuesIn(region);
        if (values == null) {
            return false;
        }
        return switch (claim) {
            case ComparisonClaim.Cut _ -> Border.reachesBothSides(at, seam(), values);
            // The value it names and a row beside it on either side. With the value put above the
            // seam, the seam parts it from what is below; put below, from what is above.
            case ComparisonClaim.Singled _ -> values.holdAt(at)
                    && (Border.standsBeside(at, Seam.where(of, at, Towards.ABOVE), Towards.BELOW,
                            values)
                            || Border.standsBeside(at, Seam.where(of, at, Towards.BELOW),
                                    Towards.ABOVE, values));
        };
    }

    /**
     * What {@code region} leaves this quantity, as the two questions a line asks of it — or null
     * where it leaves the quantity nothing at all.
     */
    private Border.Values valuesIn(SearchRegion region) {
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
        return new Border.Values() {
            @Override
            public boolean extendTo(Level level) {
                return extent.extendTo(level);
            }

            @Override
            public boolean holdAt(Level level) {
                if (held.refuses(level)) {
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
                return against(region, level, past)
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
