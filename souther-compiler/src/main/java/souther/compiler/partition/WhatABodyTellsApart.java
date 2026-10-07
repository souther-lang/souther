package souther.compiler.partition;

import souther.compiler.check.RuleRef;
import souther.compiler.inputs.BlockReason;
import souther.compiler.inputs.FilingCoordinate;
import souther.compiler.inputs.Requirements;
import souther.compiler.inputs.RuleWithoutALine;
import souther.compiler.inputs.TermPath;
import souther.compiler.reading.CoverageRead;
import souther.compiler.reading.Decision;
import souther.compiler.reading.WayIn;
import souther.compiler.types.ModelOccurrence;
import souther.compiler.types.SourceConstructOrigin;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * The reading {@link BodyDistinction} is made by: the ways a body's runs take, each put to the
 * classes of every position it is about.
 *
 * <p><b>A way and not a decision.</b> A decision tells apart only what arrives where it is made. Under
 * {@code guard n > 0} a second {@code guard n > -10} is made of the values the first let through, and
 * comes out the same way for all of them, so it tells nothing apart; read on its own it would split
 * {@code n <= -10} from the values just above it, which no run does. So what a way says about a
 * position is what all of its decisions about that position admit together — the same conjunction
 * a cell is ({@link InteractionCells}) — and a way that admits nothing at some position is one no
 * value takes.
 *
 * <p>Each condition is put to the classes once, however many ways it is on: which position it is
 * about is a walk over the positions, and the ways repeat what holds above a fork for every way out
 * of it.
 */
final class WhatABodyTellsApart {

    /** The ways read so far at one position: what each admitted there, and which comparisons
     *  admitted it. */
    private final List<List<boolean[]>> splits = new ArrayList<>();
    private final List<Set<ModelOccurrence>> comparisonsRead = new ArrayList<>();
    /** Whether some way said something about the position this reading does not put to its
     *  classes. */
    private final boolean[] unread;
    /** Whether some way a run takes holds a decision the reading could name no subject for, which
     *  leaves what is told apart unknown at every position. */
    private boolean subjectUnknown;
    /** The positions measured, with the reading they were measured in — which says where a
     *  condition stands among them ({@link ConditionPlacement}). */
    private final MeasuredInput.MeasuredAxes measured;
    private final List<Axis> axes;
    /** The rules the reading of the input read to the end and found no line in, with why. */
    private final List<RuleWithoutALine> noLine;
    /** Which position each condition is about and what it admits there, asked once of each. */
    private final Map<souther.compiler.reading.Condition, Placed> placed = new HashMap<>();

    private WhatABodyTellsApart(MeasuredInput.MeasuredAxes measured,
                                List<RuleWithoutALine> noLine) {
        this.measured = measured;
        this.axes = measured.axes();
        this.noLine = noLine;
        this.unread = new boolean[axes.size()];
        for (int at = 0; at < axes.size(); at++) {
            splits.add(new ArrayList<>());
            comparisonsRead.add(new LinkedHashSet<>());
        }
    }

    /**
     * What the body read as {@code read} tells apart at each position {@code measured}, where
     * {@code noLine} is what the reading of the input found about the rules it drew no line for.
     */
    static Map<AxisId, BodyDistinction> of(CoverageRead.Read read,
                                           MeasuredInput.MeasuredAxes measured,
                                           List<RuleWithoutALine> noLine) {
        WhatABodyTellsApart reading = new WhatABodyTellsApart(measured, noLine);
        List<Axis> axes = measured.axes();
        for (WayIn way : read.taken()) {
            reading.take(way);
        }
        Map<AxisId, BodyDistinction> out = new LinkedHashMap<>();
        for (int at = 0; at < axes.size(); at++) {
            out.put(axes.get(at).id(), reading.at(at));
        }
        return Map.copyOf(out);
    }

    /**
     * What one condition says about the positions measured here.
     *
     * <p>The two that place nothing are not one. A condition about something this run measures no
     * position of says nothing about any of them; a condition whose subject the reading could not
     * name may be about any of them, and what it tells apart is not known. Read as one, a decision
     * nothing could place would be a decision about nothing.
     */
    private sealed interface Placed {

        /**
         * About the {@code at}th position.
         *
         * @param admitted the classes it admits there, or null where it admits nothing this
         *                 reading can put to the classes
         */
        record About(int at, List<Boolean> admitted) implements Placed {}

        /** About nothing this run measures a position of. */
        record AboutNoPosition() implements Placed {}

        /** About something the reading could not name, which may be any of the positions. */
        record SubjectUnknown() implements Placed {}

        /**
         * About a name the cases of a sum share, and so about the position it stands at under
         * whichever case a row is.
         *
         * <p>One answer per case and not one for all of them: a row is one case, and what the
         * condition admits of it is what it admits at that case's position. A row under another
         * case is not at this position at all, so a way admitting nothing here says only that its
         * rows are not this case.
         *
         * @param underEach what the condition admits at the position under each case measured
         *                  here, with what a row is taken to be to stand there
         */
        record UnderTheCases(List<UnderACase> underEach) implements Placed {}

        /** What the condition admits at the position under one case, and what a row is taken to
         *  be to stand there. */
        record UnderACase(About about, Requirements taken) {}
    }

    private Placed placedOf(souther.compiler.reading.Condition condition) {
        return placed.computeIfAbsent(condition, this::placing);
    }

    /** Where {@code each} stands, which is {@link ConditionPlacement}'s answer, and what it admits
     *  there. */
    private Placed placing(souther.compiler.reading.Condition each) {
        return switch (ConditionPlacement.of(each, measured)) {
            // A fork the reading could not name a subject for: a value no position is, a name bound
            // over several cases, an attempted construction. Which way it goes may turn on any
            // position's value — whether a construction holds its rules can refuse a case of what
            // it is built from — and the condition says nothing of which.
            case ConditionPlacement.Unnamed _ -> new Placed.SubjectUnknown();
            case ConditionPlacement.AtNoPosition _ -> new Placed.AboutNoPosition();
            case ConditionPlacement.AtAPosition(int at) ->
                    about(each, at, InteractionCells.standingOf(each));
            case ConditionPlacement.UnderTheCases(var underEach) -> {
                List<Placed.UnderACase> out = new ArrayList<>();
                for (ConditionPlacement.UnderACase one : underEach) {
                    out.add(new Placed.UnderACase(about(each, one.axis(), one.at()),
                            one.taken()));
                }
                yield new Placed.UnderTheCases(List.copyOf(out));
            }
        };
    }

    /**
     * What {@code each} admits at the {@code at}th position.
     *
     * @param standing where a case of a value is asked ({@link InteractionCells#admittedAt})
     */
    private Placed.About about(souther.compiler.reading.Condition each, int at,
                               TermPath standing) {
        InteractionCells.Cell cell = InteractionCells.admittedAt(each, axes, at, standing);
        if (cell != null) {
            List<Boolean> admitted = new ArrayList<>();
            for (boolean one : cell.allowed()[at]) {
                admitted.add(one);
            }
            return new Placed.About(at, List.copyOf(admitted));
        }
        // A comparison with no line here, which the reading of the input read to the end and found
        // divides nothing that arrives at it: every value a run brings there goes the same way.
        // Within the way it is on it admits whatever arrives, which rules out nothing the way does
        // not — and read as something unread, every comparison made under another would leave its
        // position one nothing could be said about.
        if (each instanceof souther.compiler.reading.Condition.Side side
                && dividesNothingThatArrives(side, axes.get(at))) {
            return new Placed.About(at,
                    Collections.nCopies(axes.get(at).classes().size(), true));
        }
        return new Placed.About(at, null);
    }

    /** Whether the comparison of {@code side} is one the reading of the input found divides
     *  nothing that arrives at it at {@code axis}. */
    private boolean dividesNothingThatArrives(souther.compiler.reading.Condition.Side side,
                                              Axis axis) {
        ModelOccurrence states = ModelOccurrence.statedAt(side.statedAt()).orElse(null);
        if (states == null) {
            return false;
        }
        for (RuleWithoutALine each : noLine) {
            if (each.rule() instanceof RuleRef.Comparison rule
                    && rule.origin().equals(states.origin())
                    && filedAt(each.at(), axis)
                    && each.why() instanceof BlockReason.ReadToEndWithoutLine read
                    && dividesNothing(read)) {
                return true;
            }
        }
        return false;
    }

    /** Whether a finding filed at {@code at} is about the number {@code axis} measures. */
    private static boolean filedAt(FilingCoordinate at, Axis axis) {
        return switch (at) {
            case FilingCoordinate.AtPosition it -> it.path().equals(axis.path());
            case FilingCoordinate.OfTerm it -> it.term().equals(axis.term());
        };
    }

    /**
     * Whether a rule read to the end with no line sends every value that arrives the same way.
     *
     * <p>Every kind decided here, so that one added later is a decision and not a default. A rule
     * relating two positions, or drawn on a number taken over a run, tells apart something this
     * position's classes are not, and what it does to them is not known.
     */
    private static boolean dividesNothing(BlockReason.ReadToEndWithoutLine why) {
        return switch (why) {
            case BlockReason.ComparisonCuttingNothing _,
                 BlockReason.ComparisonCuttingOutsideDomain _,
                 BlockReason.ComparisonNothingArrivesAtItsLine _,
                 BlockReason.PredicateTellingNothingApart _ -> true;
            case BlockReason.ComparisonBetweenPositions _,
                 BlockReason.ComparisonOverARun _,
                 BlockReason.RuleRestrictingToAdmittedValues _,
                 BlockReason.ClassesNotComposed _ -> false;
        };
    }

    /** One way: what all of its decisions admit together at each position, if a value can take it. */
    private void take(WayIn way) {
        boolean[][] here = new boolean[axes.size()][];
        boolean[] unreadHere = new boolean[axes.size()];
        boolean subjectUnknownHere = false;
        List<Set<ModelOccurrence>> statedHere = new ArrayList<>();
        for (int at = 0; at < axes.size(); at++) {
            statedHere.add(new LinkedHashSet<>());
        }
        // Whether a condition about the position itself is on the way, so that a row taking the way
        // stands there. A condition about a name the cases share says nothing of that: a row under
        // another case takes the way without being at this position.
        boolean[] standsHere = new boolean[axes.size()];
        // The conditions about a name the cases share, put to the classes once the positions the
        // way stands at are known: which case a row taking the way can be is what they say.
        List<Decision> underTheCases = new ArrayList<>();
        for (Decision decision : way.decisions()) {
            souther.compiler.reading.Condition each = decision.constrains();
            switch (placedOf(each)) {
                case Placed.About it -> {
                    standsHere[it.at()] = true;
                    admit(it, each, here, unreadHere, statedHere);
                }
                case Placed.UnderTheCases _ -> underTheCases.add(decision);
                case Placed.AboutNoPosition _ -> { }
                case Placed.SubjectUnknown _ -> subjectUnknownHere = true;
            }
        }
        // Each under the cases a row taking the way can be. The position under a case stands only
        // where the row is that case, so a case the way's own positions rule out is not one its
        // rows are: a fork on a shared name reached once the value turned out to be an `A` is about
        // `A`'s position and says nothing of `B`'s.
        for (Decision decision : underTheCases) {
            souther.compiler.reading.Condition each = decision.constrains();
            for (Placed.UnderACase one : ((Placed.UnderTheCases) placedOf(each)).underEach()) {
                if (canBe(one.taken(), here, standsHere)) {
                    admit(one.about(), each, here, unreadHere, statedHere);
                }
            }
        }
        for (int at = 0; at < axes.size(); at++) {
            if (here[at] == null || anyOf(here[at])) {
                continue;
            }
            // No class of the position takes this way. Where the way puts a row at the position,
            // no value takes it and nothing on it is anything a run decides; where only a name the
            // cases share was asked about, the rows taking it are under another case, and the way
            // says nothing about this position.
            if (standsHere[at]) {
                return;
            }
            here[at] = null;
        }
        // Only for a way some value takes. A decision nothing could place is still one no run makes
        // where the rest of its way admits no class.
        subjectUnknown |= subjectUnknownHere;
        for (int at = 0; at < axes.size(); at++) {
            if (here[at] != null) {
                splits.get(at).add(here[at]);
                comparisonsRead.get(at).addAll(statedHere.get(at));
            }
            unread[at] |= unreadHere[at];
        }
    }

    /** What {@code one}, said by {@code each}, admits, met into what the way admits so far. */
    private static void admit(Placed.About one, souther.compiler.reading.Condition each,
                              boolean[][] here, boolean[] unreadHere,
                              List<Set<ModelOccurrence>> statedHere) {
        if (one.admitted() == null) {
            unreadHere[one.at()] = true;
            return;
        }
        // A position with no classes has nothing for the condition to tell apart, and nothing it
        // admits says whether a value takes the way: that is asked of a position a value at it is
        // in some class of.
        if (one.admitted().isEmpty()) {
            return;
        }
        if (here[one.at()] == null) {
            here[one.at()] = new boolean[one.admitted().size()];
            Arrays.fill(here[one.at()], true);
        }
        for (int c = 0; c < here[one.at()].length; c++) {
            here[one.at()][c] &= one.admitted().get(c);
        }
        if (each instanceof souther.compiler.reading.Condition.Side side) {
            ModelOccurrence.statedAt(side.statedAt()).ifPresent(statedHere.get(one.at())::add);
        }
    }

    /**
     * Whether a row taken to be {@code taken} can take a way that stands at the positions
     * {@code standsHere} marks, in the classes {@code here} leaves them.
     *
     * <p>Asked of each position on its own, as what the way leaves there is: a position stands only
     * where what its path requires holds, and a class of it only where what the class selects holds
     * too — which {@link Requirements#merge} answers, as it does for every reader putting two such
     * requirements together.
     */
    private boolean canBe(Requirements taken, boolean[][] here, boolean[] standsHere) {
        for (int at = 0; at < axes.size(); at++) {
            if (!standsHere[at]) {
                continue;
            }
            Axis axis = axes.get(at);
            if (here[at] == null) {
                if (!taken.compatibleWith(axis.requirements())) {
                    return false;
                }
                continue;
            }
            boolean some = false;
            for (int c = 0; c < here[at].length && !some; c++) {
                some = here[at][c]
                        && taken.compatibleWith(axis.requiring(axis.classes().get(c)));
            }
            if (!some) {
                return false;
            }
        }
        return true;
    }

    private static boolean anyOf(boolean[] admitted) {
        for (boolean each : admitted) {
            if (each) {
                return true;
            }
        }
        return false;
    }

    /** What the ways read tell apart at the {@code at}th position. */
    private BodyDistinction at(int at) {
        Axis axis = axes.get(at);
        // What the body wrote that divided the position, each of which has to be a rule one of the
        // comparisons read above is a reading of. A rule of the type is the model's distinction and
        // not this behavior's, which is the whole question here, so it is not asked for.
        //
        // A line is filed under the construct its rule is stated at, which is what a decision is
        // filed under too, so the two meet there. A parting — a comparison read for where it parts
        // the values rather than where it cuts them — carries the rule and not the construct, and a
        // comparison's rule is the construct the author wrote, whichever reading of it this was.
        Set<SourceConstructOrigin> written = new LinkedHashSet<>();
        for (ModelOccurrence each : comparisonsRead.get(at)) {
            written.add(each.origin());
        }
        boolean ruleNoDecisionRead = false;
        for (RuleEvidenceOrigin origin : linesAndDivisions(axis)) {
            if (writtenInTheBody(origin.rule())
                    && !(origin instanceof LineOrigin.ComparisonOrigin comparison
                            && comparisonsRead.get(at).contains(comparison.read().states()))) {
                ruleNoDecisionRead = true;
            }
        }
        for (Parting parting : axis.parted()) {
            for (AuthoredLine line : parting.alternatives()) {
                RuleRef rule = line.which().rule();
                ruleNoDecisionRead |= writtenInTheBody(rule)
                        && !(rule instanceof RuleRef.Comparison comparison
                                && written.contains(comparison.origin()));
            }
        }
        // Unread over anything read. What was read at the position is part of what the body tells
        // apart there, and a part is never said as the whole.
        boolean unplacedHere = unread[at] || ruleNoDecisionRead;
        List<List<String>> groups = groupsOf(axis.classes(), splits.get(at));
        // Unless what was read already tells every class apart, which nothing further can refine:
        // whatever went unread, the partition is the finest there is.
        boolean everyClassApart = !splits.get(at).isEmpty()
                && groups.size() == axis.classes().size();
        if ((subjectUnknown || unplacedHere) && !everyClassApart) {
            return new BodyDistinction.Unread(groups, unplacedHere);
        }
        if (splits.get(at).isEmpty()) {
            return new BodyDistinction.Untouched();
        }
        return new BodyDistinction.Drawn(groups);
    }

    /** Every reading of a rule that drew a line on the position or composed its classes. */
    private static List<RuleEvidenceOrigin> linesAndDivisions(Axis axis) {
        List<RuleEvidenceOrigin> out = new ArrayList<>(axis.divides());
        for (Cut cut : axis.cuts()) {
            out.addAll(cut.origins());
        }
        return out;
    }

    /**
     * Whether {@code rule} was written in the body, as against named by the author.
     *
     * <p>A rule the author named — an invariant, an {@code ensures} — says what the type or the
     * answer holds and is no statement about what this behavior tells apart; one written in a body
     * is.
     */
    private static boolean writtenInTheBody(RuleRef rule) {
        return rule instanceof RuleRef.Written;
    }

    /**
     * The classes in groups, two in one group where every way admits both or neither.
     *
     * <p>The coarsest partition finer than what every way admits, which is what telling apart
     * composes to: two classes some way takes one of and not the other are in different groups,
     * however many ways say nothing about them.
     */
    private static List<List<String>> groupsOf(List<PartitionClass> classes,
                                              List<boolean[]> splits) {
        Map<List<Boolean>, List<String>> bySignature = new LinkedHashMap<>();
        for (int c = 0; c < classes.size(); c++) {
            List<Boolean> signature = new ArrayList<>(splits.size());
            for (boolean[] split : splits) {
                signature.add(split[c]);
            }
            bySignature.computeIfAbsent(signature, _ -> new ArrayList<>()).add(classes.get(c).id());
        }
        return List.copyOf(bySignature.values());
    }
}
