package souther.compiler.partition;

import souther.compiler.check.RuleRef;
import souther.compiler.inputs.BlockReason;
import souther.compiler.inputs.FilingCoordinate;
import souther.compiler.inputs.RuleWithoutALine;
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
    private final List<Axis> axes;
    /** The rules the reading of the input read to the end and found no line in, with why. */
    private final List<RuleWithoutALine> noLine;
    /** Which position each condition is about and what it admits there, asked once of each. */
    private final Map<souther.compiler.reading.Condition, Placed> placed = new HashMap<>();

    private WhatABodyTellsApart(List<Axis> axes, List<RuleWithoutALine> noLine) {
        this.axes = axes;
        this.noLine = noLine;
        this.unread = new boolean[axes.size()];
        for (int at = 0; at < axes.size(); at++) {
            splits.add(new ArrayList<>());
            comparisonsRead.add(new LinkedHashSet<>());
        }
    }

    /**
     * What the body read as {@code read} tells apart at each of {@code axes}, where {@code noLine}
     * is what the reading of the input found about the rules it drew no line for.
     */
    static Map<AxisId, BodyDistinction> of(CoverageRead.Read read, List<Axis> axes,
                                           List<RuleWithoutALine> noLine) {
        WhatABodyTellsApart reading = new WhatABodyTellsApart(axes, noLine);
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
     * <p>Three answers, and the two that place nothing are not one. A condition about something
     * this run measures no position of says nothing about any of them; a condition whose subject
     * the reading could not name may be about any of them, and what it tells apart is not known.
     * Read as one, a decision nothing could place would be a decision about nothing.
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
    }

    private Placed placedOf(souther.compiler.reading.Condition condition) {
        return placed.computeIfAbsent(condition, each -> {
            // A fork the reading could not name a subject for: a value no position is, a name bound
            // over several cases, an attempted construction. Which way it goes may turn on any
            // position's value — whether a construction holds its rules can refuse a case of what
            // it is built from — and the condition says nothing of which.
            if (each instanceof souther.compiler.reading.Condition.Arm) {
                return new Placed.SubjectUnknown();
            }
            int at = InteractionCells.positionOf(each, axes);
            if (at < 0) {
                return new Placed.AboutNoPosition();
            }
            InteractionCells.Cell cell = InteractionCells.admittedBy(each, axes);
            if (cell != null) {
                List<Boolean> admitted = new ArrayList<>();
                for (boolean one : cell.allowed()[at]) {
                    admitted.add(one);
                }
                return new Placed.About(at, List.copyOf(admitted));
            }
            // A comparison with no line here, which the reading of the input read to the end and
            // found divides nothing that arrives at it: every value a run brings there goes the
            // same way. Within the way it is on it admits whatever arrives, which rules out
            // nothing the way does not — and read as something unread, every comparison made under
            // another would leave its position one nothing could be said about.
            if (each instanceof souther.compiler.reading.Condition.Side side
                    && dividesNothingThatArrives(side, axes.get(at))) {
                return new Placed.About(at,
                        Collections.nCopies(axes.get(at).classes().size(), true));
            }
            return new Placed.About(at, null);
        });
    }

    /** Whether the comparison of {@code side} is one the reading of the input found divides
     *  nothing that arrives at it at {@code axis}. */
    private boolean dividesNothingThatArrives(souther.compiler.reading.Condition.Side side,
                                              Axis axis) {
        ModelOccurrence states = ModelOccurrence.statedAt(side.comparison()).orElse(null);
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
        for (Decision decision : way.decisions()) {
            souther.compiler.reading.Condition each = decision.constrains();
            Placed.About one;
            switch (placedOf(each)) {
                case Placed.About it -> one = it;
                case Placed.AboutNoPosition _ -> {
                    continue;
                }
                case Placed.SubjectUnknown _ -> {
                    subjectUnknownHere = true;
                    continue;
                }
            }
            if (one.admitted() == null) {
                unreadHere[one.at()] = true;
                continue;
            }
            // A position with no classes has nothing for the condition to tell apart, and nothing
            // it admits says whether a value takes the way: that is asked of a position a value at
            // it is in some class of.
            if (one.admitted().isEmpty()) {
                continue;
            }
            boolean any = false;
            if (here[one.at()] == null) {
                here[one.at()] = new boolean[one.admitted().size()];
                Arrays.fill(here[one.at()], true);
            }
            for (int c = 0; c < here[one.at()].length; c++) {
                here[one.at()][c] &= one.admitted().get(c);
                any |= here[one.at()][c];
            }
            if (!any) {
                // No class of the position takes this way, so no value does and nothing on it is
                // anything a run decides.
                return;
            }
            if (each instanceof souther.compiler.reading.Condition.Side side) {
                ModelOccurrence.statedAt(side.comparison()).ifPresent(statedHere.get(one.at())::add);
            }
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
