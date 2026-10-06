package souther.compiler.partition;

import souther.compiler.check.RuleRef;
import souther.compiler.reading.CoverageRead;
import souther.compiler.reading.Decision;
import souther.compiler.reading.Factor;
import souther.compiler.reading.Interaction;
import souther.compiler.reading.Outcome;
import souther.compiler.reading.PathAccess;
import souther.compiler.reading.WayIn;
import souther.compiler.types.ModelOccurrence;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * How far a behavior's body tells apart the classes of one position of its input.
 *
 * <p>The third of three answers about a position, and none of them stands for another. Which
 * classes the position holds is the model's ({@link Axis#classes()}); which rules those classes were
 * composed out of is where they came from ({@link Axis#divides()}); this is what the behavior does
 * with them. A sum holds its cases because it is a sum, so a {@code match} over them composes no
 * class and leaves {@code divides} empty — and tells every case apart all the same.
 *
 * <p>A partition of the classes and not a count of them. A body that takes {@code A}, {@code B},
 * {@code C} and {@code D} and asks only whether a value is one of the first two tells the four apart
 * as two groups. So what is held is the groups: two classes are in one group where nothing the body
 * decides on goes one way for one of them and the other way for the other.
 *
 * <p><b>Read off the decisions, through the lookup a cell is made by.</b> A decision names the
 * position it turns on — a {@code match} on a case, a comparison a fork is taken by — and which
 * classes it leaves is what {@link InteractionCells} already reads a condition into. A {@code match}
 * arm, a {@code guard} and a comparison are all a condition, and each splits the classes into the
 * ones it admits and the rest.
 *
 * <p><b>And a rule the body wrote that no decision reads is said, not guessed at.</b> The predicate
 * handed to a {@code List.filter} divides a position into classes and the walk that finds the
 * decisions does not enter it, on purpose. What the body tells apart there is real and is not
 * something this reads into classes, so the position is {@link Unread} rather than one the body
 * tells nothing apart about.
 *
 * <p><b>And not where a value is used.</b> A position copied into the answer, or added to another,
 * is read by the body and told apart by nothing. A sum divides a position by being a sum, and a body
 * that never looks at it has said nothing about it.
 */
public sealed interface BodyDistinction {

    /** Nothing the body decides on or writes is about the position, so every class goes one way. */
    record Untouched() implements BodyDistinction {}

    /**
     * Something the body decides on is about the position, and all of it was read into classes.
     *
     * @param groups the classes, each in the group of those nothing the body decides on tells it
     *               apart from, in the order of the first class of each
     */
    record Drawn(List<Set<String>> groups) implements BodyDistinction {

        public Drawn {
            groups = groups.stream().map(Set::copyOf).toList();
        }
    }

    /**
     * Something the body says about the position is not read into classes: a condition this
     * compiler names the position of and cannot place, or a rule the body wrote that no decision
     * reads.
     */
    record Unread() implements BodyDistinction {}

    /** There is no body to read, so what the behavior tells apart is not known. */
    record NoBody() implements BodyDistinction {}

    /**
     * Whether a combination of this position's classes with another's is worth a row.
     *
     * <p>Where the body says something about it, whether or not that was read into classes, and
     * where there is no body at all. A combination asks that the behavior was tried with both
     * classes at once, which is worth asking where the behavior may tell them apart; a position the
     * body says nothing about answers the same however the other moves. With no body, what is
     * missing is the reading and not the relevance.
     */
    default boolean makesCombinations() {
        return switch (this) {
            case Untouched _ -> false;
            case Drawn _, Unread _, NoBody _ -> true;
        };
    }

    /** What a behavior with no body tells apart at each of {@code axes}, which is unknown. */
    static Map<AxisId, BodyDistinction> withoutABody(List<Axis> axes) {
        Map<AxisId, BodyDistinction> out = new LinkedHashMap<>();
        for (Axis axis : axes) {
            out.put(axis.id(), new NoBody());
        }
        return Map.copyOf(out);
    }

    /**
     * What the body read as {@code read} tells apart at each of {@code axes}.
     *
     * <p>A condition this compiler cannot name a position for is about none of them: what it says
     * is unknown rather than about everything, and reading it as everything would put a position
     * into the pair space on the strength of something unread.
     */
    static Map<AxisId, BodyDistinction> of(CoverageRead.Read read, List<Axis> axes) {
        // What every fork is taken by, and beside it what the values a meeting is over are settled
        // by: a comparison whose truth is handed on as a value is a decision no fork is taken by,
        // and the body tells its position apart all the same.
        //
        // A set, because the three readings name one decision as often as they meet it, and what
        // it tells apart is the same however often it was met.
        Set<souther.compiler.reading.Condition> said = new LinkedHashSet<>(read.decided());
        for (Interaction group : read.interactions()) {
            group.reach().forEach(each -> said.add(each.constrains()));
            for (Factor factor : group.factors()) {
                for (Outcome outcome : factor.outcomes()) {
                    outcome.holds().forEach(each -> said.add(each.constrains()));
                }
            }
        }
        read.arms().forEach((_, access) -> {
            if (access instanceof PathAccess.Ways(var ways, var _)) {
                for (WayIn way : ways) {
                    for (Decision each : way.decisions()) {
                        said.add(each.constrains());
                    }
                }
            }
        });
        // Which position each is about, asked once of each. Asked per position instead, every
        // condition is looked up again for every position the behavior has.
        List<List<souther.compiler.reading.Condition>> about = new ArrayList<>(axes.size());
        for (int at = 0; at < axes.size(); at++) {
            about.add(new ArrayList<>());
        }
        for (souther.compiler.reading.Condition each : said) {
            int at = InteractionCells.positionOf(each, axes);
            if (at >= 0) {
                about.get(at).add(each);
            }
        }
        Map<AxisId, BodyDistinction> out = new LinkedHashMap<>();
        for (int at = 0; at < axes.size(); at++) {
            out.put(axes.get(at).id(), at(at, about.get(at), axes));
        }
        return Map.copyOf(out);
    }

    /** What the conditions {@code said}, each about it, tell apart at the {@code at}th of
     *  {@code axes}. */
    private static BodyDistinction at(int at, List<souther.compiler.reading.Condition> said,
                                      List<Axis> axes) {
        Axis axis = axes.get(at);
        List<boolean[]> splits = new ArrayList<>();
        Set<ModelOccurrence> comparisonsRead = new LinkedHashSet<>();
        boolean unread = false;
        for (souther.compiler.reading.Condition each : said) {
            InteractionCells.Cell admitted = InteractionCells.admittedBy(each, axes);
            if (admitted == null) {
                unread = true;
                continue;
            }
            splits.add(admitted.allowed()[at]);
            if (each instanceof souther.compiler.reading.Condition.Side side) {
                ModelOccurrence.statedAt(side.comparison()).ifPresent(comparisonsRead::add);
            }
        }
        // What the body wrote that divided the position, each of which has to be one of the
        // comparisons read above. A rule of the type is the model's distinction and not this
        // behavior's, which is the whole question here, so it is not asked for.
        boolean ruleNoDecisionRead = false;
        for (Cut cut : axis.cuts()) {
            for (LineOrigin origin : cut.origins()) {
                ruleNoDecisionRead |= unreadBy(origin, comparisonsRead);
            }
        }
        for (RuleEvidenceOrigin origin : axis.divides()) {
            ruleNoDecisionRead |= unreadBy(origin, comparisonsRead);
        }
        for (Parting parting : axis.parted()) {
            for (AuthoredLine line : parting.alternatives()) {
                // A parting is read by no condition, so a rule the body wrote that parted the
                // position is one nothing here placed.
                ruleNoDecisionRead |= writtenInTheBody(line.which().rule());
            }
        }
        if (unread || ruleNoDecisionRead) {
            return new Unread();
        }
        if (splits.isEmpty()) {
            return new Untouched();
        }
        return new Drawn(groupsOf(axis.classes(), splits));
    }

    /**
     * Whether {@code origin} is a rule the body wrote that none of the comparisons read is.
     *
     * <p>Asked of the construct the rule is stated at, which is what a decision and a line drawn off
     * the same comparison both file it under ({@link InteractionCells}).
     */
    private static boolean unreadBy(RuleEvidenceOrigin origin, Set<ModelOccurrence> read) {
        if (!writtenInTheBody(origin.rule())) {
            return false;
        }
        return !(origin instanceof LineOrigin.ComparisonOrigin comparison
                && read.contains(comparison.read().states()));
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
     * The classes in groups, two in one group where every split admits both or neither.
     *
     * <p>The coarsest partition finer than every split, which is what telling apart composes to:
     * two classes the body tells apart anywhere are in different groups, however many conditions
     * say nothing about them.
     */
    private static List<Set<String>> groupsOf(List<PartitionClass> classes,
                                             List<boolean[]> splits) {
        Map<List<Boolean>, Set<String>> bySignature = new LinkedHashMap<>();
        for (int c = 0; c < classes.size(); c++) {
            List<Boolean> signature = new ArrayList<>(splits.size());
            for (boolean[] split : splits) {
                signature.add(split[c]);
            }
            bySignature.computeIfAbsent(signature, _ -> new LinkedHashSet<>())
                    .add(classes.get(c).id());
        }
        return List.copyOf(bySignature.values());
    }
}
