package souther.compiler.partition;

import souther.compiler.check.Carrier;
import souther.compiler.check.PredicateStatement;
import souther.compiler.inputs.BlockReason;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.numeric.OrderedInterval;
import souther.compiler.numeric.Place;
import souther.compiler.numeric.PlacesApart;
import souther.compiler.numeric.Text;
import net.unit8.notation199x.pattern.Meter;
import souther.compiler.observe.Figure;
import souther.compiler.observe.WorkFigure;
import souther.compiler.regex.PatternPlan;
import souther.compiler.values.Allowance;
import souther.compiler.values.Sameness;
import souther.compiler.values.Value;
import souther.compiler.values.ValueSet;
import souther.compiler.values.ValuesWithin;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;
import java.util.function.Supplier;

/**
 * What the rules about one position divide it into, in the one vocabulary they can all be said in.
 *
 * <p><b>The question is the vocabulary, and not which kind of evidence arrived.</b> A position is
 * divided by everything the model says about it, and what this decides is whether all of that can be
 * said as one exclusive and exhaustive list of classes. Branching instead on which kind of rule was
 * met, a position reached by two kinds had the classes of whichever kind the branch happened to
 * name, and the other kind's distinctions went missing from the denominator with nothing said.
 *
 * <p><b>Two vocabularies today.</b> A rule can put a line on the order the values are counted on, or
 * tell a set of them from the rest. Both divide a position and neither is the other: a run of values
 * has a least and a next, and a set has neither, so a class in one of them cannot be written in the
 * other. A position reached by both is one this compiler has no single list of classes for, and it
 * comes back saying so rather than divided by the half that happened to be expressible.
 *
 * <p><b>Nothing else is lost by that.</b> Where the classes are not composed, the cuts a line drew
 * and the places the rules part the position are still what they were — they are separate
 * observations about the position and not a projection of the classes. What goes is the denominator,
 * which is the thing that would have been wrong.
 *
 * <p>And a class exists because the model divides the position, never because a value can be written
 * into a row for it. A class nobody can compose a value for says that about itself; dropped instead,
 * the denominator a build is measured against would follow what this compiler can generate.
 */
final class Classing {

    private Classing() {
    }

    /**
     * Which vocabulary a position's rules can all be said in.
     *
     * <p>The one place the question is answered. Asked again by whoever is assembling the measure,
     * the two would agree by having been written alike — until one of them learned about a third
     * vocabulary, and then a position would be divided by one answer and accounted for by the other.
     */
    enum Vocabulary {

        /**
         * Every rule is a distinction on the order the values are counted on: a line drawn on it,
         * or a value singled out of it.
         *
         * <p>Not every class this leaves is a run. A value singled out beside a line is a class of
         * its own, and the run it falls in is a class without it ({@link OrderedClasses}).
         */
        ON_AN_ORDER,

        /** Every rule tells a set of the values from the rest. */
        BY_SETS,

        /**
         * The rules are not all in one vocabulary, so the position has no classes.
         *
         * <p>A class on an order and a class that is a set cannot be written as each other: a run
         * of values has a least and a next, and a set has neither. Divided by the half that happened
         * to be expressible, a run would be counted at a class the model tells apart from the one
         * beside it.
         */
        NOT_ONE
    }

    /**
     * Which of the three {@code mine} is, over all of a position's rules and not the first of them.
     *
     * <p>Asked of what each distinction can be said as, and never of which reader produced it. A
     * value singled out of a string is a set of one value and is also a place on the order the
     * strings are counted on, so it goes whichever way the rules beside it go; a value singled out
     * of a number is only the second. A line is only the second, and a set told from the rest is
     * only the first.
     *
     * <p>A position every rule of which draws a line keeps the vocabulary it has always had. Asked
     * the other way round, a position singling out one string would change which algebra its
     * classes are written in the day a set rule was written beside it, and the classes it already
     * had would be rewritten under a rule that says nothing about them.
     */
    static Vocabulary vocabularyOf(List<RuleEvidence> mine, Carrier carrier) {
        boolean sets = true;
        boolean lines = true;
        for (RuleEvidence each : mine) {
            sets &= asASet(each, carrier) != null;
            lines &= !(each instanceof RuleEvidence.BySet);
        }
        if (lines) {
            return Vocabulary.ON_AN_ORDER;
        }
        return sets ? Vocabulary.BY_SETS : Vocabulary.NOT_ONE;
    }

    /**
     * What one piece of evidence tells apart, said as sets, or null where it cannot be said so.
     *
     * <p>The capability the vocabulary is chosen by. A rule that tells a set from the rest has both
     * sides already; a value singled out of a string is the one value and every other string, which
     * is the same distinction written in this algebra rather than a second answer about it. A line
     * has no such writing, and neither has a value singled out of anything but a string — a run of
     * values is not a set this compiler holds, and saying so is what keeps the two apart.
     */
    private static AsASet asASet(RuleEvidence evidence, Carrier carrier) {
        return switch (evidence) {
            case RuleEvidence.BySet(SetStatement it) ->
                    new AsASet(it.whenTrue(), it.whenFalse(), it.statement());
            case RuleEvidence.Singles(GuardThresholds.Guards.Singled it) -> {
                if (!(carrier instanceof Carrier.Text) || !(it.value() instanceof Text text)) {
                    yield null;
                }
                Value one = new Value.Text(text.at());
                yield new AsASet(ValuesWithin.all(new ValueSet.Finite(Set.of(one))),
                        new ValueSet.Cofinite(Set.of(one)),
                        new PredicateStatement.Equalling(text.at()));
            }
            case RuleEvidence.Divides _ -> null;
        };
    }

    /**
     * One distinction of a position, said as the values on either side of it.
     *
     * <p>What a piece of evidence comes to once it is asked to speak this vocabulary. Every kind of
     * evidence that can be said this way answers with one of these and the rest answer with
     * nothing, which is what makes the question about the distinction rather than about which
     * reader produced it.
     *
     * @param whenTrue the values shown on the side the rule holds on, a length and all: what is
     *                 asked of that side is asked of the length as well
     */
    private record AsASet(ValuesWithin whenTrue, ValueSet whenFalse, PredicateStatement states) {}

    /**
     * What the rules of one position came to: the classes, and the rules that make none.
     *
     * <p>Two answers and not one, because they are about different rules. A rule read to the end
     * whose two sides the position does not both hold divides nothing — and it stops nothing
     * either: the rules beside it divide the position as they would have without it. Folded into
     * the first answer, a rule that states no distinction would close a denominator, which is what
     * a distinction gone missing does and this is the opposite of that.
     *
     * @param forEach what became of each rule that was handed in, one entry each. Total over them
     *                by construction: a rule this could not finish qualifying is in the same state
     *                as one it never reached, and both are things a reader is owed — so there is no
     *                way to answer here and leave a rule with nothing said about it
     * @param leftOpen the values of the position each rule shows on neither of its sides, which no
     *                 class holds; none where every rule shows every value on one. Carried by
     *                 every answer, the classes composed or not: it is what the rules left, and
     *                 is owed a question however the classes came out
     */
    record Result(Classed classed, List<Disposed> forEach, List<LeftOpen> leftOpen) {

        Result {
            forEach = List.copyOf(forEach);
            leftOpen = List.copyOf(leftOpen);
        }

        /** The rules the classes were made out of. */
        List<RuleEvidence> dividing() {
            return of(Outcome.DIVIDED);
        }

        /** And the rules the classes were not composed out of, because there are none. */
        List<RuleEvidence> notComposed() {
            return of(Outcome.NOT_COMPOSED);
        }

        private List<RuleEvidence> of(Outcome outcome) {
            return forEach.stream().filter(each -> each.outcome() == outcome)
                    .map(Disposed::what).toList();
        }
    }

    /**
     * What became of one rule handed to this.
     *
     * <p>Four and not two, because a rule this could not finish qualifying is neither of the
     * obvious ones, and a line the classes did not take up is none of them. Left out of the answer,
     * such a rule is one the measure was handed and says nothing about — which the account that
     * follows refuses, and rightly: a position whose classes nobody could compose still owes a
     * sentence about every rule that reached it.
     */
    enum Outcome {

        /**
         * The classes are made out of it: it tells two of the position's values apart, or it
         * leaves some of them open and its classes are drawn over the rest, which may be all on
         * one side of it.
         */
        DIVIDED,

        /**
         * It was read and tells none of them apart, so it makes no class and stops nothing. Said
         * only of a rule shown on one side or the other of every value here: one leaving values
         * open may tell those apart from the rest.
         */
        TOLD_NOTHING_APART,

        /** The position has no classes, so this rule is not among what made any. */
        NOT_COMPOSED,

        /**
         * A line or a value singled out that the classes did not take up, whose answer is the
         * walk's that draws it.
         *
         * <p>Here so that this answer is total over what it was handed without claiming rules it
         * did not decide about. A line makes no class where the classes are sets and none where
         * there are no classes, and it still cuts the position — so what became of it is settled
         * where the cut is made, and an answer saying nothing about it would leave a reader unable
         * to tell "not mine to say" from "forgotten".
         */
        LEFT_TO_THE_WALK
    }

    /** One rule of a position and what became of it. */
    record Disposed(RuleEvidence what, Outcome outcome,
                    BlockReason.RuleWithoutLineReason why) {

        Disposed {
            if ((why == null) != (outcome != Outcome.TOLD_NOTHING_APART)) {
                throw new IllegalArgumentException(
                        "a rule that tells nothing apart says so, and nothing else here does");
            }
        }
    }

    /** What the rules of one position came to. */
    sealed interface Classed {

        /**
         * The order the values are counted on is the vocabulary, so the classes are what the lines
         * and the values singled out leave on it together, which the caller works out.
         *
         * <p>Its own answer and not an empty list of classes. What this says is which algebra the
         * position's classes are written in, and a position genuinely divided into none is a
         * different thing — read off the emptiness, the two would be one answer and a position
         * whose rules divide it nowhere would be sent to the reading that builds runs.
         */
        record OnTheOrder() implements Classed {}

        /** Every rule said as sets, and the classes they leave. */
        record Composed(List<PartitionClass> classes) implements Classed {

            public Composed {
                classes = List.copyOf(classes);
            }
        }

        /**
         * The rules are not all sayable in one vocabulary, so the position has no classes here.
         *
         * <p>Not the classes of the rules that were sayable. A denominator is exclusive and
         * exhaustive or it is not one, and half of a position's rules leave a list that says a run
         * fell in a class the model tells apart from the one beside it.
         */
        record NotComposed(BlockReason.RuleWithoutLineReason why) implements Classed {

            public NotComposed {
                if (why == null) {
                    throw new IllegalArgumentException(
                            "a position whose classes were not composed was stopped by something");
                }
            }
        }
    }

    /**
     * What {@code mine} leaves {@code term} divided into, given everything that reached it.
     *
     * @param blocked the rules that would have divided this position and did not. One of them and
     *                there are no classes, whatever the rest are written in
     * @param writing what a row would carry for a value of this position, or null where nothing
     *                here composes one
     */
    static Result of(NumericTerm.FromOnePosition term, List<RuleEvidence> mine,
                     List<ClassingBlocker> blocked, Carrier carrier, ValueSet admits,
                     Allowance<NumericTerm.FromOnePosition> allowance,
                     Supplier<Meter> perWitness,
                     Function<Place, FixtureTemplate> writing) {
        // Which of the rules actually tell two of this position's values apart, asked before
        // anything else is decided. An invariant restricts and a behavior divides what is left, so
        // a rule whose two sides the position does not both hold states no distinction here — and
        // one that states none must not be in the population that chooses a vocabulary or composes
        // a class. Left in, a rule that divides nothing would put the position's classes in one
        // algebra or the other, and would stand in every label the classes carry.
        List<RuleEvidence> active = new ArrayList<>();
        List<Disposed> told = new ArrayList<>();
        // What each rule leaves open, asked of every rule before anything is composed. It is a
        // fact about the rule and not about the classes: whether the classes come out, and
        // however far this gets before it stops, the values a rule was shown on neither side of
        // are owed a question, and every answer below carries them.
        Map<RuleEvidence, LeftOpen> leaves = new LinkedHashMap<>();
        for (RuleEvidence each : mine) {
            if (!(each instanceof RuleEvidence.BySet set)) {
                continue;
            }
            Worked<LeftOpen> left = leftOpen(term, admits, set.states(), allowance);
            if (left.refused() != null) {
                return notComposed(mine, told, new BlockReason.BehaviorDistinctionsTooCostly(
                        ofTheDistinctions(left.refused())), List.copyOf(leaves.values()));
            }
            if (left.answer() != null) {
                leaves.put(each, left.answer());
            }
        }
        List<LeftOpen> open = List.copyOf(leaves.values());
        for (RuleEvidence each : mine) {
            // Only a rule read as a set of the strings is asked. A line and a value singled out are
            // settled where they were read — the reader that makes one has already held it to what
            // the position may take — and what a rule of the strings names is every string there
            // is, which is the one thing this position's own values have still to be met with.
            //
            // Asked of all of them, a value singled out of a string would buy machines out of the
            // allowance for what a behavior tells apart, and a model that only writes equalities
            // could lose its classes to a limit meant for something else.
            if (!(each instanceof RuleEvidence.BySet set)) {
                active.add(each);
                continue;   // filled in below, once it is known whether the classes took it up
            }
            Worked<Telling> worked = tellsApart(term, admits,
                    new AsASet(set.states().whenTrue(), set.states().whenFalse(),
                            set.states().statement()),
                    leaves.get(each), allowance);
            // What was left to work out is what a run allowed more would have worked out, and the
            // rules already qualified are qualified all the same — but there are no classes for any
            // of them to be part of, so what became of every one of them is the same thing. Said as
            // nothing at all, the account that follows is handed a position whose rules it was owed
            // an answer about and got none.
            if (worked.refused() != null) {
                return notComposed(mine, told, new BlockReason.BehaviorDistinctionsTooCostly(
                        ofTheDistinctions(worked.refused())), open);
            }
            if (worked.answer() == Telling.UNSETTLED) {
                return notComposed(mine, told, new BlockReason.ClassesNotComposed(), open);
            }
            boolean divides = worked.answer() != Telling.NOTHING_APART;
            told.add(divides
                    ? new Disposed(each, Outcome.DIVIDED, null)
                    : new Disposed(each, Outcome.TOLD_NOTHING_APART,
                            new BlockReason.PredicateTellingNothingApart()));
            if (divides) {
                active.add(each);
            }
        }
        // Asked after that, and kept as it was said. A rule missing from the denominator is missing
        // however the rules beside it are written, and what stopped it is a fact about that rule
        // rather than about what the position's rules come to together.
        if (!blocked.isEmpty()) {
            return notComposed(mine, told, blocked.get(0).why(), open);
        }
        switch (vocabularyOf(active, carrier)) {
            case ON_AN_ORDER -> {
                return new Result(new Classed.OnTheOrder(),
                        filled(mine, told, Outcome.LEFT_TO_THE_WALK), open);
            }
            case NOT_ONE -> {
                return notComposed(mine, told, new BlockReason.ClassesNotComposed(), open);
            }
            default -> { }
        }
        List<AsASet> said = new ArrayList<>();
        active.forEach(each -> said.add(asASet(each, carrier)));
        Worked<List<Cell>> refined = refined(term, admits, said, allowance);
        if (refined.refused() != null) {
            return notComposed(mine, told, new BlockReason.BehaviorDistinctionsTooCostly(
                    ofTheDistinctions(refined.refused())), open);
        }
        if (refined.answer() == null) {
            return notComposed(mine, told, new BlockReason.ClassesNotComposed(), open);
        }
        List<Cell> cells = refined.answer();
        // Every value the position holds left open by one rule or another, so no class stands
        // over any of them. The position has no classes, and that is the reason. Each rule that
        // left values open says which, as it does beside classes; the rules beside them left
        // nothing open, and what stopped the classes is not theirs to be told of.
        if (cells.isEmpty() && !open.isEmpty()) {
            return notComposed(mine, told, BlockReason.RelationShownOverARegion.of(
                    open.stream().flatMap(each -> each.open().stream()).toList(),
                    open.stream().flatMap(each -> each.statement().imagesNotShown().stream())
                            .toList(),
                    open.stream().flatMap(each -> each.byCodePoints().stream()).toList()), open);
        }
        List<PartitionClass> out = new ArrayList<>();
        for (Cell cell : cells) {
            out.add(classOf(term, cell, carrier, perWitness, writing).ofTheNumber(term));
        }
        // The classes are sets, so everything that went into them went into them — a value singled
        // out of a string is one of these classes rather than a cut beside them.
        return new Result(new Classed.Composed(out), filled(mine, told, Outcome.DIVIDED), open);
    }

    /**
     * The values of a position one rule shows on neither of its sides, which no class holds: the
     * strings it shows nothing of at any length, and the strings of its true side longer than it
     * is shown at ({@link SetStatement#leftOpen}), each met with what the position holds.
     *
     * @param statement the rule
     * @param open      the values left open, each as long as it is left open at; none of them
     *                  shown to hold nothing
     */
    record LeftOpen(SetStatement statement, List<ValuesWithin> open,
                    List<BlockReason.CodePointsLeftOpen> byCodePoints) {

        LeftOpen {
            if (statement == null || open == null || byCodePoints == null
                    || (open.isEmpty() && byCodePoints.isEmpty())) {
                throw new IllegalArgumentException("a rule leaves some values of a position open");
            }
            open = List.copyOf(open);
            byCodePoints = List.copyOf(byCodePoints);
        }
    }

    /**
     * What {@code statement} leaves open of the values {@code term} holds, or nothing where it
     * shows each of them on one side; or the limit the allowance refused working it out at.
     */
    private static Worked<LeftOpen> leftOpen(NumericTerm.FromOnePosition term, ValueSet admits,
                                             SetStatement statement,
                                             Allowance<NumericTerm.FromOnePosition> allowance) {
        List<ValuesWithin> open = new ArrayList<>();
        for (ValuesWithin each : statement.leftOpen()) {
            Allowance.Composed held =
                    allowance.meet(Sameness.Block.of(term), admits, each.values());
            if (held.gaveUp()) {
                return Worked.refusedAt(held.refused());
            }
            ValuesWithin here = each.over(held.set());
            if (!here.shownToHoldNone()) {
                open.add(here);
            }
        }
        List<BlockReason.CodePointsLeftOpen> byCodePoints = new ArrayList<>();
        for (SetStatement.NotCounted each : statement.notCounted()) {
            Allowance.Composed held =
                    allowance.meet(Sameness.Block.of(term), admits, each.values());
            if (held.gaveUp()) {
                return Worked.refusedAt(held.refused());
            }
            if (!ValuesWithin.all(held.set()).shownToHoldNone()) {
                byCodePoints.add(each.why());
            }
        }
        return Worked.to(open.isEmpty() && byCodePoints.isEmpty() ? null
                : new LeftOpen(statement, open, byCodePoints));
    }

    /**
     * {@code told} with an entry for every rule it does not already answer for.
     *
     * <p>What the answer is total over is what it was handed, and the rules it took no position on
     * are said to be that rather than left out. Left out, a reader cannot tell a rule this decided
     * nothing about from one it forgot — and the account that follows is the reader.
     */
    private static List<Disposed> filled(List<RuleEvidence> mine, List<Disposed> told,
                                         Outcome otherwise) {
        List<Disposed> out = new ArrayList<>();
        for (RuleEvidence each : mine) {
            Disposed already = told.stream().filter(one -> one.what().equals(each))
                    .findFirst().orElse(null);
            out.add(already != null ? already : new Disposed(each, otherwise, null));
        }
        return out;
    }

    /**
     * The position with no classes, and every rule that reached it answered for.
     *
     * <p>What was already proved to tell nothing apart keeps that answer — it is a fact about the
     * rule and stays true whatever became of the rest. A rule read as a set is one the classes were
     * not composed out of, whether this got as far as qualifying it or not; a line or a value
     * singled out still cuts the position, and what became of it is settled where the cut is made.
     *
     * <p>Written here so that the places that say "no classes" say it the same way: one of them
     * keeping its own list is one of them able to leave a rule out. And with what the rules left
     * open, which no class is the reason to drop.
     */
    private static Result notComposed(List<RuleEvidence> mine, List<Disposed> told,
                                      BlockReason.RuleWithoutLineReason why,
                                      List<LeftOpen> open) {
        List<Disposed> out = new ArrayList<>();
        for (RuleEvidence each : mine) {
            Disposed already = told.stream().filter(one -> one.what().equals(each))
                    .findFirst().orElse(null);
            if (already != null && already.outcome() == Outcome.TOLD_NOTHING_APART) {
                out.add(already);
            } else {
                out.add(new Disposed(each,
                        each instanceof RuleEvidence.BySet
                                ? Outcome.NOT_COMPOSED : Outcome.LEFT_TO_THE_WALK, null));
            }
        }
        return new Result(new Classed.NotComposed(why), out, open);
    }

    /**
     * The figure a refusal of a behavior's distinctions was, said as the figures of what a behavior
     * tells apart: what was being built under the allowance here is that and nothing else.
     */
    static Figure ofTheDistinctions(PatternPlan.Refused refused) {
        return refused.as(WorkFigure.BEHAVIOR_DISTINCTIONS_ONE_MACHINE,
                WorkFigure.BEHAVIOR_DISTINCTIONS_IN_ALL);
    }

    /**
     * What working something out under the allowance came to: the answer, or the limit that
     * refused it and no answer.
     *
     * @param answer  what was worked out, or null where it was refused or the reading could not
     *                settle it
     * @param refused the limit that refused it, or null where it was worked out
     */
    private record Worked<T>(T answer, PatternPlan.Refused refused) {

        static <T> Worked<T> to(T answer) {
            return new Worked<>(answer, null);
        }

        static <T> Worked<T> refusedAt(PatternPlan.Refused refused) {
            return new Worked<>(null, refused);
        }
    }

    /**
     * Whether {@code said} tells two of the position's values apart, or the limit the allowance
     * refused working it out at.
     *
     * <p>Both sides against what the position holds, and not against every value there is. A rule
     * can name strings on both sides and have the declarations leave nothing on one of them, which
     * is the position undivided by it however the strings fall.
     *
     * <p>And each side is what it was shown to hold, with {@code open} beside them: the values it
     * was shown on neither side of, which may be on either. A side shown to hold nothing is one
     * that does only where nothing is open, so a rule leaving values open is never one that tells
     * nothing apart. Its classes are drawn over what it was shown on, which is a class to each
     * side shown to hold a value there.
     *
     * @param open what the rule leaves open of the position's values, or null where it leaves
     *             none
     */
    private static Worked<Telling> tellsApart(NumericTerm.FromOnePosition term, ValueSet admits,
                                              AsASet said, LeftOpen open,
                                              Allowance<NumericTerm.FromOnePosition> allowance) {
        Allowance.Composed yes =
                allowance.meet(Sameness.Block.of(term), admits, said.whenTrue().values());
        if (yes.gaveUp()) {
            return Worked.refusedAt(yes.refused());
        }
        Allowance.Composed no = allowance.meet(Sameness.Block.of(term), admits, said.whenFalse());
        if (no.gaveUp()) {
            return Worked.refusedAt(no.refused());
        }
        ValuesWithin holding = said.whenTrue().over(yes.set());
        ValuesWithin failing = ValuesWithin.all(no.set());
        if (open == null && (holding.shownToHoldNone() || failing.shownToHoldNone())) {
            return Worked.to(Telling.NOTHING_APART);
        }
        if (holding.shownToHoldAValue() && failing.shownToHoldAValue()) {
            return Worked.to(Telling.APART);
        }
        return Worked.to(open != null && settled(holding) && settled(failing)
                ? Telling.OVER_WHAT_WAS_SHOWN : Telling.UNSETTLED);
    }

    /** Whether {@code side} is shown to hold a value or shown to hold none. */
    private static boolean settled(ValuesWithin side) {
        return side.shownToHoldAValue() || side.shownToHoldNone();
    }

    /**
     * What a rule did to the values of a position. A side whose strings are not shown to include a
     * value is neither one that holds nothing nor one that holds something, so it is not a rule
     * that tells nothing apart.
     *
     * <p>{@link #OVER_WHAT_WAS_SHOWN} is a rule that leaves values open and is shown to hold a
     * value on one side at most of what it was shown on: whether it tells two values apart turns
     * on the values it was not shown on. Its classes are drawn as any rule's are, over what it was
     * shown on.
     */
    private enum Telling { APART, OVER_WHAT_WAS_SHOWN, NOTHING_APART, UNSETTLED }

    /**
     * One class the rules about a position leave it divided into.
     *
     * <p>A cell of the coarsest partition every distinction's two sides are a union of cells of,
     * which is what several rules about one position come to. Two rules leave four, and a run of the
     * model is in exactly one of them — so four is what the rows are owed at, and the two rules
     * taken one at a time would ask for a distinction the other one already made.
     *
     * <p><b>What each rule states and how it came out, in the order they were read.</b> Where a run
     * falls is decided by each of them coming out one way or the other, and that is what tells a
     * cell from its neighbours — so the assignment is what a cell is, and a reader names the class
     * out of it.
     */
    record Cell(ValuesWithin values, List<Answered> under) {

        Cell {
            if (values == null || values.values().isEmpty()) {
                throw new IllegalArgumentException(
                        "a class of a position holds a value; an empty one is no class of it");
            }
            under = List.copyOf(under);
        }

        /** The same cell, with one more rule coming out {@code holding} and what that leaves. */
        Cell and(ValuesWithin narrowed, PredicateStatement states, boolean holding) {
            List<Answered> wider = new ArrayList<>(under);
            wider.add(new Answered(states, holding));
            return new Cell(narrowed, wider);
        }
    }

    /** One of a position's rules, and whether a value in the cell satisfies it. */
    record Answered(PredicateStatement states, boolean holds) {

        Answered {
            if (states == null) {
                throw new IllegalArgumentException("a rule that came out one way states something");
            }
        }
    }

    /**
     * What {@code said} leaves {@code term} divided into, or the limit the allowance refused it at.
     *
     * <p>Each distinction in turn against what the ones before it left: a cell either satisfies it
     * or does not, and one that would hold no value is no class of the position and is dropped
     * rather than published as a class no run is ever counted at.
     *
     * <p>The limit and not the cells so far. A partition is exclusive and exhaustive or it is not
     * one, and cells the meets got through before the allowance ran out are neither — read as the
     * position's classes, the values in the ones nobody finished would be owed no row at all.
     */
    private static Worked<List<Cell>> refined(NumericTerm.FromOnePosition term, ValueSet admits,
                                              List<AsASet> said,
                                              Allowance<NumericTerm.FromOnePosition> allowance) {
        // What the position holds, which is what the rules of a body divide. Started from the
        // strings instead, a rule would divide values the declarations already refused and the
        // position would come back with classes no run is ever in.
        List<Cell> cells = new ArrayList<>();
        cells.add(new Cell(ValuesWithin.all(admits), List.of()));
        for (AsASet each : said) {
            List<Cell> narrower = new ArrayList<>();
            for (Cell cell : cells) {
                for (boolean holding : new boolean[] {true, false}) {
                    ValuesWithin side = holding ? each.whenTrue()
                            : ValuesWithin.all(each.whenFalse());
                    Allowance.Composed met = allowance.meet(Sameness.Block.of(term),
                            cell.values().values(), side.values());
                    if (met.gaveUp()) {
                        return Worked.refusedAt(met.refused());
                    }
                    ValuesWithin both = cell.values().meeting(side, met.set());
                    if (both.shownToHoldAValue()) {
                        narrower.add(cell.and(both, each.states(), holding));
                    } else if (!both.shownToHoldNone()) {
                        // Neither a class nor none: the cell stands for strings no value may be.
                        return new Worked<>(null, null);
                    }
                }
            }
            cells = narrower;
        }
        return Worked.to(cells);
    }

    /** One cell as a class: what it holds, what it is called, and what a row would carry for it. */
    private static PartitionClass classOf(NumericTerm.FromOnePosition term, Cell cell,
                                          Carrier carrier, Supplier<Meter> perWitness,
                                          Function<Place, FixtureTemplate> writing) {
        String label = said(cell);
        // The words, and not a name of this method's own. What a document shows a reader is the
        // class identity — every kind of class here is named by what it means, prefixed by the
        // number it is a class of — so a name made out of which rules held would be published in
        // place of the words and a reader would be shown nothing they could act on.
        //
        // Which does tie the identity to the wording: a class renamed is a class nothing was
        // recorded at. That is the arrangement every other class in this measure is already under,
        // and one kind of class keeping its own would be a document that reads two ways.
        String id = PartitionClass.idOf(term, label);
        Recognition is = new Recognition.OfASet(cell.values());
        // Over the whole of the order and away from nothing: what the cell holds is already what
        // the rules leave, met together where the cells were refined. An allowance of this class's
        // own, because what one of them costs to write is nothing the class beside it should be
        // short of. Looked for among the values of the cell's lengths, and a value found past them
        // is in no class, so it stands for none.
        Place stands = carrier.somewhereIn(cell.values().toLookIn(),
                new OrderedInterval(null, null), PlacesApart.NONE, perWitness.get());
        if (stands instanceof Text(String text) && !cell.values().has(new Value.Text(text))) {
            stands = null;
        }
        FixtureTemplate written =
                stands == null ? null : writing.apply(stands);
        return written == null
                ? PartitionClass.ungeneratable(id, label, is,
                        "nothing here composed a string of this position that the rules leave in"
                                + " this class")
                : PartitionClass.of(id, label, is,
                        RepresentativeSource.of(written));
    }

    /**
     * What a cell is called: each of the position's rules and how it came out, in the order the
     * body states them.
     *
     * <p>The rules and not where they were written. A class is a set of the position's values, and
     * what names one is what a value in it satisfies — sent to a line and a column, a reader would
     * have to go and read the rule to find out what the class is.
     */
    private static String said(Cell cell) {
        return cell.under().stream()
                .map(each -> each.holds() ? each.states().saidOf("x") : each.states().deniedOf("x"))
                .reduce((one, other) -> one + " and " + other).orElseThrow();
    }

}
