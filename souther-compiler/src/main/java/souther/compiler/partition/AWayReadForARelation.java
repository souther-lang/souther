package souther.compiler.partition;

import souther.compiler.inputs.CasesLeft;
import souther.compiler.inputs.NameReach;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Refinement;
import souther.compiler.inputs.Requirements;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.CanonicalForm;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.OrderedInterval;
import souther.compiler.numeric.OrderedRuns;
import souther.compiler.numeric.Rel;
import souther.compiler.types.TypeSymbol;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

/**
 * A way past the figure read again for one relation, with each choice on it as it comes to for
 * the values the relation reads.
 *
 * <p>What a relation shows along a way is what it shows of the values its places take there, so
 * ways that differ only in what they leave other places are one way to it, and a choice it does
 * not read is read as often as there are ways of the choices beside it. Three things are shown
 * apart, and only then is a choice read as less ({@link ChoiceRead}).
 *
 * <p>What part of each alternative bears on the relation. A condition bears on it where it asks
 * of a position the relation reads, or one the declarations or a condition on the way bearing on
 * the relation tie to one ({@link #bearingOnTheRelation}), and the rest is apart.
 *
 * <p>That a value meets what is apart, for every way of the choices read as less. A way no
 * contradiction was found on is not that — {@code z > 0 && z < 1} over an {@code Int} is open —
 * so a value is built and the statements are worked out at it ({@link #metBySomeValue}).
 *
 * <p>And then that the values the relation's places take along the way are those they take along
 * what it is read as. A row along the way holds them where some alternative's part bearing on the
 * relation leaves them. And every value of theirs that part leaves, beside the rest of what bears
 * on the relation, stands in a row with a value met apart beside it: the positions apart are tied
 * to none of theirs, by the declarations or by anything left on the way.
 *
 * <p>A condition nothing was read of may tie anything to anything, so where one is on the way
 * nothing is shown. What comes back is read for the relation alone: the way, its choices and the
 * figure that stopped it are still what the generator, the coverage and the reports read.
 */
final class AWayReadForARelation {

    /** What the declarations say of the positions a way is read again over. */
    interface Declarations {

        /** Whether {@code one} and {@code other} are one place or one is inside the other, or a
         *  rule of the declarations ties the two. */
        boolean tie(TermPath one, TermPath other);

        /** Whether no rule of a value around {@code at} names it, so none holds it beside
         *  anything. */
        boolean nameNothingAt(TermPath at);

        /**
         * The ends between which a row may hold {@code term} at every value and at no other: what
         * the declarations leave it, within where its type stops — or null where that is not
         * shown. Shown only of the number at a place every row holds, on a count or a decimal,
         * that no rule of a value around it names.
         */
        NumericDomain.Bounds leaveEveryValueBetween(NumericTerm term);

        /** Whether some value of the case {@code leaf} is shown to exist. */
        boolean leaveAValueOf(TypeSymbol leaf);
    }

    /**
     * What a way read again comes to.
     *
     * @param as        the way read again, or empty where no choice on it is shown to come to
     *                  less than it is, or the walks ran out before it was read
     * @param stoppedAt the figures reached reading it again, past which a choice was kept as it
     *                  stands that might have been shown to come to less: none lose anything where
     *                  {@code as} is read, and each is a figure why where it is not
     */
    record ReadAgain(Optional<Reachability> as, Set<CompositionBudget> stoppedAt) {

        ReadAgain {
            stoppedAt = Set.copyOf(stoppedAt);
        }
    }

    private final Reachability.Ways.Whole whole;
    private final Declarations declarations;

    /** The positions bearing on the relation, widened as the way is read. */
    private final Set<TermPath> bearing;

    /** How many walks this has taken ({@link CompositionBudget#WALKS_A_WAY_IS_READ_AGAIN_WITH}). */
    private int walks;

    /** How many pairs of bounds this has put together
     *  ({@link CompositionBudget#PAIRS_OF_BOUNDS_A_WAY_IS_READ_AGAIN_WITH}). */
    private long pairs;

    /** How many alternatives this has taken in beside the ways of the choices before them
     *  ({@link CompositionBudget#CHOICES_ON_A_WAY_LOOKED_AT}). */
    private int lookedAt;

    private final Set<CompositionBudget> stoppedAt = new LinkedHashSet<>();

    private AWayReadForARelation(Reachability.Ways.Whole whole, Set<TermPath> read,
                                 Declarations declarations) {
        this.whole = whole;
        this.declarations = declarations;
        this.bearing = new LinkedHashSet<>(read);
    }

    /** The way {@code whole} was read from, read again for a relation reading {@code read}. */
    static ReadAgain of(Reachability.Ways.Whole whole, Set<TermPath> read,
                        Declarations declarations) {
        if (!whole.from().way().declined().isEmpty()) {
            return new ReadAgain(Optional.empty(), Set.of());
        }
        AWayReadForARelation reading = new AWayReadForARelation(whole, read, declarations);
        Optional<Reachability> as = reading.readAgain();
        return new ReadAgain(as, reading.stoppedAt);
    }

    /**
     * The way {@code onTheWay} comes to, walked once more — or null where this has walked as often
     * as it reads a way again with, which shows nothing.
     */
    private Reachability walked(List<OnTheWay> onTheWay) {
        if (walks >= CompositionBudget.WALKS_A_WAY_IS_READ_AGAIN_WITH.maximum()) {
            stoppedAt.add(CompositionBudget.WALKS_A_WAY_IS_READ_AGAIN_WITH);
            return null;
        }
        walks++;
        return whole.from().readAs(onTheWay);
    }

    private Optional<Reachability> readAgain() {
        List<OnTheWay> entries = whole.from().way().onTheWay();
        Set<OnTheWay> choices = Collections.newSetFromMap(new IdentityHashMap<>());
        choices.addAll(whole.unsplit());
        // What each condition asks of: one on the way, and one in an alternative of a choice.
        List<Set<TermPath>> asked = new ArrayList<>();
        for (OnTheWay each : entries) {
            if (choices.contains(each) && each.ofSeveralWays()) {
                each.alternatives().forEach(alternative ->
                        alternative.forEach(one -> askedOneByOne(one, asked)));
            } else {
                asked.add(WayToTheBorder.positionsInside(each));
            }
        }
        List<OnTheWay> stated = entries.stream().filter(each -> !choices.contains(each)).toList();
        // A choice whose part apart no value was shown to meet is kept as it is, and the
        // positions it asks of then bear on the relation through it: the rest are parted again.
        Set<OnTheWay> keptWhole = Collections.newSetFromMap(new IdentityHashMap<>());
        Map<OnTheWay, ChoiceRead> parted = new IdentityHashMap<>();
        boolean again = true;
        while (again) {
            again = false;
            bearingOnTheRelation(asked);
            parted.clear();
            for (OnTheWay each : whole.unsplit()) {
                ChoiceRead one = keptWhole.contains(each) ? null : ChoiceRead.of(each, this);
                if (one != null) {
                    parted.put(each, one);
                } else if (bearing.addAll(WayToTheBorder.positionsInside(each))) {
                    again = true;
                    break;
                }
            }
            if (again) {
                continue;
            }
            if (!metApart(stated, List.of())) {
                return Optional.empty();
            }
            List<OnTheWay> lessOf = new ArrayList<>();
            List<ChoiceRead> less = new ArrayList<>();
            for (OnTheWay each : whole.unsplit()) {
                ChoiceRead one = parted.get(each);
                if (one != null && !one.whole()) {
                    lessOf.add(each);
                    less.add(one);
                }
            }
            int first = firstNotMet(stated, less);
            if (first >= 0) {
                keptWhole.add(lessOf.get(first));
                bearing.addAll(WayToTheBorder.positionsInside(lessOf.get(first)));
                again = true;
            }
        }
        boolean readAsLess = false;
        List<OnTheWay> rest = new ArrayList<>();
        for (OnTheWay each : entries) {
            ChoiceRead one = parted.get(each);
            if (one == null) {
                rest.add(each);
            } else {
                readAsLess |= one.comesToLess();
                one.standingFor().ifPresent(rest::add);
            }
        }
        return readAsLess ? Optional.ofNullable(walked(rest)) : Optional.empty();
    }

    /**
     * Whether what the alternatives of a choice ask bearing on the relation, {@code bearing},
     * one or another, holds of every value the declarations leave.
     *
     * <p>Shown where the alternatives between them are read as bounds on one form, and the runs
     * they leave it hold every value the declarations leave the form ({@link FormsLeft#onOneForm}).
     */
    private boolean leavesEveryValueDeclared(List<List<OnTheWay>> bearing) {
        FormsRead forms = new FormsRead();
        FormsLeft left = null;
        for (List<OnTheWay> alternative : bearing) {
            FormsLeft one = forms.of(alternative);
            left = left == null ? one : left.join(one);
        }
        if (left == null || left.everyValue()) {
            return left != null;
        }
        Optional<OnOneForm> bounded = left.onOneForm();
        if (bounded.isEmpty()) {
            return false;
        }
        OrderedRuns everyValue = forms.declared(bounded.get().form(), whole.from().declarations());
        return everyValue != null
                && everyValue.meet(bounded.get().runs()).sameValuesAs(everyValue);
    }

    /**
     * The first of {@code less}, in their order on the way, past which what {@code stated} and the
     * choices up to it ask apart is not shown met — or -1 where all of them together are. What
     * none of them asks apart is met already.
     *
     * <p>Found by halving: where the first so many are met and the first so many more are not,
     * the one kept is among those between. Which choice is kept whole decides how much the
     * relation is read as, and nothing about whether what it is read as is so, which is the choices
     * left being met together, asked again once none is kept. So the halving needs nothing of how
     * the answer for fewer choices goes with the answer for more, and asks as many times as the
     * logarithm of the choices: asked one more at a time, every choice before it is asked again
     * with each, and the walks are as many as the choices and as long as the ones before.
     */
    private int firstNotMet(List<OnTheWay> stated, List<ChoiceRead> less) {
        if (metApart(stated, less)) {
            return -1;
        }
        int met = 0;
        int notMet = less.size();
        while (notMet - met > 1) {
            int half = (met + notMet) >>> 1;
            if (metApart(stated, less.subList(0, half))) {
                met = half;
            } else {
                notMet = half;
            }
        }
        return notMet - 1;
    }

    /**
     * Whether what {@code stated} and the choices {@code read} as less ask apart from the
     * relation is shown met, along every way of those choices a row past them may take.
     *
     * <p>A choice some alternative of which asks nothing bearing on the relation needs that one
     * met ({@link ChoiceRead#toMeet}). A choice every alternative of which bears needs each met,
     * since a row may take any of them: one value meeting all of them at once shows it, and is
     * asked first. Where none does — under {@code (x <= 0 && z == 0 || x >= 10 && z == 1)} no
     * {@code z} is both — each alternative is asked with its own value. Conditions apart that ask
     * of no position in common, nor of two the declarations tie, are met each by its own value,
     * so the alternatives are asked together only where they meet such a condition: every way of
     * taking the alternatives of the choices in one such part together that may hold together is
     * asked ({@link Part#met}), and where they are more ways than a way is looked along, nothing
     * is shown.
     */
    private boolean metApart(List<OnTheWay> stated, List<ChoiceRead> read) {
        List<OnTheWay> all = new ArrayList<>(apartOf(stated));
        List<ChoiceRead> each = new ArrayList<>();
        for (ChoiceRead choice : read) {
            all.addAll(choice.toMeet());
            if (!choice.leftOut()) {
                each.add(choice);
            }
        }
        if (aValueMeets(all)) {
            return true;
        }
        if (each.isEmpty()) {
            return false;
        }
        List<OnTheWay> together = new ArrayList<>(apartOf(stated));
        read.stream().filter(ChoiceRead::leftOut).forEach(one -> together.addAll(one.toMeet()));
        WaysFound found = new WaysFound(bearingOf(stated), each);
        for (Part part : partsApart(together, each)) {
            if (!part.met(stated, found)) {
                return false;
            }
        }
        return true;
    }

    /**
     * The ways of some of the choices asked apart that may hold together, found once for each
     * list of them and asked of by every part they are in
     * ({@link AWayReadForARelation#heldTogether}). Which ways
     * hold together turns on what the choices and the way ask of the relation, which is the same
     * in every part, and not on what a part asks apart.
     */
    private final class WaysFound {

        private final List<OnTheWay> bearingTaken;
        private final Map<ChoiceRead, Integer> numbered = new IdentityHashMap<>();
        private final Map<List<Integer>, List<TakenTogether>> found = new HashMap<>();
        private final FormsRead forms = new FormsRead();

        WaysFound(List<OnTheWay> bearingTaken, List<ChoiceRead> asked) {
            this.bearingTaken = bearingTaken;
            for (ChoiceRead each : asked) {
                numbered.put(each, numbered.size());
            }
        }

        FormsRead forms() {
            return forms;
        }

        /** The ways of {@code choices} that may hold together, or null where finding them
         *  stopped at a figure. */
        List<TakenTogether> of(List<ChoiceRead> choices) {
            List<Integer> key = choices.stream().map(numbered::get).toList();
            List<TakenTogether> ways = found.get(key);
            if (ways == null) {
                ways = heldTogether(choices, bearingTaken, forms);
                if (ways != null) {
                    found.put(key, ways);
                }
            }
            return ways;
        }
    }

    /** What of {@code stated} asks of positions apart from the relation. */
    private List<OnTheWay> apartOf(List<OnTheWay> stated) {
        return stated.stream()
                .filter(one -> !bearsOn(WayToTheBorder.positionsInside(one), bearing)).toList();
    }

    /** What of {@code stated} asks of positions bearing on the relation. */
    private List<OnTheWay> bearingOf(List<OnTheWay> stated) {
        return stated.stream()
                .filter(one -> bearsOn(WayToTheBorder.positionsInside(one), bearing)).toList();
    }

    /**
     * The conditions {@code together} and the alternatives of {@code each} ask apart, gathered
     * into parts no two of which ask of one position or of two the declarations tie.
     */
    private List<Part> partsApart(List<OnTheWay> together, List<ChoiceRead> each) {
        List<Part> out = new ArrayList<>();
        for (OnTheWay one : together) {
            joined(out, WayToTheBorder.positionsInside(one)).conditions.add(one);
        }
        for (ChoiceRead choice : each) {
            for (int leaf = 0; leaf < choice.leaves().size(); leaf++) {
                for (OnTheWay one : choice.leaves().get(leaf).apart()) {
                    joined(out, WayToTheBorder.positionsInside(one)).asked(choice, leaf, one);
                }
            }
        }
        return out;
    }

    /** The part of {@code parts} asking of {@code positions}, made one with every other part
     *  that asks of one of them. */
    private Part joined(List<Part> parts, Set<TermPath> positions) {
        Part into = new Part();
        for (Part part : List.copyOf(parts)) {
            if (bearsOn(positions, part.positions)) {
                into.take(part);
                parts.remove(part);
            }
        }
        into.positions.addAll(positions);
        parts.add(into);
        return into;
    }

    /** Conditions apart from the relation that may ask of a value together, with what each
     *  leaf of a choice asks among them ({@link ChoiceRead.Leaf}). */
    private final class Part {

        private final Set<TermPath> positions = new LinkedHashSet<>();
        private final List<OnTheWay> conditions = new ArrayList<>();
        private final Map<ChoiceRead, Map<Integer, List<OnTheWay>>> leaves =
                new IdentityHashMap<>();

        /** The choices here in the order they came, which is the order their ways are asked in:
         *  with the walks counted, which way is asked first decides where they run out. */
        private final List<ChoiceRead> inOrder = new ArrayList<>();

        void asked(ChoiceRead choice, int leaf, OnTheWay condition) {
            leaves.computeIfAbsent(choice, _ -> {
                inOrder.add(choice);
                return new LinkedHashMap<>();
            }).computeIfAbsent(leaf, _ -> new ArrayList<>()).add(condition);
        }

        void take(Part other) {
            positions.addAll(other.positions);
            conditions.addAll(other.conditions);
            for (ChoiceRead choice : other.inOrder) {
                other.leaves.get(choice).forEach((leaf, those) ->
                        those.forEach(one -> asked(choice, leaf, one)));
            }
        }

        /**
         * Whether every way of taking the alternatives of the choices here together is met: a
         * value meets the conditions here beside what those alternatives ask here, or no row
         * takes what they ask bearing on the relation beside what the way states of it. Under
         * {@code (x <= 0 && z == 0 || x >= 10 && z == 1)} and
         * {@code (x <= 3 && z == 0 || x >= 7 && z == 1)}, no {@code z} is nought and one, and
         * no {@code x} is at or below nought and at or above seven either.
         *
         * <p>Or every value of the relation's places that what they ask bearing on it leaves is
         * one some way met leaves them, with a value met apart beside it. Under
         * {@code (x >= 10 && z <= 1 || x < 10 && z == 5)} and
         * {@code (x >= 10 && z >= 5 || x >= 10 && z == 0 || x < 10 && z == 5)}, no {@code z} is at
         * or below one and at or above five, but every {@code x} at or above ten is one a row
         * takes with {@code z} nought. That no value meets what a way asks apart is not enough on
         * its own: the values it leaves the relation's places may be none a row past the choices
         * holds them at ({@link #insideWhatIsMet}).
         *
         * <p>The ways are those of the choices' leaves, a row past a choice inside an alternative
         * being along one alternative of it ({@link ChoiceRead.Leaf}), and only those that may
         * hold together are asked ({@link AWayReadForARelation#heldTogether}). So no one value has
         * to meet what every
         * leaf asks, and the leaves' values of the relation's places a way met leaves are each
         * met by a value of their own: each value of them is a row with that way's value apart
         * beside it, the positions apart being tied to none of those of the relation.
         *
         * <p>A way is looked along where it is asked by a walk, and as many are looked along as a
         * way is; past that, nothing is shown. A way met by a value its numbers are given without
         * a walk is not looked along ({@link #metByItsNumbersAlone}).
         */
        boolean met(List<OnTheWay> stated, WaysFound found) {
            List<OnTheWay> bearingTaken = bearingOf(stated);
            FormsRead forms = found.forms();
            List<TakenTogether> ways = found.of(inOrder);
            if (ways == null) {
                return false;
            }
            int lookedAlong = 0;
            List<Set<OnTheWay>> met = new ArrayList<>();
            List<Set<OnTheWay>> notMet = new ArrayList<>();
            List<Set<OnTheWay>> notMetUnlooked = new ArrayList<>();
            for (TakenTogether way : ways) {
                List<OnTheWay> apart = new ArrayList<>(conditions);
                Set<OnTheWay> chosen = new LinkedHashSet<>();
                for (int at = 0; at < inOrder.size(); at++) {
                    ChoiceRead choice = inOrder.get(at);
                    int leaf = way.leaves().get(at);
                    apart.addAll(leaves.get(choice).getOrDefault(leaf, List.of()));
                    chosen.addAll(choice.leaves().get(leaf).bearing());
                }
                switch (metByItsNumbersAlone(apart)) {
                    case MET -> met.add(chosen);
                    case NOT_MET -> notMetUnlooked.add(chosen);
                    case NOT_ASKED -> {
                        if (lookedAlong >= CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG.maximum()) {
                            stoppedAt.add(CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG);
                            return false;
                        }
                        lookedAlong++;
                        (aValueMeets(apart) ? met : notMet).add(chosen);
                    }
                }
            }
            for (Set<OnTheWay> chosen : notMetUnlooked) {
                if (!insideWhatIsMet(chosen, met, forms)) {
                    if (lookedAlong >= CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG.maximum()) {
                        stoppedAt.add(CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG);
                        return false;
                    }
                    lookedAlong++;
                    notMet.add(chosen);
                }
            }
            for (Set<OnTheWay> chosen : notMet) {
                if (insideWhatIsMet(chosen, met, forms)) {
                    continue;
                }
                List<OnTheWay> bearingAlong = new ArrayList<>(bearingTaken);
                bearingAlong.addAll(chosen);
                Reachability taken = walked(bearingAlong);
                if (taken == null || taken instanceof Reachability.Reaching) {
                    return false;
                }
            }
            return true;
        }

        /**
         * Whether every row {@code chosen}, what a way asks of the relation beside what the way
         * states of it, leaves is one some way of {@code met} leaves, each what such a way asks.
         * What the way states is asked of all of them alike, so it is left out.
         *
         * <p>Shown where {@code chosen} asks all one of them asks and more. Or where all of what
         * {@code chosen} asks is read as bounds on one form, the alternatives of a choice in it
         * too: the runs of the form it leaves are then inside those left together by the ways of
         * {@code met} that are read so as well ({@link FormsLeft#onOneForm}). That is how choices
         * that part one number by the same lines are read, where what each alternative asks apart
         * was asked of every line at once ({@link ChoiceRead#toMeet}) and so is met by no value
         * beside another.
         */
        private static boolean insideWhatIsMet(Set<OnTheWay> chosen, List<Set<OnTheWay>> met,
                                               FormsRead forms) {
            if (met.stream().anyMatch(chosen::containsAll)) {
                return true;
            }
            Optional<OnOneForm> asked = forms.of(chosen).onOneForm();
            if (asked.isEmpty()) {
                return false;
            }
            OnOneForm left = asked.get();
            OrderedRuns leftByMet = OrderedRuns.nothing();
            for (Set<OnTheWay> each : met) {
                FormsLeft one = forms.of(each);
                if (one.everyValue()) {
                    return true;
                }
                Optional<OnOneForm> same = one.onOneForm();
                if (same.isPresent() && same.get().form().equals(left.form())) {
                    leftByMet = leftByMet.join(same.get().runs());
                }
            }
            return left.runs().meet(leftByMet).sameValuesAs(left.runs());
        }
    }

    /**
     * The ways of taking a leaf of each of {@code choices} that may hold together, in the order
     * the choices came and their leaves in each — or null where this has taken in as many leaves
     * as a way's choices are looked at with, which is then a figure this was stopped at.
     *
     * <p>A way no value of whose forms lies in the runs what it asks bearing on the relation
     * leaves them, beside what the way states of the relation, is one no row takes, which is the
     * second half of what {@link Part#met} accepts, and a way narrower than it is one no row takes
     * either. So such a way is met and not counted, nor is any way it is part of.
     * Choices that each part one number by the same lines — two lookups of one value in one table
     * — hold together only where they agree on the part, and are counted as that many ways and
     * not as the product of their sizes, whether the lines are written in an alternative or in a
     * choice nested in it. Choices of numbers apart from one another hold together in every way,
     * and are counted as the product.
     *
     * <p>What is read of a way is what it leaves at most ({@link FormsLeft}), so it shows no more
     * ways closed than are. A leaf is taken in beside a way only where the runs they leave the
     * one form they are looked up by meet ({@link LeavesByOneForm}), so leaves parting a value by
     * a table's lines are taken in beside the ways of their own line and not beside every way,
     * and the ways of two such choices are found in as many steps as they have lines. Every leaf
     * taken in is one looked at, as the walk of a way counts the alternatives it takes in to find
     * its open ways ({@link OneOfEach}), and counted over the whole reading again. How many of
     * the ways found are looked along is {@link Part#met}'s to count.
     */
    private List<TakenTogether> heldTogether(List<ChoiceRead> choices,
                                             List<OnTheWay> bearingTaken, FormsRead forms) {
        List<TakenTogether> ways = List.of(new TakenTogether(List.of(), forms.of(bearingTaken)));
        for (ChoiceRead choice : choices) {
            List<FormsLeft> leftByLeaves = choice.leaves().stream()
                    .map(leaf -> forms.of(leaf.bearing())).toList();
            LeavesByOneForm byForm = LeavesByOneForm.of(leftByLeaves);
            List<TakenTogether> wider = new ArrayList<>();
            for (TakenTogether way : ways) {
                for (int leaf : byForm.meeting(way.left())) {
                    if (lookedAt >= CompositionBudget.CHOICES_ON_A_WAY_LOOKED_AT.maximum()) {
                        stoppedAt.add(CompositionBudget.CHOICES_ON_A_WAY_LOOKED_AT);
                        return null;
                    }
                    lookedAt++;
                    FormsLeft left = way.left().meet(leftByLeaves.get(leaf));
                    if (left.holdsNothing()) {
                        continue;
                    }
                    List<Integer> taken = new ArrayList<>(way.leaves());
                    taken.add(leaf);
                    wider.add(new TakenTogether(taken, left));
                }
            }
            ways = wider;
        }
        return ways;
    }

    /**
     * One way of taking a leaf of each of some choices together, and what it leaves the forms
     * bearing on the relation.
     *
     * @param leaves the leaf taken of each choice, in their order ({@link ChoiceRead#leaves})
     * @param left   what the way leaves the forms, at most
     */
    private record TakenTogether(List<Integer> leaves, FormsLeft left) {}

    /**
     * The leaves of a choice, looked up by the runs they leave the one form most of them bound,
     * so that the leaves a way may hold together with are found without taking in every leaf.
     *
     * <p>A leaf whose runs of the form lie apart from a way's holds together with it in no row:
     * the way leaves the form at most its runs and the leaf at most its own. It is passed over. A
     * leaf bounding no such form, and every leaf beside a way bounding none, may hold together,
     * and is found. A leaf leaving some form nothing is no way at all and is never found. The
     * leaves found are in their order on the choice.
     *
     * <p>Looked up by the ends around each leaf's runs, lowest lower end first, with the loosest
     * upper end of every leaf up to each: the leaves whose runs start before a way's end are the
     * first so many, and of those the ones reaching past where the way starts are found by going
     * back from the last until no leaf before reaches it.
     */
    private static final class LeavesByOneForm {

        private final CanonicalForm<NumericTerm> form;
        private final List<Integer> every = new ArrayList<>();
        private final List<Integer> free = new ArrayList<>();
        private final List<Integer> byLowerEnd = new ArrayList<>();
        private final List<OrderedInterval> around = new ArrayList<>();
        private final List<Endpoint> reachedUpTo = new ArrayList<>();

        private LeavesByOneForm(CanonicalForm<NumericTerm> form) {
            this.form = form;
        }

        static LeavesByOneForm of(List<FormsLeft> leaves) {
            Map<CanonicalForm<NumericTerm>, Integer> bounding = new LinkedHashMap<>();
            for (FormsLeft each : leaves) {
                if (!each.holdsNothing()) {
                    each.runs().keySet().forEach(form -> bounding.merge(form, 1, Integer::sum));
                }
            }
            CanonicalForm<NumericTerm> most = null;
            for (Map.Entry<CanonicalForm<NumericTerm>, Integer> each : bounding.entrySet()) {
                if (most == null || each.getValue() > bounding.get(most)) {
                    most = each.getKey();
                }
            }
            LeavesByOneForm out = new LeavesByOneForm(most);
            List<Integer> bounded = new ArrayList<>();
            for (int leaf = 0; leaf < leaves.size(); leaf++) {
                FormsLeft each = leaves.get(leaf);
                if (each.holdsNothing()) {
                    continue;
                }
                out.every.add(leaf);
                (most != null && each.runs().containsKey(most) ? bounded : out.free).add(leaf);
            }
            List<OrderedInterval> hulls = new ArrayList<>();
            for (int leaf : bounded) {
                hulls.add(leaves.get(leaf).runs().get(most).hull());
            }
            List<Integer> order = new ArrayList<>();
            for (int at = 0; at < bounded.size(); at++) {
                order.add(at);
            }
            order.sort((one, other) -> byLowerEnd(hulls.get(one).low(), hulls.get(other).low()));
            Endpoint reached = null;
            for (int at : order) {
                OrderedInterval hull = hulls.get(at);
                reached = out.byLowerEnd.isEmpty() ? hull.high() : loosest(reached, hull.high());
                out.byLowerEnd.add(bounded.get(at));
                out.around.add(hull);
                out.reachedUpTo.add(reached);
            }
            return out;
        }

        /** The leaves that may hold together with a way leaving the forms {@code left}, in their
         *  order on the choice. */
        List<Integer> meeting(FormsLeft left) {
            if (left.holdsNothing()) {
                return List.of();
            }
            OrderedRuns its = form == null ? null : left.runs().get(form);
            if (its == null) {
                return every;
            }
            OrderedInterval way = its.hull();
            int before = 0;
            int after = around.size();
            while (before < after) {
                int half = (before + after) >>> 1;
                if (Endpoint.someValueLiesBetween(around.get(half).low(), way.high())) {
                    before = half + 1;
                } else {
                    after = half;
                }
            }
            List<Integer> found = new ArrayList<>(free);
            for (int at = before - 1; at >= 0
                    && Endpoint.someValueLiesBetween(way.low(), reachedUpTo.get(at)); at--) {
                OrderedInterval leaf = around.get(at);
                if (Endpoint.someValueLiesBetween(Endpoint.lower(leaf.low(), way.low()),
                        Endpoint.upper(leaf.high(), way.high()))) {
                    found.add(byLowerEnd.get(at));
                }
            }
            found.sort(Integer::compare);
            return found;
        }

        /** Lowest first, no end lowest of all ({@link Endpoint#lower}). */
        private static int byLowerEnd(Endpoint one, Endpoint other) {
            if (one == null || other == null) {
                return one == null ? (other == null ? 0 : -1) : 1;
            }
            if (one.sameAs(other)) {
                return 0;
            }
            return Endpoint.lower(one, other) == one ? 1 : -1;
        }

        /** The looser of two upper ends, no end loosest of all ({@link Endpoint#upper}). */
        private static Endpoint loosest(Endpoint one, Endpoint other) {
            if (one == null || other == null) {
                return null;
            }
            return Endpoint.upper(one, other) == one ? other : one;
        }
    }

    /**
     * The runs each form of the input's numbers lies in along a way, as far as conditions bounding
     * it say: every row taking the way has each form in its runs, whatever else it asks.
     *
     * <p>A form is one number of a row only where every position it weighs is one value of the
     * row, outside every container, and those are the conditions read: one asking of an element
     * may ask of another element than the next, which no bound on one number says. That is the
     * rule a walk of the way takes conditions into its region by ({@link WayToTheBorder}), and
     * what it leaves out is left out here. A bound is on its form however it is scaled:
     * {@code 2 * x <= 10} and {@code x <= 5} are one ({@link CanonicalForm}). Turned round,
     * {@code -x >= -5} is a bound on the form turned round, which the form's lowest terms keep
     * apart; read as a form of its own, it is met with no bound on {@code x}, which leaves a way
     * more values and closes none that is open.
     *
     * <p>Over every value of a form between its places and not only those a count steps through,
     * so runs a counted order leaves no value between are still two.
     *
     * @param runs  for each form some condition bounds, the runs it leaves it; a form not here is
     *              left every value
     * @param exact whether every row with each form in its runs takes the way, which is so where
     *              every condition was read as bounds, and the alternatives of a choice too
     */
    record FormsLeft(Map<CanonicalForm<NumericTerm>, OrderedRuns> runs, boolean exact) {

        /** What nothing asks: every value of every form, and every row. */
        static final FormsLeft EVERY_VALUE = new FormsLeft(Map.of(), true);

        /** What a condition read as no bound asks: every value at most, and less than every row. */
        static final FormsLeft NOT_READ = new FormsLeft(Map.of(), false);

        FormsLeft {
            runs = Map.copyOf(runs);
        }

        /** What a row taking both ways leaves the forms. */
        FormsLeft meet(FormsLeft other) {
            Map<CanonicalForm<NumericTerm>, OrderedRuns> both = new HashMap<>(runs);
            other.runs.forEach((form, there) -> both.merge(form, there, OrderedRuns::meet));
            return new FormsLeft(both, exact && other.exact);
        }

        /**
         * What a row taking one way or the other leaves the forms: the runs of each form both
         * bound, joined. Exact where both are and they bound the one form, or one leaves every
         * value; otherwise the rows are not those of runs of each form apart.
         */
        FormsLeft join(FormsLeft other) {
            if (everyValue() || other.everyValue()) {
                return EVERY_VALUE;
            }
            Map<CanonicalForm<NumericTerm>, OrderedRuns> either = new HashMap<>();
            runs.forEach((form, here) -> {
                OrderedRuns there = other.runs.get(form);
                if (there != null) {
                    either.put(form, here.join(there));
                }
            });
            return new FormsLeft(either, exact && other.exact && runs.size() == 1
                    && runs.keySet().equals(other.runs.keySet()));
        }

        /** Whether no row takes the way: some form is left no value. */
        boolean holdsNothing() {
            return runs.values().stream().anyMatch(OrderedRuns::holdsNothing);
        }

        /** Whether every row takes the way. */
        boolean everyValue() {
            return exact && runs.isEmpty();
        }

        /** The one form the way bounds and the runs it leaves it, where the rows taking the way
         *  are exactly those with the form in the runs. */
        Optional<OnOneForm> onOneForm() {
            if (!exact || runs.size() != 1) {
                return Optional.empty();
            }
            Map.Entry<CanonicalForm<NumericTerm>, OrderedRuns> only =
                    runs.entrySet().iterator().next();
            return Optional.of(new OnOneForm(only.getKey(), only.getValue()));
        }
    }

    /** A form, and the runs a way leaves it. */
    record OnOneForm(CanonicalForm<NumericTerm> form, OrderedRuns runs) {}

    /** What conditions leave the forms they bound ({@link FormsLeft}), each condition read once. */
    static final class FormsRead {

        private final Map<OnTheWay, FormsLeft> read = new HashMap<>();

        /** Each form read, as the first bound on it wrote it with its constant left out, and what
         *  that writing is the form times. */
        private final Map<CanonicalForm<NumericTerm>, Written> written = new HashMap<>();

        private record Written(LinearForm<NumericTerm> form, ExactRatio by) {}

        /**
         * The run of {@code form} the declarations leave every value of it in — or null where
         * that is not shown, or {@code form} was not read here. Asked of the form as a bound on
         * it wrote it, and brought back to the form by what that writing is the form times.
         */
        OrderedRuns declared(CanonicalForm<NumericTerm> form, SearchRegion declarations) {
            Written as = written.get(form);
            if (as == null || !(declarations.projectionOf(as.form())
                    instanceof NumericDomain.FormProjection.Within(NumericDomain.Bounds bounds))) {
                return null;
            }
            Endpoint low = bounds.min() == null ? null : divided(bounds.min(), as.by());
            Endpoint high = bounds.max() == null ? null : divided(bounds.max(), as.by());
            if ((bounds.min() != null && low == null) || (bounds.max() != null && high == null)) {
                return null;
            }
            return OrderedRuns.of(new OrderedInterval(low, high));
        }

        /** {@code end} divided by {@code by}, which is positive — or null where that is no
         *  count. */
        private static Endpoint divided(Endpoint end, ExactRatio by) {
            if (!(end.at() instanceof Count count)
                    || !(count.exactly().dividedBy(by)
                            instanceof ExactAnswer.Held<ExactRatio>(ExactRatio at))
                    || !(Count.written(at)
                            instanceof ExactAnswer.Held<Optional<Count>>(Optional<Count> place))
                    || place.isEmpty()) {
                return null;
            }
            return new Endpoint(place.get(), end.inclusive());
        }

        /** What {@code conditions} together leave the forms. */
        FormsLeft of(Collection<OnTheWay> conditions) {
            FormsLeft out = FormsLeft.EVERY_VALUE;
            for (OnTheWay each : conditions) {
                FormsLeft one = read.get(each);
                if (one == null) {
                    one = leftBy(each);
                    read.put(each, one);
                }
                out = out.meet(one);
            }
            return out;
        }

        private FormsLeft leftBy(OnTheWay condition) {
            return switch (condition) {
                case OnTheWay.TakenIn(var _, RowDemand.Relational(
                        TakenConstraint.Affine(LinearForm<NumericTerm> written, Rel rel)))
                        when WayToTheBorder.ofOnePosition(condition) -> leftBy(written, rel);
                case OnTheWay.OneOf several -> {
                    FormsLeft out = null;
                    for (List<OnTheWay> alternative : several.alternatives()) {
                        FormsLeft one = of(alternative);
                        out = out == null ? one : out.join(one);
                    }
                    yield out;
                }
                case OnTheWay.TakenIn _, OnTheWay.Narrowed _, OnTheWay.Settled _,
                     OnTheWay.Counted _, OnTheWay.Declined _ -> FormsLeft.NOT_READ;
            };
        }

        /** What {@code bound rel 0} leaves its form, in lowest terms; not read where its threshold
         *  is no place of the form's order. */
        private FormsLeft leftBy(LinearForm<NumericTerm> bound, Rel rel) {
            if (!(CanonicalForm.of(bound.coefs()) instanceof CanonicalForm.Scaled<NumericTerm>(
                    CanonicalForm<NumericTerm> on, ExactRatio by))) {
                return FormsLeft.NOT_READ;
            }
            // by * on + constant rel 0 is on rel -constant / by.
            if (!(bound.constant().negated().dividedBy(by)
                    instanceof ExactAnswer.Held<ExactRatio>(ExactRatio threshold))
                    || !(Count.written(threshold)
                            instanceof ExactAnswer.Held<Optional<Count>>(Optional<Count> place))
                    || place.isEmpty()) {
                return FormsLeft.NOT_READ;
            }
            written.putIfAbsent(on, new Written(
                    new LinearForm<>(ExactRatio.ZERO, bound.coefs()), by));
            return new FormsLeft(Map.of(on, OrderedRuns.leftBy(rel, place.get())), true);
        }
    }

    /**
     * Whether some value is shown to meet what {@code onTheWay} asks of the positions not bearing
     * on the relation, beside the declarations, along one of the ways it comes to
     * ({@link #metBySomeValue}).
     */
    private boolean aValueMeets(List<OnTheWay> onTheWay) {
        if (!(walked(onTheWay) instanceof Reachability.Reaching meeting)) {
            return false;
        }
        List<Reachability.Reaching> open = switch (meeting.ways()) {
            case Reachability.Ways.One _ -> List.of(meeting);
            case Reachability.Ways.Each each -> each.along();
            case Reachability.Ways.Whole each -> {
                // Only the ways looked along are asked, and the figure past which the rest were
                // not is one of the reasons a choice may be kept as it stands.
                stoppedAt.add(each.figure());
                yield each.along();
            }
        };
        // A way some of whose choices the figure left unchosen asks less than a row along it
        // meets, so only one every choice on which was chosen shows anything.
        return open.stream().anyMatch(each -> each.ways() instanceof Reachability.Ways.One
                && metBySomeValue(each));
    }

    /** What giving the numbers of a way values came to, with no walk of it taken. */
    private enum ByItsNumbers {

        /** A value meeting what the way asks was shown. */
        MET,

        /** None was shown, which is not that none is. */
        NOT_MET,

        /** The way asks something not of its numbers, so this was not asked; a walk is. */
        NOT_ASKED
    }

    /**
     * Whether some value is shown to meet {@code onTheWay} without walking it: asked only where
     * every condition on it is a bound on the input's numbers that a walk would take into its
     * region, each at one value outside every container ({@link WayToTheBorder#ofOnePosition}).
     *
     * <p>Along such a way a row is asked the bounds and nothing else: no choice to split at, no
     * case required and nothing declined. The proof of a way is then of those bounds alone
     * ({@link #metBySomeValue(List, Requirements, SearchRegion)}), and it holds whatever region
     * the values are looked for in, so they are looked for in what the declarations leave with
     * the bounds taken in. A truth, a case, a choice or anything not read is not such a bound,
     * and the way is walked.
     */
    private ByItsNumbers metByItsNumbersAlone(List<OnTheWay> onTheWay) {
        List<OnTheWay.TakenIn> bounded = new ArrayList<>();
        List<TakenConstraint> constraints = new ArrayList<>();
        for (OnTheWay each : onTheWay) {
            if (!(each instanceof OnTheWay.TakenIn taken
                    && taken.demand() instanceof RowDemand.Relational(TakenConstraint.Affine affine)
                    && WayToTheBorder.ofOnePosition(each))) {
                return ByItsNumbers.NOT_ASKED;
            }
            bounded.add(taken);
            constraints.add(affine);
        }
        SearchRegion region = TakenConstraint.narrowedBy(constraints, whole.from().declarations());
        if (TakenConstraint.nothingIsLeftFor(constraints, region)) {
            return ByItsNumbers.NOT_MET;
        }
        return metBySomeValue(bounded, Requirements.NONE, region)
                ? ByItsNumbers.MET : ByItsNumbers.NOT_MET;
    }

    /** Adds to {@code into} what each condition {@code entry} asks of, one by one inside the
     *  alternatives of a choice, which are parted where they stand ({@link ChoiceRead}). */
    private static void askedOneByOne(OnTheWay entry, List<Set<TermPath>> into) {
        if (entry instanceof OnTheWay.OneOf several) {
            several.alternatives().forEach(alternative ->
                    alternative.forEach(one -> askedOneByOne(one, into)));
        } else {
            into.add(WayToTheBorder.positionsInside(entry));
        }
    }

    /**
     * A choice on a way, read for a relation: what each alternative of it asks that bears on the
     * relation, and what it asks apart from that.
     *
     * <p>Three things, by what is apart. Nothing: it is read as it is. Some alternative asks
     * nothing bearing on it: where what that one asks apart is met, every value the relation's
     * places take beside the rest of the way is one some row past the choice holds them at, and
     * the choice comes to nothing for the relation. Otherwise: where what each alternative asks
     * apart is met, a row past the choice holds the relation's places at the values some
     * alternative's part bearing on it leaves, and every such value with a value met apart beside
     * it is a row past the choice — so it comes to the parts bearing on it, which is how
     * {@code !(age >= 70 && ancestor && !apart)} comes to the age alone.
     *
     * <p>And where those parts between them leave the relation's places every value the
     * declarations leave, it comes to nothing for the relation in the same way: a lookup of a
     * value in a table, whose rows' lines leave the value nowhere out
     * ({@link AWayReadForARelation#leavesEveryValueDeclared}).
     *
     * <p>What is asked apart of each way a row takes past it is asked of its {@link Leaf leaves}:
     * an alternative with a choice inside it is one way for each alternative of that choice, and
     * each asks apart what that alternative asks beside what the alternative around it does. A
     * row past a lookup of a value in a table is along one row of the table, and what it asks of
     * the grade compared with is what that row asks, and not what every row asks at once.
     *
     * @param bearing          what each alternative asks that bears on the relation, in their
     *                         order, with a choice inside it as what that choice comes to
     * @param apart            what each asks apart from that, with a choice inside it as what
     *                         that choice is to meet at once ({@link #toMeet})
     * @param leaves           the ways a row takes past it, each with what it asks bearing on
     *                         the relation and apart from it
     * @param leavesEveryValue whether the parts in {@code bearing} between them are shown to
     *                         leave every value the declarations leave
     */
    record ChoiceRead(OnTheWay choice, List<List<OnTheWay>> bearing,
                      List<List<OnTheWay>> apart, List<Leaf> leaves, boolean leavesEveryValue) {

        /**
         * One way a row takes past a choice: an alternative, and an alternative of each choice
         * inside it.
         *
         * @param bearing what it asks that bears on the relation
         * @param apart   what it asks apart from that
         */
        record Leaf(List<OnTheWay> bearing, List<OnTheWay> apart) {

            Leaf {
                bearing = List.copyOf(bearing);
                apart = List.copyOf(apart);
            }

            /** This, asking {@code each} as well, on the side {@code bears} says. */
            Leaf with(OnTheWay each, boolean bears) {
                List<OnTheWay> on = new ArrayList<>(bearing);
                List<OnTheWay> off = new ArrayList<>(apart);
                (bears ? on : off).add(each);
                return new Leaf(on, off);
            }

            /** This, asking what {@code other} does as well. */
            Leaf and(Leaf other) {
                List<OnTheWay> on = new ArrayList<>(bearing);
                on.addAll(other.bearing);
                List<OnTheWay> off = new ArrayList<>(apart);
                off.addAll(other.apart);
                return new Leaf(on, off);
            }
        }

        /**
         * {@code choice} parted by the positions {@code reading} has bearing on the relation — or
         * null where it is not read so: a count, whose ways are its statements' and no
         * alternatives, or a choice of cases some of which bear and some not.
         *
         * <p>Its leaves are as many as the ways of the choices inside its alternatives, up to as
         * many alternatives as a way's choices are looked at with: past that, each alternative is
         * one leaf asking apart what its choices are to meet at once, which is more than any of
         * their ways asks and so shows no more met than is, and the figure is one the reading
         * again stopped at.
         */
        static ChoiceRead of(OnTheWay choice, AWayReadForARelation reading) {
            if (!choice.ofSeveralWays()) {
                return null;
            }
            int most = CompositionBudget.CHOICES_ON_A_WAY_LOOKED_AT.maximum();
            List<List<OnTheWay>> bearing = new ArrayList<>();
            List<List<OnTheWay>> apart = new ArrayList<>();
            List<Leaf> leaves = new ArrayList<>();
            boolean opened = true;
            for (List<OnTheWay> alternative : choice.alternatives()) {
                List<OnTheWay> on = new ArrayList<>();
                List<OnTheWay> off = new ArrayList<>();
                List<Leaf> ways = List.of(new Leaf(List.of(), List.of()));
                for (OnTheWay each : alternative) {
                    // A choice inside an alternative is parted as one on the way is, and what it
                    // comes to for the relation is part of what the alternative does.
                    ChoiceRead inside = each instanceof OnTheWay.OneOf ? of(each, reading) : null;
                    if (inside != null) {
                        inside.standingFor().ifPresent(on::add);
                        off.addAll(inside.toMeet());
                        List<Leaf> wider = new ArrayList<>();
                        for (Leaf way : ways) {
                            for (Leaf in : inside.leaves()) {
                                if (opened && leaves.size() + wider.size() < most) {
                                    wider.add(way.and(in));
                                } else {
                                    opened = false;
                                }
                            }
                        }
                        ways = wider;
                    } else {
                        boolean bears = reading.bearsOn(WayToTheBorder.positionsInside(each),
                                reading.bearing);
                        (bears ? on : off).add(each);
                        ways = ways.stream().map(way -> way.with(each, bears)).toList();
                    }
                }
                bearing.add(on);
                apart.add(off);
                leaves.addAll(ways);
            }
            if (!opened) {
                reading.stoppedAt.add(CompositionBudget.CHOICES_ON_A_WAY_LOOKED_AT);
                leaves.clear();
                for (int each = 0; each < bearing.size(); each++) {
                    leaves.add(new Leaf(bearing.get(each), apart.get(each)));
                }
            }
            ChoiceRead out = new ChoiceRead(choice, bearing, apart, leaves,
                    reading.leavesEveryValueDeclared(bearing));
            return out.whole() || out.leftOut() || choice instanceof OnTheWay.OneOf ? out : null;
        }

        /** Whether the relation is read as less for it than as it stands, where what it asks
         *  apart is met. */
        boolean comesToLess() {
            return !whole() || standingFor().isEmpty();
        }

        /** Whether nothing it asks is apart from the relation. */
        boolean whole() {
            return apart.stream().allMatch(List::isEmpty);
        }

        /** Whether some alternative asks nothing bearing on the relation. */
        boolean leftOut() {
            return bearing.stream().anyMatch(List::isEmpty);
        }

        /**
         * What a value is to meet for this to come to {@link #standingFor}, at once: one of the
         * alternatives asking nothing bearing on the relation, where some does, and what every
         * alternative asks apart otherwise — which is more than it needs, each alternative being
         * met by a value of its own ({@link AWayReadForARelation#metApart}).
         */
        List<OnTheWay> toMeet() {
            if (!leftOut()) {
                return apart.stream().flatMap(List::stream).toList();
            }
            List<List<OnTheWay>> free = new ArrayList<>();
            for (int each = 0; each < bearing.size(); each++) {
                if (bearing.get(each).isEmpty()) {
                    free.add(apart.get(each));
                }
            }
            if (free.size() == 1) {
                return free.getFirst();
            }
            if (free.size() == bearing.size()) {
                return List.of(choice);
            }
            OnTheWay.OneOf several = (OnTheWay.OneOf) choice;
            return List.of(OnTheWay.OneOf.of(several.condition(), several.anchor(), free,
                    Optional.empty()));
        }

        /** What the choice comes to for the relation, where what it asks apart is met: nothing
         *  where the parts bearing on it leave every value the declarations leave, or some
         *  alternative asks nothing bearing on it, and the parts bearing on it otherwise. */
        Optional<OnTheWay> standingFor() {
            if (leavesEveryValue) {
                return Optional.empty();
            }
            if (whole()) {
                return Optional.of(choice);
            }
            if (leftOut()) {
                return Optional.empty();
            }
            OnTheWay.OneOf several = (OnTheWay.OneOf) choice;
            return Optional.of(OnTheWay.OneOf.of(several.condition(), several.anchor(), bearing,
                    Optional.empty()));
        }
    }

    /**
     * Widens the positions bearing on the relation to every position bearing on them: those of
     * each of {@code stated} — what a condition on the way, or one alternative of a choice, asks
     * of — that asks of one bearing on them, until none is left that does.
     *
     * <p>A condition asking of a position the relation reads and of another holds the two
     * together, and so does an alternative asking of both, since which values the one takes then
     * turns on which way the other went. So such a position is one the relation reads through the
     * condition, and a condition asking of it bears on the relation in turn: {@code x} read, and
     * {@code y} tied to it, and {@code z} to {@code y}, bear on it alike.
     */
    private void bearingOnTheRelation(List<Set<TermPath>> stated) {
        boolean[] taken = new boolean[stated.size()];
        boolean grew = true;
        while (grew) {
            grew = false;
            for (int each = 0; each < stated.size(); each++) {
                if (!taken[each] && bearsOn(stated.get(each), bearing)) {
                    bearing.addAll(stated.get(each));
                    taken[each] = true;
                    grew = true;
                }
            }
        }
    }

    /** Whether one of {@code positions} is tied to one of {@code to} ({@link Declarations#tie}). */
    private boolean bearsOn(Set<TermPath> positions, Set<TermPath> to) {
        for (TermPath each : positions) {
            for (TermPath that : to) {
                if (declarations.tie(each, that)) {
                    return true;
                }
            }
        }
        return false;
    }

    /**
     * Whether some value is shown to meet what {@code way} asks of the positions not bearing on
     * the relation, beside the declarations: one way some row may take, open and nothing on it
     * declined.
     *
     * <p>The numbers those positions are asked of are given values, and every statement of them is
     * then worked out at those values ({@link WholeValuesMeeting}). That is the proof: the values
     * are a row's, whatever the region took in or rounded, where
     * the declarations leave each every value between its ends and no rule of a value around it
     * names it, which may hold it beside another. A truth asked of a {@code Bool} no rule around it
     * names is met by one of its values, and a case asked of a position no rule around it names by
     * a value of the case, where one is shown to exist. Anything else asked of those positions
     * shows nothing.
     */
    private boolean metBySomeValue(Reachability.Reaching way) {
        return way.declined().isEmpty()
                && metBySomeValue(way.boundedOnTheWay(), way.requirements(), way.region());
    }

    /**
     * Whether some value is shown to meet {@code bounded}, what a way asks of a row, beside
     * {@code required} and the declarations, values being looked for over {@code region}: the
     * proof {@link #metBySomeValue(Reachability.Reaching)} makes of a way, and the one it makes
     * of a way no walk was taken for ({@link #metByItsNumbersAlone}). The region is where values
     * are looked for and not what they are shown by, so a wider one shows no more.
     */
    private boolean metBySomeValue(List<OnTheWay.TakenIn> bounded, Requirements required,
                                   SearchRegion region) {
        List<TakenConstraint.Affine> numbers = new ArrayList<>();
        for (OnTheWay.TakenIn taken : bounded) {
            if (bearsOn(taken.demand().positions(), bearing)) {
                continue;
            }
            switch (taken.demand()) {
                case RowDemand.Relational(TakenConstraint.Affine affine) -> numbers.add(affine);
                case RowDemand.Relational _ -> {
                    return false;
                }
                // A way asking one Bool for both values is one no row takes, which the walk says
                // ({@link Reachability.NothingReaches}), so the truths of a way taken are met
                // together wherever no rule holds the Bool beside anything.
                case RowDemand.ATruth truth -> {
                    for (TermPath at : truth.positions()) {
                        if (!declarations.nameNothingAt(at)) {
                            return false;
                        }
                    }
                }
                case RowDemand.Exists _, RowDemand.ForAll _, RowDemand.OneValueAtBoth _,
                     RowDemand.SoMany _, RowDemand.OnARemainder _, RowDemand.ForTheRun _ -> {
                    return false;
                }
            }
        }
        for (NameReach.Crossing each : required.crossings()) {
            if (!bearsOn(Set.of(each.at(), each.to()), bearing)) {
                return false;
            }
        }
        for (Map.Entry<TermPath, CasesLeft> each : required.refinements().entrySet()) {
            TermPath at = each.getKey();
            if (bearsOn(Set.of(at), bearing)) {
                continue;
            }
            if (!declarations.nameNothingAt(at)
                    || each.getValue().atoms().stream().noneMatch(atom ->
                            atom instanceof Refinement.SumCase sum
                                    && declarations.leaveAValueOf(sum.leaf()))) {
                return false;
            }
        }
        WholeValuesMeeting.Witness witness = WholeValuesMeeting.of(numbers, region,
                declarations::leaveEveryValueBetween,
                CompositionBudget.PAIRS_OF_BOUNDS_A_WAY_IS_READ_AGAIN_WITH.maximum() - pairs);
        pairs += witness.pairsCombined();
        if (witness instanceof WholeValuesMeeting.Witness.NotShown(boolean past, long _) && past) {
            stoppedAt.add(CompositionBudget.PAIRS_OF_BOUNDS_A_WAY_IS_READ_AGAIN_WITH);
        }
        return witness instanceof WholeValuesMeeting.Witness.Found;
    }
}
