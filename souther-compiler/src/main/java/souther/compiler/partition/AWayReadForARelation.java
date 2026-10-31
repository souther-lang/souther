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
        for (Part part : partsApart(together, each)) {
            if (!part.met(stated)) {
                return false;
            }
        }
        return true;
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
            for (int alternative = 0; alternative < choice.apart().size(); alternative++) {
                for (OnTheWay one : choice.apart().get(alternative)) {
                    joined(out, WayToTheBorder.positionsInside(one))
                            .asked(choice, alternative, one);
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
     *  alternative of a choice asks among them. */
    private final class Part {

        private final Set<TermPath> positions = new LinkedHashSet<>();
        private final List<OnTheWay> conditions = new ArrayList<>();
        private final Map<ChoiceRead, Map<Integer, List<OnTheWay>>> alternatives =
                new IdentityHashMap<>();

        /** The choices here in the order they came, which is the order their ways are asked in:
         *  with the walks counted, which way is asked first decides where they run out. */
        private final List<ChoiceRead> inOrder = new ArrayList<>();

        void asked(ChoiceRead choice, int alternative, OnTheWay condition) {
            alternatives.computeIfAbsent(choice, _ -> {
                inOrder.add(choice);
                return new LinkedHashMap<>();
            }).computeIfAbsent(alternative, _ -> new ArrayList<>()).add(condition);
        }

        void take(Part other) {
            positions.addAll(other.positions);
            conditions.addAll(other.conditions);
            for (ChoiceRead choice : other.inOrder) {
                other.alternatives.get(choice).forEach((alternative, those) ->
                        those.forEach(one -> asked(choice, alternative, one)));
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
         * <p>Only the ways that may hold together are asked, and they are what a way is looked
         * along with ({@link #heldTogether}).
         */
        boolean met(List<OnTheWay> stated) {
            List<OnTheWay> bearingTaken = bearingOf(stated);
            FormsRead forms = new FormsRead();
            List<TakenTogether> ways = heldTogether(bearingTaken, forms);
            if (ways == null) {
                return false;
            }
            List<Set<OnTheWay>> met = new ArrayList<>();
            List<Set<OnTheWay>> notMet = new ArrayList<>();
            for (TakenTogether way : ways) {
                List<OnTheWay> apart = new ArrayList<>(conditions);
                Set<OnTheWay> chosen = new LinkedHashSet<>();
                for (int at = 0; at < inOrder.size(); at++) {
                    ChoiceRead choice = inOrder.get(at);
                    int alternative = way.alternatives().get(at);
                    apart.addAll(alternatives.get(choice).getOrDefault(alternative, List.of()));
                    chosen.addAll(choice.bearing().get(alternative));
                }
                (aValueMeets(apart) ? met : notMet).add(chosen);
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

        /**
         * The ways of taking an alternative of each choice here that may hold together, in the
         * order the choices came and their alternatives in each — or null where they are more
         * than a way is looked along with, which is then a figure this was stopped at.
         *
         * <p>A way no value of whose forms lies in the runs what it asks bearing on the relation
         * leaves them, beside what the way states of the relation, is one no row takes, which is
         * the second half of what {@link #met} accepts, and a way narrower than it is one no row
         * takes either. So such a way is met and not counted, nor is any way it is part of.
         * Choices that each part one number by the same lines — two lookups of one value in one
         * table — hold together only where they agree on the part, and are counted as that many
         * ways and not as the product of their sizes, whether the lines are written in an
         * alternative or in a choice nested in it. Choices of numbers apart from one another hold
         * together in every way, and are counted as the product.
         *
         * <p>What is read of a way is what it leaves at most ({@link FormsLeft}), so it shows no
         * more ways closed than are. And the ways counted are those of the choices taken so far,
         * each time one more is taken, so a way is never counted past the figure only to be closed
         * by the choices after it.
         */
        private List<TakenTogether> heldTogether(List<OnTheWay> bearingTaken, FormsRead forms) {
            List<TakenTogether> ways = List.of(new TakenTogether(List.of(),
                    forms.of(bearingTaken)));
            for (ChoiceRead choice : inOrder) {
                List<TakenTogether> wider = new ArrayList<>();
                for (TakenTogether way : ways) {
                    for (int alternative = 0; alternative < choice.bearing().size();
                         alternative++) {
                        FormsLeft left = way.left().meet(
                                forms.of(choice.bearing().get(alternative)));
                        if (left.holdsNothing()) {
                            continue;
                        }
                        List<Integer> taken = new ArrayList<>(way.alternatives());
                        taken.add(alternative);
                        wider.add(new TakenTogether(taken, left));
                        if (wider.size() > CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG.maximum()) {
                            stoppedAt.add(CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG);
                            return null;
                        }
                    }
                }
                ways = wider;
            }
            return ways;
        }
    }

    /**
     * One way of taking an alternative of each of some choices together, and what it leaves the
     * forms bearing on the relation.
     *
     * @param alternatives the alternative taken of each choice, in their order
     * @param left         what the way leaves the forms, at most
     */
    private record TakenTogether(List<Integer> alternatives, FormsLeft left) {}

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
    private record FormsLeft(Map<CanonicalForm<NumericTerm>, OrderedRuns> runs, boolean exact) {

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
    private record OnOneForm(CanonicalForm<NumericTerm> form, OrderedRuns runs) {}

    /** What conditions leave the forms they bound ({@link FormsLeft}), each condition read once. */
    private static final class FormsRead {

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
     * @param bearing          what each alternative asks that bears on the relation, in their
     *                         order
     * @param apart            what each asks apart from that
     * @param leavesEveryValue whether the parts in {@code bearing} between them are shown to
     *                         leave every value the declarations leave
     */
    record ChoiceRead(OnTheWay choice, List<List<OnTheWay>> bearing,
                      List<List<OnTheWay>> apart, boolean leavesEveryValue) {

        /**
         * {@code choice} parted by the positions {@code reading} has bearing on the relation — or
         * null where it is not read so: a count, whose ways are its statements' and no
         * alternatives, or a choice of cases some of which bear and some not.
         */
        static ChoiceRead of(OnTheWay choice, AWayReadForARelation reading) {
            if (!choice.ofSeveralWays()) {
                return null;
            }
            List<List<OnTheWay>> bearing = new ArrayList<>();
            List<List<OnTheWay>> apart = new ArrayList<>();
            for (List<OnTheWay> alternative : choice.alternatives()) {
                List<OnTheWay> on = new ArrayList<>();
                List<OnTheWay> off = new ArrayList<>();
                for (OnTheWay each : alternative) {
                    // A choice inside an alternative is parted as one on the way is, and what it
                    // comes to for the relation is part of what the alternative does.
                    ChoiceRead inside = each instanceof OnTheWay.OneOf ? of(each, reading) : null;
                    if (inside != null) {
                        inside.standingFor().ifPresent(on::add);
                        off.addAll(inside.toMeet());
                    } else {
                        (reading.bearsOn(WayToTheBorder.positionsInside(each), reading.bearing)
                                ? on : off).add(each);
                    }
                }
                bearing.add(on);
                apart.add(off);
            }
            ChoiceRead out = new ChoiceRead(choice, bearing, apart,
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
        if (!way.declined().isEmpty()) {
            return false;
        }
        List<TakenConstraint.Affine> numbers = new ArrayList<>();
        for (OnTheWay.TakenIn taken : way.boundedOnTheWay()) {
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
        Requirements required = way.requirements();
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
        WholeValuesMeeting.Witness witness = WholeValuesMeeting.of(numbers, way.region(),
                declarations::leaveEveryValueBetween,
                CompositionBudget.PAIRS_OF_BOUNDS_A_WAY_IS_READ_AGAIN_WITH.maximum() - pairs);
        pairs += witness.pairsCombined();
        if (witness instanceof WholeValuesMeeting.Witness.NotShown(boolean past, long _) && past) {
            stoppedAt.add(CompositionBudget.PAIRS_OF_BOUNDS_A_WAY_IS_READ_AGAIN_WITH);
        }
        return witness instanceof WholeValuesMeeting.Witness.Found;
    }
}
