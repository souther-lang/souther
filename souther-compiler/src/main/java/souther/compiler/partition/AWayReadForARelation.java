package souther.compiler.partition;

import souther.compiler.inputs.CasesLeft;
import souther.compiler.inputs.NameReach;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Refinement;
import souther.compiler.inputs.Requirements;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.types.TypeSymbol;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collections;
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
         * The ends between which the declarations leave {@code term} every value and no other,
         * where no rule of a value around it names it — or null where that is not shown.
         */
        NumericDomain.Bounds leaveEveryValueBetween(NumericTerm term);

        /** Whether some value of the case {@code leaf} is shown to exist. */
        boolean leaveAValueOf(TypeSymbol leaf);
    }

    private final Reachability.Ways.Whole whole;
    private final Declarations declarations;

    /** The positions bearing on the relation, widened as the way is read. */
    private final Set<TermPath> bearing;

    private AWayReadForARelation(Reachability.Ways.Whole whole, Set<TermPath> read,
                                 Declarations declarations) {
        this.whole = whole;
        this.declarations = declarations;
        this.bearing = new LinkedHashSet<>(read);
    }

    /**
     * The way {@code whole} was read from, read again for a relation reading {@code read} — or
     * empty where no choice on it is shown to come to less than it is.
     */
    static Optional<Reachability> of(Reachability.Ways.Whole whole, Set<TermPath> read,
                                     Declarations declarations) {
        if (!whole.from().way().declined().isEmpty()) {
            return Optional.empty();
        }
        return new AWayReadForARelation(whole, read, declarations).readAgain();
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
                asked.add(positionsOf(each));
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
                } else if (bearing.addAll(positionsOf(each))) {
                    again = true;
                    break;
                }
            }
            if (again) {
                continue;
            }
            List<ChoiceRead> met = new ArrayList<>();
            if (!metApart(stated, met)) {
                return Optional.empty();
            }
            for (OnTheWay each : whole.unsplit()) {
                ChoiceRead one = parted.get(each);
                if (one == null || one.whole()) {
                    continue;
                }
                met.add(one);
                if (!metApart(stated, met)) {
                    keptWhole.add(each);
                    bearing.addAll(positionsOf(each));
                    again = true;
                    break;
                }
            }
        }
        if (parted.values().stream().allMatch(ChoiceRead::whole)) {
            return Optional.empty();
        }
        List<OnTheWay> rest = new ArrayList<>();
        for (OnTheWay each : entries) {
            ChoiceRead one = parted.get(each);
            if (one == null) {
                rest.add(each);
            } else {
                one.standingFor().ifPresent(rest::add);
            }
        }
        return Optional.of(whole.from().readAs(rest));
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
     * taking the alternatives of the choices in one such part together is asked ({@link Part#met}),
     * and where they are more ways than a way is looked along, nothing is shown.
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
        return stated.stream().filter(one -> !bearsOn(positionsOf(one), bearing)).toList();
    }

    /** What of {@code stated} asks of positions bearing on the relation. */
    private List<OnTheWay> bearingOf(List<OnTheWay> stated) {
        return stated.stream().filter(one -> bearsOn(positionsOf(one), bearing)).toList();
    }

    /**
     * The conditions {@code together} and the alternatives of {@code each} ask apart, gathered
     * into parts no two of which ask of one position or of two the declarations tie.
     */
    private List<Part> partsApart(List<OnTheWay> together, List<ChoiceRead> each) {
        List<Part> out = new ArrayList<>();
        for (OnTheWay one : together) {
            joined(out, positionsOf(one)).conditions.add(one);
        }
        for (ChoiceRead choice : each) {
            for (int alternative = 0; alternative < choice.apart().size(); alternative++) {
                for (OnTheWay one : choice.apart().get(alternative)) {
                    joined(out, positionsOf(one)).asked(choice, alternative, one);
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

        void asked(ChoiceRead choice, int alternative, OnTheWay condition) {
            alternatives.computeIfAbsent(choice, _ -> new LinkedHashMap<>())
                    .computeIfAbsent(alternative, _ -> new ArrayList<>()).add(condition);
        }

        void take(Part other) {
            positions.addAll(other.positions);
            conditions.addAll(other.conditions);
            other.alternatives.forEach((choice, byAlternative) ->
                    byAlternative.forEach((alternative, those) ->
                            those.forEach(one -> asked(choice, alternative, one))));
        }

        /**
         * Whether every way of taking the alternatives of the choices here together is met: a
         * value meets the conditions here beside what those alternatives ask here, or no row
         * takes what they ask bearing on the relation beside what the way states of it. Under
         * {@code (x <= 0 && z == 0 || x >= 10 && z == 1)} and
         * {@code (x <= 3 && z == 0 || x >= 7 && z == 1)}, no {@code z} is nought and one, and
         * no {@code x} is at or below nought and at or above seven either.
         */
        boolean met(List<OnTheWay> stated) {
            List<ChoiceRead> those = new ArrayList<>(alternatives.keySet());
            long count = 1;
            for (ChoiceRead each : those) {
                count *= each.apart().size();
                if (count > CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG.maximum()) {
                    return false;
                }
            }
            return metAlongEach(those, 0, conditions, bearingOf(stated));
        }

        private boolean metAlongEach(List<ChoiceRead> those, int at, List<OnTheWay> apart,
                                     List<OnTheWay> bearingTaken) {
            if (at == those.size()) {
                return aValueMeets(apart)
                        || !(whole.from().readAs(bearingTaken) instanceof Reachability.Reaching);
            }
            ChoiceRead choice = those.get(at);
            for (int alternative = 0; alternative < choice.apart().size(); alternative++) {
                List<OnTheWay> withApart = new ArrayList<>(apart);
                withApart.addAll(alternatives.get(choice).getOrDefault(alternative, List.of()));
                List<OnTheWay> withBearing = new ArrayList<>(bearingTaken);
                withBearing.addAll(choice.bearing().get(alternative));
                if (!metAlongEach(those, at + 1, withApart, withBearing)) {
                    return false;
                }
            }
            return true;
        }
    }

    /**
     * Whether some value is shown to meet what {@code onTheWay} asks of the positions not bearing
     * on the relation, beside the declarations, along one of the ways it comes to
     * ({@link #metBySomeValue}).
     */
    private boolean aValueMeets(List<OnTheWay> onTheWay) {
        if (!(whole.from().readAs(onTheWay) instanceof Reachability.Reaching meeting)) {
            return false;
        }
        List<Reachability.Reaching> open = switch (meeting.ways()) {
            case Reachability.Ways.One _ -> List.of(meeting);
            case Reachability.Ways.Each each -> each.along();
            case Reachability.Ways.Whole each -> each.along();
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
            into.add(positionsOf(entry));
        }
    }

    /** The positions {@code entry} asks of, inside its alternatives and its statements as
     *  well. */
    private static Set<TermPath> positionsOf(OnTheWay entry) {
        Set<TermPath> out = new LinkedHashSet<>(WayToTheBorder.positionsOf(entry));
        if (entry.ofSeveralWays()) {
            entry.alternatives().forEach(alternative ->
                    alternative.forEach(one -> out.addAll(positionsOf(one))));
        }
        if (entry instanceof OnTheWay.Counted counted) {
            counted.parts().forEach(one -> out.addAll(positionsOf(one)));
        }
        return out;
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
     * @param bearing what each alternative asks that bears on the relation, in their order
     * @param apart   what each asks apart from that
     */
    record ChoiceRead(OnTheWay choice, List<List<OnTheWay>> bearing,
                      List<List<OnTheWay>> apart) {

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
                        (reading.bearsOn(positionsOf(each), reading.bearing) ? on : off).add(each);
                    }
                }
                bearing.add(on);
                apart.add(off);
            }
            ChoiceRead out = new ChoiceRead(choice, bearing, apart);
            return out.whole() || out.leftOut() || choice instanceof OnTheWay.OneOf ? out : null;
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
            return List.of(new OnTheWay.OneOf(several.condition(), several.anchor(), free,
                    Optional.empty()));
        }

        /** What the choice comes to for the relation, where what it asks apart is met: nothing
         *  where some alternative asks nothing bearing on it, and the parts bearing on it
         *  otherwise. */
        Optional<OnTheWay> standingFor() {
            if (whole()) {
                return Optional.of(choice);
            }
            if (leftOut()) {
                return Optional.empty();
            }
            OnTheWay.OneOf several = (OnTheWay.OneOf) choice;
            return Optional.of(new OnTheWay.OneOf(several.condition(), several.anchor(), bearing,
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
     * <p>The numbers those positions are asked of are given values one at a time
     * ({@link #oneValueEach}), and every statement of them is then worked out at those values.
     * That is the proof: the values are a row's, whatever the region took in or rounded, where
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
                case RowDemand.ATruth truth -> {
                    for (TermPath at : truth.positions()) {
                        if (!declarations.nameNothingAt(at)) {
                            return false;
                        }
                    }
                }
                case RowDemand.Exists _, RowDemand.ForAll _, RowDemand.OneValueAtBoth _,
                     RowDemand.SoMany _, RowDemand.ForTheRun _ -> {
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
        Map<NumericTerm, ExactRatio> values = oneValueEach(numbers, way.region());
        return values != null && numbers.stream().allMatch(each -> holdsAt(each, values));
    }

    /**
     * A whole number for each number {@code statements} are of — or null where one is not shown
     * to be one the declarations leave every value between its ends, or none is left it.
     *
     * <p>Each is given its value where the ones before it stand at theirs. It is one of the whole
     * numbers the region puts it at, between the ends the declarations leave it, that the
     * statements of it and of the numbers already given leave it — those exactly, so a value held
     * out by {@code z /= 0} is passed over and the next taken ({@link WholeNumbersLeft}). What a
     * statement of numbers not yet given leaves it is read off the region, which may put it wider,
     * so the statements are worked out at the values after.
     */
    private Map<NumericTerm, ExactRatio> oneValueEach(List<TakenConstraint.Affine> statements,
                                                      SearchRegion region) {
        Set<NumericTerm> terms = new LinkedHashSet<>();
        statements.forEach(each -> terms.addAll(each.form().coefs().keySet()));
        Map<NumericTerm, ExactRatio> out = new LinkedHashMap<>();
        SearchRegion given = region;
        for (NumericTerm term : terms) {
            NumericDomain.Bounds declared = declarations.leaveEveryValueBetween(term);
            if (declared == null || !(given.projectionOf(term)
                    instanceof NumericDomain.FormProjection.Within(NumericDomain.Bounds put))) {
                return null;
            }
            WholeNumbersLeft left = WholeNumbersLeft.of(put.meet(declared));
            for (TakenConstraint.Affine each : statements) {
                if (left == null) {
                    return null;
                }
                left = leftBy(each, term, out, left);
            }
            BigInteger whole = left == null ? null : left.one();
            if (whole == null) {
                return null;
            }
            out.put(term, ExactRatio.of(whole));
            given = given.given(term, Count.of(new BigDecimal(whole)));
        }
        return out;
    }

    /**
     * What {@code statement} leaves of {@code left}, the whole numbers {@code term} may be, where
     * every other number it is of stands at {@code values}: {@code left} itself where it does not
     * weigh {@code term} or weighs one not given yet, and null where the arithmetic cannot say.
     */
    private static WholeNumbersLeft leftBy(TakenConstraint.Affine statement, NumericTerm term,
                                           Map<NumericTerm, ExactRatio> values,
                                           WholeNumbersLeft left) {
        ExactRatio weight = statement.form().coefs().get(term);
        if (weight == null || weight.isZero()) {
            return left;
        }
        ExactRatio constant = statement.form().constant();
        for (Map.Entry<NumericTerm, ExactRatio> each : statement.form().coefs().entrySet()) {
            if (each.getKey().equals(term)) {
                continue;
            }
            ExactRatio value = values.get(each.getKey());
            if (value == null) {
                return left;
            }
            if (!(each.getValue().times(value) instanceof ExactAnswer.Held<ExactRatio>(
                    ExactRatio weighed))
                    || !(constant.plus(weighed) instanceof ExactAnswer.Held<ExactRatio>(
                            ExactRatio sum))) {
                return null;
            }
            constant = sum;
        }
        return left.meeting(weight, constant, statement.rel());
    }

    /** Whether {@code statement} holds with each number it is of at {@code values} — false where
     *  one is not there, or the arithmetic cannot say. */
    static boolean holdsAt(TakenConstraint.Affine statement, Map<NumericTerm, ExactRatio> values) {
        ExactRatio at = statement.form().constant();
        for (Map.Entry<NumericTerm, ExactRatio> term : statement.form().coefs().entrySet()) {
            ExactRatio value = values.get(term.getKey());
            if (value == null || !(term.getValue().times(value)
                    instanceof ExactAnswer.Held<ExactRatio>(ExactRatio weighed))
                    || !(at.plus(weighed) instanceof ExactAnswer.Held<ExactRatio>(ExactRatio sum))) {
                return false;
            }
            at = sum;
        }
        return statement.rel().holds(at.signum());
    }
}
