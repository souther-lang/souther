package souther.compiler.partition;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.Rel;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;

/**
 * What the statements of a way that weigh the same terms alike come to together.
 *
 * <p>Statements that are one form up to a factor each hold the form against a level, so together
 * they hold it to a set of the line: {@code h >= 76} and {@code h > 75} hold it above seventy-six,
 * {@code h <= 0} and {@code h > 0} hold it nowhere. Where the set is empty no row comes along the
 * way, and where a relation of that form is the same at every point of the set, the way decides it.
 * Both are shown over the reals, which holds the integers too.
 *
 * <p>The relation asked is given as a statement is: a form and how it stands to nought. So the
 * statements and the relation are read by one rule, and no level is converted from one reading to
 * the other.
 *
 * <p>Only statements of terms read from a position outside every container are taken. Two
 * statements of a term at a position inside a container may be of two elements, which this does not
 * tell apart.
 */
final class WhatStatementsOfOneFormDecide {

    private WhatStatementsOfOneFormDecide() {
    }

    /** What the statements of one form leave: no row at all, or a relation of it decided. */
    record Verdict(boolean noRowArrives, boolean relationIsDecided) {
        static final Verdict NOTHING = new Verdict(false, false);
    }

    /**
     * Whether some statements of {@code stated} that are one form leave no point of the line, and
     * whether the statements of the form of {@code asked} decide it.
     *
     * @param asked the relation asked, or null where nothing is asked
     */
    static Verdict of(List<TakenConstraint.Affine> stated, TakenConstraint.Affine asked) {
        List<TakenConstraint.Affine> left = new ArrayList<>();
        for (TakenConstraint.Affine each : stated) {
            if (each != null && !each.form().coefs().isEmpty() && outsideEveryContainer(each)) {
                left.add(each);
            }
        }
        boolean decided = false;
        while (!left.isEmpty()) {
            TakenConstraint.Affine first = left.removeFirst();
            Map<NumericTerm, ExactRatio> form = first.form().coefs();
            List<Bound> bounds = new ArrayList<>();
            bounds.add(new Bound(ExactRatio.ONE, first));
            for (int i = left.size() - 1; i >= 0; i--) {
                ExactRatio factor = factorBetween(form, left.get(i).form().coefs());
                if (factor != null) {
                    bounds.add(new Bound(factor, left.remove(i)));
                }
            }
            ExactRatio askedFactor = asked == null ? null
                    : factorBetween(form, asked.form().coefs());
            Bound askedBound = askedFactor == null ? null : new Bound(askedFactor, asked);
            List<Boolean> askedAt = new ArrayList<>();
            Boolean empty = pointsLeft(bounds, askedBound, askedAt);
            if (empty == null) {
                continue;
            }
            if (empty) {
                return new Verdict(true, false);
            }
            if (askedBound != null && !askedAt.isEmpty()
                    && askedAt.stream().distinct().count() == 1) {
                decided = true;
            }
        }
        return new Verdict(false, decided);
    }

    /**
     * The statements of {@code stated} that hold the form of {@code asked} to an interval a row
     * can stand anywhere near the line of {@code asked} in, or none where one of them cannot.
     *
     * <p>A row that puts one term at a value beside the relation's line and every other term where
     * the declarations leave it has the form within the greatest weight of the line, whatever
     * the others are: one step of the term moves the form by its weight. Where the statements
     * hold the form on both sides of the line over that far, such a row meets them, and they tie
     * the terms to one another by nothing that row needs. Statements are orders only: an
     * interval is what an order holds a form to, and two of them leave one.
     *
     * <p>What follows from it is only of a reading that moves one term while the others stand
     * where they may: a value of that term is then settled one way or the other, or left either
     * way, as it is without the statements. A reading that moves two terms together moves the
     * form by more than the greatest weight, and the interval need not reach as far as that.
     *
     * @param asked the relation asked as a statement
     */
    static List<TakenConstraint.Affine> leavingRoomAroundTheLine(
            List<TakenConstraint.Affine> stated, TakenConstraint.Affine asked) {
        ExactRatio reach = asked.form().coefs().values().stream().map(ExactRatio::abs)
                .max(ExactRatio::compareTo).orElse(null);
        if (reach == null) {
            return List.of();
        }
        List<Bound> bounds = new ArrayList<>();
        for (TakenConstraint.Affine each : stated) {
            if (each.form().coefs().isEmpty() || !outsideEveryContainer(each)) {
                continue;
            }
            ExactRatio factor = factorBetween(asked.form().coefs(), each.form().coefs());
            if (factor == null) {
                continue;
            }
            if (each.rel() == Rel.EQ || each.rel() == Rel.NE) {
                return List.of();
            }
            bounds.add(new Bound(factor, each));
        }
        ExactRatio line = asked.form().constant().negated();
        ExactRatio below = line.minus(reach).orNull();
        ExactRatio above = line.plus(reach).orNull();
        if (bounds.isEmpty() || below == null || above == null) {
            return List.of();
        }
        for (Bound each : bounds) {
            if (!Boolean.TRUE.equals(each.holdsAt(below))
                    || !Boolean.TRUE.equals(each.holdsAt(above))) {
                return List.of();
            }
        }
        return bounds.stream().map(Bound::statement).toList();
    }

    /** One statement, as its form is {@code factor} times the form of its group. */
    private record Bound(ExactRatio factor, TakenConstraint.Affine statement) {

        /** Where the statement crosses the line of the group's form: where the form it is
         *  {@code factor} times, held with its constant, comes to nought. */
        ExactRatio crossing() {
            return statement.form().constant().negated().dividedBy(factor).orNull();
        }

        /** Whether the statement holds where the group's form is {@code point}; null where it is
         *  not worked out. */
        Boolean holdsAt(ExactRatio point) {
            ExactRatio value = factor.times(point)
                    .flatMap(scaled -> scaled.plus(statement.form().constant())).orNull();
            return value == null ? null : statement.rel().holds(value.signum());
        }
    }

    /**
     * Whether no point of the line holds every bound, or null where that is not worked out; and,
     * for the points that do, whether the asked relation holds at each.
     */
    private static Boolean pointsLeft(List<Bound> bounds, Bound asked, List<Boolean> askedAt) {
        TreeMap<ExactRatio, Integer> crossings = new TreeMap<>(ExactRatio::compareTo);
        ExactRatio[] crossingOf = new ExactRatio[bounds.size()];
        for (int i = 0; i < crossingOf.length; i++) {
            crossingOf[i] = bounds.get(i).crossing();
            if (crossingOf[i] == null) {
                return null;
            }
            crossings.put(crossingOf[i], 0);
        }
        ExactRatio askedCrossing = null;
        if (asked != null) {
            askedCrossing = asked.crossing();
            if (askedCrossing == null) {
                return null;
            }
            crossings.put(askedCrossing, 0);
        }
        List<ExactRatio> points = pointsAround(crossings.keySet());
        if (points == null) {
            return null;
        }
        // The points are in order, each crossing at an odd place, so which side of a statement's
        // crossing a point is on is where it stands beside that place: a statement holds on one
        // side, at the crossing and on the other side as its relation says of the sign of its form.
        int place = 1;
        for (Map.Entry<ExactRatio, Integer> each : crossings.entrySet()) {
            each.setValue(place);
            place += 2;
        }
        int[] holding = new int[points.size() + 1];
        for (int i = 0; i < crossingOf.length; i++) {
            Bound bound = bounds.get(i);
            int at = crossings.get(crossingOf[i]);
            int sign = bound.factor().signum();
            holdOver(holding, 0, at, bound.statement().rel().holds(-sign));
            holdOver(holding, at, at + 1, bound.statement().rel().holds(0));
            holdOver(holding, at + 1, points.size(), bound.statement().rel().holds(sign));
        }
        boolean any = false;
        int count = 0;
        for (int at = 0; at < points.size(); at++) {
            count += holding[at];
            if (count == bounds.size()) {
                any = true;
                if (asked != null) {
                    int askedAtCrossing = crossings.get(askedCrossing);
                    int sign = asked.factor().signum();
                    askedAt.add(asked.statement().rel().holds(
                            at < askedAtCrossing ? -sign : at == askedAtCrossing ? 0 : sign));
                }
            }
        }
        return !any;
    }

    /** Counts a statement as holding at the places from {@code from} up to {@code to}, where it
     *  does. */
    private static void holdOver(int[] holding, int from, int to, boolean holds) {
        if (holds && from < to) {
            holding[from]++;
            holding[to]--;
        }
    }

    /** Each crossing, a point between each two, and one beyond each end: the line is the same
     *  between crossings, so these show every way it can stand. Null where one is not worked out. */
    private static List<ExactRatio> pointsAround(Set<ExactRatio> crossings) {
        List<ExactRatio> points = new ArrayList<>();
        ExactRatio previous = null;
        for (ExactRatio each : crossings) {
            ExactRatio before = previous == null ? each.minus(ExactRatio.ONE).orNull()
                    : previous.plus(each).flatMap(sum -> sum.dividedBy(ExactRatio.of(2))).orNull();
            if (before == null) {
                return null;
            }
            points.add(before);
            points.add(each);
            previous = each;
        }
        ExactRatio beyond = previous.plus(ExactRatio.ONE).orNull();
        if (beyond == null) {
            return null;
        }
        points.add(beyond);
        return points;
    }

    /** {@code other} as a number times {@code form}, or null where it is not one. */
    static ExactRatio factorBetween(Map<NumericTerm, ExactRatio> form,
                                            Map<NumericTerm, ExactRatio> other) {
        if (!form.keySet().equals(other.keySet())) {
            return null;
        }
        ExactRatio factor = null;
        for (Map.Entry<NumericTerm, ExactRatio> each : form.entrySet()) {
            ExactRatio here = other.get(each.getKey()).dividedBy(each.getValue()).orNull();
            if (here == null || here.isZero() || (factor != null && factor.compareTo(here) != 0)) {
                return null;
            }
            factor = here;
        }
        return factor;
    }

    static boolean outsideEveryContainer(TakenConstraint.Affine statement) {
        for (NumericTerm each : statement.form().coefs().keySet()) {
            if (!(each instanceof NumericTerm.FromOnePosition one)
                    || one.position().insideAContainer()) {
                return false;
            }
        }
        return true;
    }
}
