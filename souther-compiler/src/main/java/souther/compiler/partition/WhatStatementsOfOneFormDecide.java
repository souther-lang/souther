package souther.compiler.partition;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.Rel;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.TreeSet;

/**
 * What the statements of a way that weigh the same terms alike come to together.
 *
 * <p>Statements that are one form up to a factor each hold the form against a level, so together
 * they hold it to a set of the line: {@code h >= 76} and {@code h > 75} hold it above seventy-six,
 * {@code h <= 0} and {@code h > 0} hold it nowhere. Where the set is empty no row comes along the
 * way, and where a relation of that form is the same at every point of the set, the way decides it.
 * Both are shown over the reals, which holds the integers too.
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
     * whether the statements of the form {@code asked} decide {@code asked} held against
     * {@code level} as {@code relation}.
     *
     * @param asked the form the relation is of, or null where nothing is asked
     */
    static Verdict of(List<TakenConstraint.Affine> stated, Map<NumericTerm, ExactRatio> asked,
                      ExactRatio level, Rel relation) {
        List<TakenConstraint.Affine> taken = new ArrayList<>();
        for (TakenConstraint.Affine each : stated) {
            if (each != null && !each.form().coefs().isEmpty() && outsideEveryContainer(each)) {
                taken.add(each);
            }
        }
        boolean decided = false;
        List<TakenConstraint.Affine> left = new ArrayList<>(taken);
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
            boolean ofTheAskedForm = asked != null && level != null
                    && factorBetween(form, asked) != null;
            List<Boolean> askedAt = new ArrayList<>();
            Boolean empty = pointsLeft(bounds, ofTheAskedForm ? asked : null, form, level,
                    relation, askedAt);
            if (empty == null) {
                continue;
            }
            if (empty) {
                return new Verdict(true, false);
            }
            if (ofTheAskedForm && !askedAt.isEmpty() && askedAt.stream().distinct().count() == 1) {
                decided = true;
            }
        }
        return new Verdict(false, decided);
    }

    /** One statement, as its form is {@code factor} times the form of its group. */
    private record Bound(ExactRatio factor, TakenConstraint.Affine statement) {}

    /**
     * Whether no point of the line holds every bound, or null where that is not worked out; and,
     * for the points that do, whether the asked relation holds at each.
     */
    private static Boolean pointsLeft(List<Bound> bounds, Map<NumericTerm, ExactRatio> asked,
                                      Map<NumericTerm, ExactRatio> form, ExactRatio level,
                                      Rel relation, List<Boolean> askedAt) {
        ExactRatio askedFactor = asked == null ? null : factorBetween(form, asked);
        // Where each bound crosses the line, in the form of the group.
        TreeSet<ExactRatio> crossings = new TreeSet<>(ExactRatio::compareTo);
        for (Bound each : bounds) {
            ExactRatio at = each.statement().form().constant().negated()
                    .dividedBy(each.factor()).orNull();
            if (at == null) {
                return null;
            }
            crossings.add(at);
        }
        ExactRatio askedAtLevel = null;
        if (askedFactor != null) {
            askedAtLevel = level.dividedBy(askedFactor).orNull();
            if (askedAtLevel == null) {
                return null;
            }
            crossings.add(askedAtLevel);
        }
        List<ExactRatio> points = new ArrayList<>();
        ExactRatio previous = null;
        for (ExactRatio each : crossings) {
            if (previous == null) {
                ExactRatio below = each.minus(ExactRatio.ONE).orNull();
                if (below == null) {
                    return null;
                }
                points.add(below);
            } else {
                ExactRatio between = previous.plus(each).flatMap(
                        sum -> sum.dividedBy(ExactRatio.of(2))).orNull();
                if (between == null) {
                    return null;
                }
                points.add(between);
            }
            points.add(each);
            previous = each;
        }
        ExactRatio above = previous.plus(ExactRatio.ONE).orNull();
        if (above == null) {
            return null;
        }
        points.add(above);
        boolean any = false;
        for (ExactRatio point : points) {
            boolean holdsAll = true;
            for (Bound each : bounds) {
                ExactRatio value = each.factor().times(point)
                        .flatMap(scaled -> scaled.plus(each.statement().form().constant()))
                        .orNull();
                if (value == null) {
                    return null;
                }
                holdsAll &= each.statement().rel().holds(value.signum());
            }
            if (holdsAll) {
                any = true;
                if (askedAtLevel != null) {
                    // The asked form is its factor times the group's, so a point of the group
                    // stands that factor's sign from the level.
                    int apart = askedFactor.signum() * point.compareTo(askedAtLevel);
                    askedAt.add(relation.holds(apart));
                }
            }
        }
        return !any;
    }

    /** {@code other} as a number times {@code form}, or null where it is not one. */
    private static ExactRatio factorBetween(Map<NumericTerm, ExactRatio> form,
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

    private static boolean outsideEveryContainer(TakenConstraint.Affine statement) {
        for (NumericTerm each : statement.form().coefs().keySet()) {
            if (!(each instanceof NumericTerm.FromOnePosition one)
                    || one.position().insideAContainer()) {
                return false;
            }
        }
        return true;
    }
}
