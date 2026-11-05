package souther.compiler.partition;

import souther.compiler.collect.SharingMap;
import souther.compiler.collect.Stacked;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.Rel;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * The relations of numbers a way has taken in, each held to the line of the form it weighs.
 *
 * <p>Statements that weigh the same terms alike are one number against constants, and what they
 * leave of it is where each of them holds at once: a range, a point, or points left out of one.
 * Kept as that, a statement taken in is told against what the others left in a few comparisons,
 * and not by working out where every one of them crosses the line again
 * ({@link WhatStatementsOfOneFormDecide#of}), which grows with how many were taken in before it.
 *
 * <p>Statements inside a container are left out, as {@code of} leaves them: each may be of another
 * element. A statement whose crossing the arithmetic cannot hold leaves its group not worked out,
 * and it stays so.
 *
 * <p>A statement joins the first group, in the order they were made, whose form it is a number
 * times ({@link WhatStatementsOfOneFormDecide#factorBetween}). Past a few groups they are found by
 * their form scaled so that its greatest weight is one either way round ({@link Filed}), and a
 * statement is told against the groups it may join and not against every group. Below that,
 * every group is told against, which costs less than scaling the form.
 *
 * <p>A way's walk holds these for each alternative it takes, so a statement taken in makes another
 * of these and leaves the one it was taken into as it was.
 */
final class FormsHeld {

    static final FormsHeld NONE = new FormsHeld(SharingMap.empty(), 0, Filed.NONE);

    /** How many groups are told against one by one before they are filed by their form. */
    private static final int LOOKED_THROUGH = 16;

    /** What taking a statement in came to. */
    sealed interface Taken {

        /** The statements are held together; this is what they leave. */
        record Held(FormsHeld forms) implements Taken {}

        /** The statements of the one form, the last of them the one taken in, leave no point. */
        record NoPointLeft(List<TakenConstraint.Affine> statements) implements Taken {}
    }

    /** The groups, by the order they were made in, from nought. */
    private final SharingMap<Integer, Group> groups;

    /** How many groups were made. */
    private final int made;

    /** The groups by their form, once there are more than {@link #LOOKED_THROUGH}, and nothing
     *  before. */
    private final Filed filed;

    private FormsHeld(SharingMap<Integer, Group> groups, int made, Filed filed) {
        this.groups = groups;
        this.made = made;
        this.filed = filed;
    }

    /** These with {@code added} taken in, or the statements of its form where they leave no point
     *  of the line. */
    Taken taking(TakenConstraint.Affine added) {
        Map<NumericTerm, ExactRatio> coefs = added.form().coefs();
        if (coefs.isEmpty() || !WhatStatementsOfOneFormDecide.outsideEveryContainer(added)) {
            return new Taken.Held(this);
        }
        boolean byForm = made > LOOKED_THROUGH;
        Map<NumericTerm, ExactRatio> scaled = byForm ? scaled(coefs) : null;
        for (int at : byForm ? filed.mayBeOfTheForm(scaled, made) : every(made)) {
            Group group = groups.get(at);
            ExactRatio factor = WhatStatementsOfOneFormDecide.factorBetween(group.weighing, coefs);
            if (factor != null) {
                Group joined = group.with(added, factor);
                if (joined.leavesNone()) {
                    return new Taken.NoPointLeft(joined.statements.inOrder());
                }
                return new Taken.Held(new FormsHeld(groups.with(at, joined), made, filed));
            }
        }
        Group fresh = new Group(coefs, Stacked.empty(), null, false, null, false, null,
                SharingMap.empty(), false, false);
        Group joined = fresh.with(added, ExactRatio.ONE);
        if (joined.leavesNone()) {
            return new Taken.NoPointLeft(joined.statements.inOrder());
        }
        SharingMap<Integer, Group> wider = groups.with(made, joined);
        Filed refiled = filed;
        if (byForm) {
            refiled = filed.with(made, scaled);
        } else if (made + 1 > LOOKED_THROUGH) {
            for (int at = 0; at <= made; at++) {
                refiled = refiled.with(at, scaled(wider.get(at).weighing));
            }
        }
        return new Taken.Held(new FormsHeld(wider, made + 1, refiled));
    }

    private static List<Integer> every(int made) {
        List<Integer> out = new ArrayList<>(made);
        for (int at = 0; at < made; at++) {
            out.add(at);
        }
        return out;
    }

    /**
     * The groups by their form scaled ({@link #scaled}), filed under it and under its negation,
     * and the groups of a form the arithmetic cannot scale.
     *
     * <p>A form a number times another is scaled to it or to its negation, since the greatest
     * weight of the one is the greatest of the other times that number made positive. So a group
     * whose form a statement is a number times is filed under the statement's form scaled, or is
     * one of a form not scaled.
     */
    private record Filed(SharingMap<Map<NumericTerm, ExactRatio>, Stacked<Integer>> byScaledForm,
                         Stacked<Integer> unscaled) {

        static final Filed NONE = new Filed(SharingMap.empty(), Stacked.empty());

        /** These with group {@code at}, of a form scaled to {@code scaled}, or null where the
         *  arithmetic could not scale it. */
        Filed with(int at, Map<NumericTerm, ExactRatio> scaled) {
            if (scaled == null) {
                return new Filed(byScaledForm, unscaled.then(at));
            }
            Map<NumericTerm, ExactRatio> negated = new HashMap<>();
            scaled.forEach((term, weight) -> negated.put(term, weight.negated()));
            return new Filed(filedUnder(filedUnder(byScaledForm, scaled, at), negated, at),
                    unscaled);
        }

        /** The groups of the {@code made} a statement of a form scaled to {@code scaled} may join,
         *  in the order they were made: every one where the form could not be scaled. */
        List<Integer> mayBeOfTheForm(Map<NumericTerm, ExactRatio> scaled, int made) {
            if (scaled == null) {
                return every(made);
            }
            List<Integer> out = new ArrayList<>();
            Stacked<Integer> alike = byScaledForm.get(scaled);
            if (alike != null) {
                out.addAll(alike.inOrder());
            }
            out.addAll(unscaled.inOrder());
            out.sort(null);
            return out;
        }

        private static SharingMap<Map<NumericTerm, ExactRatio>, Stacked<Integer>> filedUnder(
                SharingMap<Map<NumericTerm, ExactRatio>, Stacked<Integer>> filed,
                Map<NumericTerm, ExactRatio> scaled, int group) {
            Stacked<Integer> before = filed.get(scaled);
            return filed.with(scaled,
                    (before == null ? Stacked.<Integer>empty() : before).then(group));
        }
    }

    /** Each weight of {@code coefs} divided by the greatest of them made positive, or null where
     *  the arithmetic cannot hold one of the quotients. */
    private static Map<NumericTerm, ExactRatio> scaled(Map<NumericTerm, ExactRatio> coefs) {
        ExactRatio greatest = null;
        for (ExactRatio each : coefs.values()) {
            ExactRatio size = each.abs();
            if (greatest == null || size.compareTo(greatest) > 0) {
                greatest = size;
            }
        }
        Map<NumericTerm, ExactRatio> out = new HashMap<>();
        for (Map.Entry<NumericTerm, ExactRatio> each : coefs.entrySet()) {
            ExactRatio scaled = each.getValue().dividedBy(greatest).orNull();
            if (scaled == null) {
                return null;
            }
            out.put(each.getKey(), scaled);
        }
        return out;
    }

    /**
     * The statements of one form and the line they hold it to.
     *
     * @param weighing   the terms of the form and what each weighs, which every statement of the
     *                   group is a number times
     * @param statements the statements taken in, in the order they came
     * @param lowest     the least the form may be, or null where it has none
     * @param lowestOut  whether {@code lowest} itself is left out
     * @param highest    the most the form may be, or null
     * @param highestOut whether {@code highest} itself is left out
     * @param exactly    the one value the form must be, or null
     * @param except     the values the form may not be, each under itself
     * @param unknown    whether a statement crossed the line where the arithmetic cannot say
     * @param clashed    whether two statements asked for two values
     */
    private record Group(Map<NumericTerm, ExactRatio> weighing,
                         Stacked<TakenConstraint.Affine> statements,
                         ExactRatio lowest, boolean lowestOut,
                         ExactRatio highest, boolean highestOut,
                         ExactRatio exactly, SharingMap<ExactRatio, ExactRatio> except,
                         boolean unknown, boolean clashed) {

        /** This with {@code added}, which is {@code factor} times the form of the group. */
        Group with(TakenConstraint.Affine added, ExactRatio factor) {
            Stacked<TakenConstraint.Affine> taken = statements.then(added);
            ExactRatio crossing = added.form().constant().negated().dividedBy(factor).orNull();
            if (crossing == null) {
                return new Group(weighing, taken, lowest, lowestOut, highest, highestOut, exactly,
                        except, true, clashed);
            }
            Rel rel = added.rel();
            int sign = factor.signum();
            boolean below = rel.holds(-sign);
            boolean at = rel.holds(0);
            boolean above = rel.holds(sign);
            ExactRatio low = lowest;
            boolean lowOut = lowestOut;
            ExactRatio high = highest;
            boolean highOut = highestOut;
            ExactRatio exact = exactly;
            boolean clash = clashed;
            SharingMap<ExactRatio, ExactRatio> left = except;
            if (above && !below) {
                if (low == null || crossing.compareTo(low) > 0) {
                    low = crossing;
                    lowOut = !at;
                } else if (!at && crossing.compareTo(low) == 0) {
                    lowOut = true;
                }
            } else if (below && !above) {
                if (high == null || crossing.compareTo(high) < 0) {
                    high = crossing;
                    highOut = !at;
                } else if (!at && crossing.compareTo(high) == 0) {
                    highOut = true;
                }
            } else if (at) {
                if (exact != null && exact.compareTo(crossing) != 0) {
                    clash = true;
                }
                exact = crossing;
            } else {
                left = except.with(crossing, crossing);
            }
            return new Group(weighing, taken, low, lowOut, high, highOut, exact, left, unknown,
                    clash);
        }

        /** Whether no value of the form is where every statement of the group holds. */
        boolean leavesNone() {
            if (unknown) {
                return false;
            }
            if (clashed) {
                return true;
            }
            ExactRatio point = exactly;
            if (lowest != null && highest != null) {
                int order = lowest.compareTo(highest);
                if (order > 0) {
                    return true;
                }
                if (order == 0) {
                    if (lowestOut || highestOut) {
                        return true;
                    }
                    if (point != null && point.compareTo(lowest) != 0) {
                        return true;
                    }
                    point = lowest;
                }
            }
            if (point == null) {
                return false;
            }
            if (lowest != null) {
                int order = point.compareTo(lowest);
                if (order < 0 || (order == 0 && lowestOut)) {
                    return true;
                }
            }
            if (highest != null) {
                int order = point.compareTo(highest);
                if (order > 0 || (order == 0 && highestOut)) {
                    return true;
                }
            }
            // One canonical form per value, so the value left out equal to the point is the one
            // under it.
            return except.get(point) != null;
        }
    }
}
