package souther.compiler.partition;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.Rel;

import java.util.ArrayList;
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
 */
final class FormsHeld {

    static final FormsHeld NONE = new FormsHeld(List.of());

    /** What taking a statement in came to. */
    sealed interface Taken {

        /** The statements are held together; this is what they leave. */
        record Held(FormsHeld forms) implements Taken {}

        /** The statements of the one form, the last of them the one taken in, leave no point. */
        record NoPointLeft(List<TakenConstraint.Affine> statements) implements Taken {}
    }

    private final List<Group> groups;

    private FormsHeld(List<Group> groups) {
        this.groups = List.copyOf(groups);
    }

    /** These with {@code added} taken in, or the statements of its form where they leave no point
     *  of the line. */
    Taken taking(TakenConstraint.Affine added) {
        Map<NumericTerm, ExactRatio> coefs = added.form().coefs();
        if (coefs.isEmpty() || !WhatStatementsOfOneFormDecide.outsideEveryContainer(added)) {
            return new Taken.Held(this);
        }
        for (int at = 0; at < groups.size(); at++) {
            ExactRatio factor =
                    WhatStatementsOfOneFormDecide.factorBetween(groups.get(at).weighing, coefs);
            if (factor != null) {
                return takenInto(at, groups.get(at), added, factor);
            }
        }
        List<Group> wider = new ArrayList<>(groups);
        Group fresh = new Group(coefs, List.of(), null, false, null, false, null, List.of(),
                false, false);
        Group joined = fresh.with(added, ExactRatio.ONE);
        if (joined.leavesNone()) {
            return new Taken.NoPointLeft(joined.statements);
        }
        wider.add(joined);
        return new Taken.Held(new FormsHeld(wider));
    }

    private Taken takenInto(int at, Group group, TakenConstraint.Affine added, ExactRatio factor) {
        Group joined = group.with(added, factor);
        if (joined.leavesNone()) {
            return new Taken.NoPointLeft(joined.statements);
        }
        List<Group> replaced = new ArrayList<>(groups);
        replaced.set(at, joined);
        return new Taken.Held(new FormsHeld(replaced));
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
     * @param except     the values the form may not be
     * @param unknown    whether a statement crossed the line where the arithmetic cannot say
     * @param clashed    whether two statements asked for two values
     */
    private record Group(Map<NumericTerm, ExactRatio> weighing,
                         List<TakenConstraint.Affine> statements,
                         ExactRatio lowest, boolean lowestOut,
                         ExactRatio highest, boolean highestOut,
                         ExactRatio exactly, List<ExactRatio> except,
                         boolean unknown, boolean clashed) {

        /** This with {@code added}, which is {@code factor} times the form of the group. */
        Group with(TakenConstraint.Affine added, ExactRatio factor) {
            List<TakenConstraint.Affine> taken = new ArrayList<>(statements);
            taken.add(added);
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
            List<ExactRatio> left = except;
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
                left = new ArrayList<>(except);
                left.add(crossing);
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
            for (ExactRatio each : except) {
                if (point.compareTo(each) == 0) {
                    return true;
                }
            }
            return false;
        }
    }
}
