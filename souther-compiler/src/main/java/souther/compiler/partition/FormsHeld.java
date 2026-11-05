package souther.compiler.partition;

import souther.compiler.collect.SharingMap;
import souther.compiler.collect.Stacked;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.Rel;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;

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
 * their form up to a factor ({@link UpToAFactor}), and a statement is told against the groups it
 * may join and not against every group. Below that, every group is told against, which costs
 * less than reading a form up to a factor.
 *
 * <p>A way's walk holds these for each alternative it takes, so a statement taken in makes another
 * of these and leaves the one it was taken into as it was.
 */
final class FormsHeld {

    static final FormsHeld NONE = new FormsHeld(SharingMap.empty(), 0, Filed.NONE);

    /** How many groups are told against one by one before they are filed by their form. */
    private static final int LOOKED_THROUGH = 16;

    /** Where a test in this package counts the groups a statement is told against, and null
     *  everywhere else. Which groups were told against is the same answer whichever were, so how
     *  many has nowhere else to be read. */
    static long[] COUNTING_TOLD;

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
        Optional<UpToAFactor> form = byForm ? UpToAFactor.of(coefs) : Optional.empty();
        for (int at : byForm ? filed.mayBeOfTheForm(form, made) : every(made)) {
            Group group = groups.get(at);
            long[] counting = COUNTING_TOLD;
            if (counting != null) {
                counting[0]++;
            }
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
            refiled = filed.with(made, form);
        } else if (made + 1 > LOOKED_THROUGH) {
            for (int at = 0; at <= made; at++) {
                refiled = refiled.with(at, UpToAFactor.of(wider.get(at).weighing));
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
     * A form up to a factor of either sign: its weights with what the factor can change taken out,
     * the same for a form and for every number times it but for the sign, and read without
     * dividing, so it is read for every form a host's numbers hold.
     *
     * <p>A weight is a sign, a fraction with no two or five in it, and powers of two and five
     * ({@link ExactRatio}). A factor moves every power of two by its own, every power of five by
     * its own, and times every fraction by its fraction. So the powers are held as how far each is
     * above the least of the form's, and the fractions as the one list of whole numbers with no
     * common factor they are a number times: each fraction times the least common multiple of the
     * denominators and over the greatest common divisor of the numerators. That list is one up to
     * its sign, and a form is filed under both signs.
     *
     * <p>Two forms of one key are a number times each other, though not always one the arithmetic
     * holds: one past sixty-four bits of a power of two or of five, or past the host's numbers. A
     * group is made beside the others of its key only where its form is no number the arithmetic
     * holds times theirs. Two powers sixty-four bits hold that are that far apart lie one in each
     * half of what sixty-four bits hold, so the groups of one key each lie in another pair of
     * halves, of the twos and of the fives, and a key holds no more than four groups, save of forms
     * whose factor is past the host's numbers.
     */
    private record UpToAFactor(Map<NumericTerm, Weight> weights) {

        /** A weight up to the factor: the whole number, and the powers above the form's least. */
        record Weight(BigInteger whole, BigInteger twos, BigInteger fives) {}

        /** The form of {@code coefs} up to a factor, or empty where reading it takes a number
         *  past the largest the host holds. */
        static Optional<UpToAFactor> of(Map<NumericTerm, ExactRatio> coefs) {
            try {
                BigInteger divisor = BigInteger.ZERO;
                BigInteger multiple = BigInteger.ONE;
                long leastTwos = Long.MAX_VALUE;
                long leastFives = Long.MAX_VALUE;
                for (ExactRatio each : coefs.values()) {
                    divisor = divisor.gcd(each.numeratorWithoutUnits());
                    BigInteger below = each.denominatorWithoutUnits();
                    multiple = multiple.divide(multiple.gcd(below)).multiply(below);
                    leastTwos = Math.min(leastTwos, each.twos());
                    leastFives = Math.min(leastFives, each.fives());
                }
                Map<NumericTerm, Weight> out = new HashMap<>();
                for (Map.Entry<NumericTerm, ExactRatio> each : coefs.entrySet()) {
                    ExactRatio weight = each.getValue();
                    out.put(each.getKey(), new Weight(
                            weight.numeratorWithoutUnits().divide(divisor)
                                    .multiply(multiple.divide(weight.denominatorWithoutUnits())),
                            BigInteger.valueOf(weight.twos())
                                    .subtract(BigInteger.valueOf(leastTwos)),
                            BigInteger.valueOf(weight.fives())
                                    .subtract(BigInteger.valueOf(leastFives))));
                }
                return Optional.of(new UpToAFactor(out));
            } catch (ArithmeticException _) {
                return Optional.empty();
            }
        }

        UpToAFactor negated() {
            Map<NumericTerm, Weight> out = new HashMap<>();
            weights.forEach((term, weight) -> out.put(term,
                    new Weight(weight.whole().negate(), weight.twos(), weight.fives())));
            return new UpToAFactor(out);
        }
    }

    /**
     * The groups by their form up to a factor, and the groups of a form that takes a number past
     * the host's to read so.
     *
     * <p>A group whose form a statement is a number times is filed under the statement's form up
     * to a factor, or is one of the others.
     */
    private record Filed(SharingMap<UpToAFactor, Stacked<Integer>> byForm,
                         Stacked<Integer> pastTheHost) {

        static final Filed NONE = new Filed(SharingMap.empty(), Stacked.empty());

        /** These with group {@code at}, of {@code form}, or of a form past the host's numbers
         *  where it is empty. */
        Filed with(int at, Optional<UpToAFactor> form) {
            if (form.isEmpty()) {
                return new Filed(byForm, pastTheHost.then(at));
            }
            return new Filed(filedUnder(filedUnder(byForm, form.get(), at),
                    form.get().negated(), at), pastTheHost);
        }

        /** The groups of the {@code made} a statement of {@code form} may join, in the order they
         *  were made: every one where its form is past the host's numbers. */
        List<Integer> mayBeOfTheForm(Optional<UpToAFactor> form, int made) {
            if (form.isEmpty()) {
                return every(made);
            }
            List<Integer> out = new ArrayList<>();
            Stacked<Integer> alike = byForm.get(form.get());
            if (alike != null) {
                out.addAll(alike.inOrder());
            }
            out.addAll(pastTheHost.inOrder());
            out.sort(null);
            return out;
        }

        private static SharingMap<UpToAFactor, Stacked<Integer>> filedUnder(
                SharingMap<UpToAFactor, Stacked<Integer>> filed, UpToAFactor form, int group) {
            Stacked<Integer> before = filed.get(form);
            return filed.with(form,
                    (before == null ? Stacked.<Integer>empty() : before).then(group));
        }
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
