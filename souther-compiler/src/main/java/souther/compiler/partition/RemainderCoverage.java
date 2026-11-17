package souther.compiler.partition;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.partition.UndividedByARelation.WholeEnds;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

/**
 * Whether one number can be chosen to bring a form of numbers to a remainder, for every row of
 * the others.
 *
 * <p>The claim is that every row of the way without the remainder's statements is a row of the
 * way with them once the number {@code pivot} is put somewhere: for every value of the numbers
 * the form holds besides, the pivot has a value that brings the form to every remainder of its
 * divisor, with every operation the run works out on the way (a narrowing) holding at it.
 *
 * <p>The others are of two kinds. A number nothing else holds is chosen too, at nought, so the
 * form is worked out the way the program works it out with it not there; every other number is
 * what the claim is about, and takes each value its type and the run leave it. A narrowing of
 * those numbers alone is a premise: it keeps rows away, and the claim is the narrower for it. A
 * narrowing that names the pivot or a number chosen is an obligation, which the choice meets
 * where it is held, and which comes out of the way with the statements it was for.
 */
final class RemainderCoverage {

    private RemainderCoverage() {}

    /** A number of the form other than the pivot, and the values its type and the run leave it. */
    record Other(WholeEnds ends, boolean chosenAtNought) {}

    /**
     * What the choice shows: for every value of {@code universal}, the others are chosen so that
     * {@code narrowingsMet} hold. They are the only narrowings a reader may leave out.
     */
    record Proof(Set<NumericTerm> universal, List<TakenConstraint.Affine> narrowingsMet) {}

    /**
     * What choosing {@code pivot} shows of the statements, or empty where it shows nothing.
     *
     * @param dividend  the form the statements hold to a remainder, without its constant
     * @param moves     the constant each statement moves the form by
     * @param divisor   the divisor the remainder is of
     * @param narrowing what the run narrows on the way to the relation
     * @param least     the least whole number the form is worked out inside
     * @param greatest  the greatest
     */
    static Optional<Proof> prove(NumericTerm pivot, WholeEnds pivotEnds,
                                 Map<NumericTerm, Other> others, LinearForm<NumericTerm> dividend,
                                 List<BigInteger> moves, BigInteger divisor,
                                 List<TakenConstraint> narrowing, BigInteger least,
                                 BigInteger greatest) {
        // A pivot weighing more than one steps the form by more than one, and the values of it in
        // the window are as many as the window is wide only for some remainders of the rest: it
        // is not asked.
        BigInteger weight = UndividedByARelation.wholeNumberOf(dividend.coefs().get(pivot));
        if (weight == null || weight.abs().compareTo(BigInteger.ONE) != 0 || moves.isEmpty()) {
            return Optional.empty();
        }
        BigInteger rest = moves.stream().reduce(BigInteger::min).orElseThrow();
        BigInteger spread = moves.stream().reduce(BigInteger::max).orElseThrow().subtract(rest);
        Map<NumericTerm, WholeEnds> universal = new LinkedHashMap<>();
        Set<NumericTerm> atNought = new LinkedHashSet<>();
        for (Map.Entry<NumericTerm, Other> each : others.entrySet()) {
            WholeEnds ends = each.getValue().ends();
            if (each.getValue().chosenAtNought()) {
                if ((ends.low() != null && ends.low().signum() > 0)
                        || (ends.high() != null && ends.high().signum() < 0)) {
                    return Optional.empty();
                }
                atNought.add(each.getKey());
            } else if (ends.low() == null || ends.high() == null) {
                return Optional.empty();
            } else {
                universal.put(each.getKey(), ends);
            }
        }
        Form form = new Form(pivot, dividend, universal.keySet(), atNought);
        BigInteger[] sum = form.universalSum(universal);
        if (sum == null) {
            return Optional.empty();
        }
        BigInteger[] range = form.tightened(narrowing, sum);
        if (range == null) {
            return Optional.empty();
        }
        WholeEnds ends = form.pivotWithin(narrowing, pivotEnds);
        // The form without its constant lies where the program works it out: inside the type as
        // the statements state it, and inside each end the run narrows it to.
        List<TakenConstraint.Affine> met = new ArrayList<>();
        BigInteger[] formRange = form.formWithin(narrowing, universal, new BigInteger[] {
                least.subtract(rest), greatest.subtract(spread).subtract(rest)}, met);
        if (ends == null || formRange == null
                || !UndividedByARelation.windowHoldsEveryRemainder(weight, ends,
                        range[0].add(rest), range[1].add(rest), spread, divisor,
                        formRange[0].add(rest), formRange[1].add(rest).add(spread))) {
            return Optional.empty();
        }
        return Optional.of(new Proof(universal.keySet(), met));
    }

    /** The form's numbers sorted by what is done with them. */
    private record Form(NumericTerm pivot, LinearForm<NumericTerm> dividend,
                        Set<NumericTerm> universal, Set<NumericTerm> atNought) {

        private BigInteger weightOf(NumericTerm term) {
            return UndividedByARelation.wholeNumberOf(dividend.coefs().get(term));
        }

        /** The least and the greatest the universal numbers weigh together, or null. */
        BigInteger[] universalSum(Map<NumericTerm, WholeEnds> ends) {
            BigInteger low = BigInteger.ZERO;
            BigInteger high = BigInteger.ZERO;
            for (Map.Entry<NumericTerm, WholeEnds> each : ends.entrySet()) {
                BigInteger by = weightOf(each.getKey());
                if (by == null) {
                    return null;
                }
                low = low.add(by.signum() >= 0 ? by.multiply(each.getValue().low())
                        : by.multiply(each.getValue().high()));
                high = high.add(by.signum() >= 0 ? by.multiply(each.getValue().high())
                        : by.multiply(each.getValue().low()));
            }
            return new BigInteger[] {low, high};
        }

        /**
         * {@code sum} narrowed by the narrowings of the universal numbers alone that hold the
         * form they weigh together between two ends: a premise, which keeps rows away and so
         * leaves the claim narrower. Any other narrowing of them says nothing here. Null where the
         * premises leave no sum.
         */
        BigInteger[] tightened(List<TakenConstraint> narrowing, BigInteger[] sum) {
            BigInteger low = sum[0];
            BigInteger high = sum[1];
            for (TakenConstraint each : narrowing) {
                if (!(each instanceof TakenConstraint.Affine affine) || universal.isEmpty()
                        || !affine.form().coefs().keySet().equals(universal)
                        || (affine.rel() != Rel.LE && affine.rel() != Rel.GE)) {
                    continue;
                }
                BigInteger lambda = ratioToTheDividend(affine.form(), universal);
                BigInteger constant = UndividedByARelation.wholeNumberOf(affine.form().constant());
                if (lambda == null || constant == null) {
                    continue;
                }
                boolean upper = (affine.rel() == Rel.LE) == (lambda.signum() > 0);
                BigInteger bound = lambda.signum() > 0 ? constant.negate() : constant;
                if (upper) {
                    high = high.min(bound);
                } else {
                    low = low.max(bound);
                }
            }
            return low.compareTo(high) > 0 ? null : new BigInteger[] {low, high};
        }

        /**
         * {@code form} as the dividend over {@code terms} scaled by one or by minus one, which
         * is that scale, or null where it is another form of them.
         */
        BigInteger ratioToTheDividend(LinearForm<NumericTerm> form, Set<NumericTerm> terms) {
            BigInteger lambda = null;
            for (NumericTerm term : terms) {
                BigInteger onTerm = UndividedByARelation.wholeNumberOf(form.coefs().get(term));
                BigInteger inDividend = weightOf(term);
                if (onTerm == null || inDividend == null || inDividend.signum() == 0) {
                    return null;
                }
                BigInteger[] divided = onTerm.divideAndRemainder(inDividend);
                if (divided[1].signum() != 0 || divided[0].abs().compareTo(BigInteger.ONE) != 0
                        || (lambda != null && !lambda.equals(divided[0]))) {
                    return null;
                }
                lambda = divided[0];
            }
            return lambda;
        }

        /**
         * The pivot's ends narrowed by what the run narrows of it and the numbers chosen at
         * nought alone: those hold wherever the pivot is put within what is left.
         */
        WholeEnds pivotWithin(List<TakenConstraint> narrowing, WholeEnds ends) {
            BigInteger low = ends.low();
            BigInteger high = ends.high();
            for (TakenConstraint each : narrowing) {
                if (!(each instanceof TakenConstraint.Affine(var form, var rel, var _))
                        || !form.coefs().containsKey(pivot)
                        || form.coefs().keySet().stream().anyMatch(term ->
                                !term.equals(pivot) && !atNought.contains(term))) {
                    continue;
                }
                BigInteger by = UndividedByARelation.wholeNumberOf(form.coefs().get(pivot));
                BigInteger constant = UndividedByARelation.wholeNumberOf(form.constant());
                if (by == null || constant == null || by.abs().compareTo(BigInteger.ONE) != 0
                        || (rel != Rel.LE && rel != Rel.GE)) {
                    return null;
                }
                // by * pivot + constant (rel) 0.
                boolean upper = (rel == Rel.LE) == (by.signum() > 0);
                BigInteger bound = by.signum() > 0 ? constant.negate() : constant;
                if (upper) {
                    high = high == null ? bound : high.min(bound);
                } else {
                    low = low == null ? bound : low.max(bound);
                }
            }
            return low != null && high != null && low.compareTo(high) > 0 ? null
                    : new WholeEnds(low, high);
        }

        /**
         * {@code formRange}, the least and the greatest the form without its constant may come
         * to, narrowed by what the run narrows that names a number chosen, those added to
         * {@code met} — or null where one is a thing this does not look at.
         *
         * <p>One of the pivot and the numbers at nought alone is in the pivot's ends
         * ({@link #pivotWithin}). One of the form whole is an end on the form: it narrows where
         * the form may lie, and so where the pivot is put. One of the numbers at nought and the
         * universal numbers holds for every value of those, with the ones at nought at nought. A
         * prefix of the form, the pivot with some of the universal numbers as the program adds
         * them, is not a thing this looks at.
         */
        BigInteger[] formWithin(List<TakenConstraint> narrowing,
                                Map<NumericTerm, WholeEnds> ends, BigInteger[] formRange,
                                List<TakenConstraint.Affine> met) {
            BigInteger low = formRange[0];
            BigInteger high = formRange[1];
            for (TakenConstraint each : narrowing) {
                if (each.terms().stream().noneMatch(term -> term.equals(pivot)
                        || atNought.contains(term))) {
                    continue;
                }
                if (!(each instanceof TakenConstraint.Affine(var form, var rel, var _))
                        || form.coefs().keySet().stream().anyMatch(term ->
                                !term.equals(pivot) && !atNought.contains(term)
                                        && !universal.contains(term))) {
                    return null;
                }
                BigInteger constant = UndividedByARelation.wholeNumberOf(form.constant());
                if (constant == null) {
                    return null;
                }
                if (!form.coefs().containsKey(pivot)) {
                    BigInteger[] range = new BigInteger[] {constant, constant};
                    for (NumericTerm term : universal) {
                        BigInteger by = form.coefs().containsKey(term)
                                ? UndividedByARelation.wholeNumberOf(form.coefs().get(term))
                                : BigInteger.ZERO;
                        WholeEnds at = ends.get(term);
                        if (by == null) {
                            return null;
                        }
                        range[0] = range[0].add(by.signum() >= 0 ? by.multiply(at.low())
                                : by.multiply(at.high()));
                        range[1] = range[1].add(by.signum() >= 0 ? by.multiply(at.high())
                                : by.multiply(at.low()));
                    }
                    if (!holdsEverywhere(range[0], range[1], rel)) {
                        return null;
                    }
                } else if (form.coefs().keySet().stream().anyMatch(universal::contains)) {
                    Set<NumericTerm> shape = new LinkedHashSet<>(universal);
                    shape.add(pivot);
                    BigInteger lambda = form.coefs().keySet().containsAll(shape)
                            && (rel == Rel.LE || rel == Rel.GE)
                            ? ratioToTheDividend(form, shape) : null;
                    if (lambda == null) {
                        return null;
                    }
                    // lambda * form + constant (rel) 0, as an end on the form.
                    boolean upper = (rel == Rel.LE) == (lambda.signum() > 0);
                    BigInteger bound = lambda.signum() > 0 ? constant.negate() : constant;
                    if (upper) {
                        high = high.min(bound);
                    } else {
                        low = low.max(bound);
                    }
                }
                met.add((TakenConstraint.Affine) each);
            }
            return low.compareTo(high) > 0 ? null : new BigInteger[] {low, high};
        }
    }

    /** Whether {@code value} held as {@code rel} against nought holds over all of
     *  {@code [low, high]}. */
    static boolean holdsEverywhere(BigInteger low, BigInteger high, Rel rel) {
        return switch (rel) {
            case GE -> low.signum() >= 0;
            case GT -> low.signum() > 0;
            case LE -> high.signum() <= 0;
            case LT -> high.signum() < 0;
            case EQ -> low.signum() == 0 && high.signum() == 0;
            case NE -> low.signum() > 0 || high.signum() < 0;
        };
    }
}
