package souther.compiler.partition;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.regex.PatternPlan;
import souther.compiler.values.TextExtents;
import souther.compiler.values.ValueSet;
import souther.compiler.values.ValuesWithin;

import net.unit8.notation199x.pattern.PatternMeaning;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;

/**
 * The lengths a string can have where some run gets past everything its way states and works out,
 * when what ties the length to other numbers is a set of statements of whole numbers.
 *
 * <p>The way states {@code length + n > 0} and the sum it works out must stay within the type:
 * for each length there may be an {@code n} that meets both, and the lengths with none are the
 * strings no run carries to the comparison. The numbers other than the length are taken out one at
 * a time, each between the ends its declarations leave it, by adding every statement that bounds it
 * from below to every statement that bounds it from above. That is exact for whole numbers where the
 * number being taken out has a weight of one or minus one in every statement it is in, since then
 * the lengths that leave it a whole number between the largest lower bound and the smallest upper
 * one are those where every lower bound is at most every upper bound; with a larger weight the
 * between may hold no whole number, and nothing is said.
 *
 * <p>What comes back is a proof and not a bound: a length in it has a whole number for every other
 * number, chosen between the ends declared for each, and a length outside it has none.
 */
final class LengthsPastTheWay {

    /** The most statements held at once, which taking numbers out multiplies. */
    private static final int MOST_ROWS = 256;

    private LengthsPastTheWay() { }

    /**
     * The whole numbers from {@code least} to {@code most}, either null where nothing bounds the
     * lengths there.
     */
    record Lengths(BigInteger least, BigInteger most) {

        /** Whether no length is between the ends. */
        boolean isEmpty() {
            return least != null && most != null && least.compareTo(most) > 0;
        }

        /** Whether every whole number from {@code from} to {@code to} is among these. */
        boolean holds(BigInteger from, BigInteger to) {
            return (least == null || least.compareTo(from) <= 0)
                    && (most == null || most.compareTo(to) >= 0);
        }

        /**
         * The strings of these lengths, or null where the ends are past what a pattern counts.
         * Lengths are counted in code points.
         */
        PatternPlan strings() {
            BigInteger from = least == null ? BigInteger.ZERO : least.max(BigInteger.ZERO);
            if (from.bitLength() >= Integer.SIZE - 1) {
                return null;
            }
            return PatternPlan.of(PatternMeaning.ofAnySymbols(from.intValueExact(), ceiling(most)));
        }

        /**
         * The strings of every other length, or null where there are none or the ends are past
         * what a pattern counts.
         */
        PatternPlan stringsOutside() {
            PatternPlan below = null;
            if (least != null && least.signum() > 0) {
                if (least.bitLength() >= Integer.SIZE - 1) {
                    return null;
                }
                below = PatternPlan.of(PatternMeaning.ofAnySymbols(0, least.intValueExact() - 1));
            }
            PatternPlan above = null;
            if (most != null && most.signum() >= 0 && most.bitLength() < Integer.SIZE - 1) {
                above = PatternPlan.of(PatternMeaning.ofAnySymbols(most.intValueExact() + 1,
                        PatternMeaning.Repeated.NO_CEILING));
            }
            return below == null ? above : above == null ? below : below.or(above);
        }

        /**
         * The strings of every other length, each as long as it is left open at: those short of
         * the least of these, and those longer than the most.
         */
        List<ValuesWithin> outside() {
            List<ValuesWithin> out = new ArrayList<>();
            if (least != null && least.signum() > 0 && least.bitLength() < Long.SIZE - 1) {
                out.add(new ValuesWithin(ValueSet.ANY, 0, least.longValueExact() - 1));
            }
            if (most != null && most.signum() >= 0
                    && most.compareTo(BigInteger.valueOf(TextExtents.LONGEST_STRING)) < 0) {
                out.add(ValuesWithin.longerThan(ValueSet.ANY, most.longValueExact()));
            }
            return out;
        }

        private static int ceiling(BigInteger most) {
            return most == null || most.bitLength() >= Integer.SIZE - 1
                    ? PatternMeaning.Repeated.NO_CEILING : most.intValueExact();
        }
    }

    /**
     * The ends a number other than the length can be held at, either null where nothing bounds it
     * there. Whole numbers: a number that is not one is not asked.
     */
    record Ends(BigInteger least, BigInteger greatest) { }

    /**
     * One statement {@code Σ weight·number + constant >= 0} of whole numbers.
     */
    private record Inequality(Map<NumericTerm, BigInteger> weights, BigInteger constant) {

        BigInteger weightOf(NumericTerm number) {
            return weights.getOrDefault(number, BigInteger.ZERO);
        }

        Inequality plus(Inequality other) {
            Map<NumericTerm, BigInteger> sum = new LinkedHashMap<>(weights);
            other.weights.forEach((number, weight) -> sum.merge(number, weight, BigInteger::add));
            sum.values().removeIf(weight -> weight.signum() == 0);
            return new Inequality(sum, constant.add(other.constant));
        }
    }

    /**
     * The lengths at which {@code length} has, for every other number {@code system} names, a whole
     * number between the ends {@code endsOf} gives it that meets all of {@code system} — or null
     * where that is not worked out: a statement that is not of whole numbers or holds a number
     * apart, a number {@code endsOf} gives no ends, or one the elimination is not exact for.
     *
     * @param length the number of the string's length
     * @param system the statements the run to the comparison meets
     * @param endsOf the ends each other number is held at by what the declarations leave it, or
     *               null where it is not a whole number held to nothing beside the others
     */
    static Lengths of(NumericTerm length, List<TakenConstraint> system,
                      Function<NumericTerm, Ends> endsOf) {
        List<Inequality> inequalities = new ArrayList<>();
        Set<NumericTerm> others = new LinkedHashSet<>();
        for (TakenConstraint each : system) {
            if (!(each instanceof TakenConstraint.Affine(LinearForm<NumericTerm> form,
                    var rel))) {
                return null;
            }
            Inequality inequality = inequalityOf(form);
            if (inequality == null) {
                return null;
            }
            switch (rel) {
                case GE -> inequalities.add(inequality);
                case GT -> inequalities.add(inequality.plus(constant(-1)));
                case LE -> inequalities.add(negated(inequality));
                case LT -> inequalities.add(negated(inequality).plus(constant(-1)));
                case EQ -> {
                    inequalities.add(inequality);
                    inequalities.add(negated(inequality));
                }
                case NE -> {
                    return null;
                }
            }
            inequality.weights().keySet().stream().filter(number -> !number.equals(length))
                    .forEach(others::add);
        }
        for (NumericTerm number : others) {
            Ends ends = endsOf.apply(number);
            if (ends == null) {
                return null;
            }
            if (ends.least() != null) {
                inequalities.add(new Inequality(Map.of(number, BigInteger.ONE), ends.least().negate()));
            }
            if (ends.greatest() != null) {
                inequalities.add(new Inequality(Map.of(number, BigInteger.ONE.negate()), ends.greatest()));
            }
        }
        for (NumericTerm number : others) {
            inequalities = takenOut(inequalities, number);
            if (inequalities == null) {
                return null;
            }
        }
        return lengthsOf(inequalities, length);
    }

    /** {@code inequalities} without {@code number}, or null where that is not exact or too large. */
    private static List<Inequality> takenOut(List<Inequality> inequalities, NumericTerm number) {
        List<Inequality> below = new ArrayList<>();
        List<Inequality> above = new ArrayList<>();
        List<Inequality> out = new ArrayList<>();
        for (Inequality each : inequalities) {
            BigInteger weight = each.weightOf(number);
            if (weight.signum() == 0) {
                out.add(each);
            } else if (weight.abs().equals(BigInteger.ONE)) {
                (weight.signum() > 0 ? below : above).add(each);
            } else {
                return null;
            }
        }
        for (Inequality lower : below) {
            for (Inequality upper : above) {
                out.add(lower.plus(upper));
                if (out.size() > MOST_ROWS) {
                    return null;
                }
            }
        }
        return out;
    }

    /** The lengths the statements left on {@code length} alone allow. */
    private static Lengths lengthsOf(List<Inequality> inequalities, NumericTerm length) {
        BigInteger least = null;
        BigInteger most = null;
        for (Inequality each : inequalities) {
            BigInteger weight = each.weightOf(length);
            if (weight.signum() == 0) {
                if (each.constant().signum() < 0) {
                    return new Lengths(BigInteger.ONE, BigInteger.ZERO);
                }
            } else if (weight.signum() > 0) {
                BigInteger from = UndividedByARelation.ceilingOf(each.constant().negate(), weight);
                least = least == null ? from : least.max(from);
            } else {
                BigInteger to = UndividedByARelation.floorOf(each.constant(), weight.negate());
                most = most == null ? to : most.min(to);
            }
        }
        return new Lengths(least, most);
    }

    /** {@code form} as an inequality, or null where a weight or the constant is no whole number. */
    private static Inequality inequalityOf(LinearForm<NumericTerm> form) {
        BigInteger constant = UndividedByARelation.wholeOf(form.constant());
        if (constant == null) {
            return null;
        }
        Map<NumericTerm, BigInteger> weights = new LinkedHashMap<>();
        for (Map.Entry<NumericTerm, ExactRatio> each : form.coefs().entrySet()) {
            BigInteger weight = UndividedByARelation.wholeOf(each.getValue());
            if (weight == null) {
                return null;
            }
            weights.put(each.getKey(), weight);
        }
        return new Inequality(weights, constant);
    }

    private static Inequality constant(long value) {
        return new Inequality(Map.of(), BigInteger.valueOf(value));
    }

    private static Inequality negated(Inequality inequality) {
        Map<NumericTerm, BigInteger> weights = new LinkedHashMap<>();
        inequality.weights().forEach((number, weight) -> weights.put(number, weight.negate()));
        return new Inequality(weights, inequality.constant().negate());
    }

}
