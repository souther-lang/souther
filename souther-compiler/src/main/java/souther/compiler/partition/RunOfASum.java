package souther.compiler.partition;

import souther.compiler.partition.UndividedByARelation.WholeEnds;

import java.math.BigInteger;
import java.util.List;
import java.util.Optional;

/**
 * The values one number takes in some row, where a sum of it and others is held between two ends,
 * each of them weighed one or minus one and each lying between its own ends.
 *
 * <p>A value {@code v} is taken where the others can sum to what brings the sum into
 * {@code [from, to]}: {@code [from - w, to - w]} meets {@code [least, greatest]} for
 * {@code w = weight * v}, where {@code least} and {@code greatest} are what the others weigh to
 * at the least and at the greatest. Each other being weighed one, the sums they can take are every
 * whole number between those, so meeting is the whole condition: {@code from <= to},
 * {@code from - greatest <= w} and {@code w <= to - least}.
 *
 * <p>This is a claim of the one number: every value of the interval it gives is taken in some row,
 * and no other is. It says nothing of the number together with another.
 */
final class RunOfASum {

    /** A number the sum holds with the one asked of, weighed by {@code weight}. */
    record Other(WholeEnds ends, BigInteger weight) {}

    private RunOfASum() {
    }

    /**
     * The values {@code mine} may take that some row takes, or empty where none is or the claim is
     * not made: an end of a number that is missing, a weight that is not one or minus one, or ends
     * {@code from} and {@code to} that no sum lies between. A null {@code from} or {@code to} is
     * an end the run does not narrow.
     */
    static Optional<WholeEnds> of(WholeEnds mine, BigInteger weight, List<Other> others,
                                  BigInteger from, BigInteger to) {
        if (mine == null || mine.low() == null || mine.high() == null || !isOne(weight)
                || (from != null && to != null && from.compareTo(to) > 0)) {
            return Optional.empty();
        }
        BigInteger least = BigInteger.ZERO;
        BigInteger greatest = BigInteger.ZERO;
        for (Other each : others) {
            WholeEnds ends = each.ends();
            if (ends == null || ends.low() == null || ends.high() == null
                    || !isOne(each.weight())) {
                return Optional.empty();
            }
            boolean added = each.weight().signum() > 0;
            least = least.add(added ? ends.low() : ends.high().negate());
            greatest = greatest.add(added ? ends.high() : ends.low().negate());
        }
        BigInteger weighedLow = from == null ? null : from.subtract(greatest);
        BigInteger weighedHigh = to == null ? null : to.subtract(least);
        boolean positive = weight.signum() > 0;
        BigInteger lowest = positive ? weighedLow : weighedHigh == null ? null : weighedHigh.negate();
        BigInteger highest = positive ? weighedHigh : weighedLow == null ? null : weighedLow.negate();
        BigInteger low = lowest == null ? mine.low() : mine.low().max(lowest);
        BigInteger high = highest == null ? mine.high() : mine.high().min(highest);
        return low.compareTo(high) > 0 ? Optional.empty() : Optional.of(new WholeEnds(low, high));
    }

    private static boolean isOne(BigInteger weight) {
        return weight != null && weight.abs().equals(BigInteger.ONE);
    }
}
