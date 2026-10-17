package souther.compiler.check;

import souther.compiler.core.Core;
import souther.compiler.numeric.OrderedInterval;
import souther.compiler.numeric.Rel;
import souther.compiler.types.Type;

import java.math.BigInteger;
import java.util.Objects;

/**
 * A comparison of a number rounded to a whole one, read as what it states of the number before it
 * was rounded.
 *
 * <p>The rounded number is a step of what was rounded, so it is no form of it and no reading of its
 * answer is arithmetic over it. What a comparison of it with a whole number states is exact all the
 * same: a line on the number before rounding, where the way of rounding puts it
 * ({@link WholeRounding}). {@code Rational.toInt(DOWN, x / 2) >= 100} is {@code x / 2 >= 100}, and
 * {@code Rational.toInt(HALF_UP, x / 2) >= 100} is {@code x / 2 >= 99.5}.
 *
 * <p><b>The way of rounding is a value.</b> The policy is read as any value is, through the names it
 * was given under, in the environment the comparison is read in, and the comparison is read only
 * where it is one case of the policy there. A policy chosen by the run is one case on each path the
 * walk reads to it; one that is no case where it is read has no one line, and is left unread rather
 * than taken as any of them.
 *
 * <p><b>The rounded number is an Int.</b> A rounding past the ends of one aborts, so a row that
 * reaches the comparison has a rounded number inside them, and a whole number past them is settled
 * by them.
 */
public final class RoundedToAWholeNumber {

    private RoundedToAWholeNumber() {}

    /**
     * What a comparison of a rounded number states of the number before rounding.
     *
     * @param <E> the environment the number is read in
     * @param rounded the number before rounding
     * @param at where the rounding was applied, which is where {@code rounded} is read
     * @param statement what holds of {@code rounded} exactly where the comparison holds
     */
    public record Read<E>(Core rounded, E at, ConstantComparison statement) {

        public Read {
            Objects.requireNonNull(rounded, "a number is rounded");
            Objects.requireNonNull(at, "read somewhere");
            Objects.requireNonNull(statement, "and the comparison states something of it");
        }
    }

    /**
     * What {@code comparison}, read in {@code at}, states of the number one of its sides rounds — or
     * null where neither side is such a rounding, its policy is no one case where it is read, or the
     * other side is no whole number the same on every run.
     */
    public static <E> Read<E> read(StatedComparison comparison, E at,
                                   TheSignOfAnOrder.Sides<E> sides) {
        ACallAgainstANumber<E, BoundOperationFact.RoundsToAWholeNumber> rounding =
                ACallAgainstANumber.of(comparison, at, sides,
                        DefaultBoundOperationFacts.get()::roundsToAWholeNumber);
        BigInteger whole = rounding == null ? null : rounding.whole();
        if (whole == null) {
            return null;
        }
        BoundOperationFact.RoundsToAWholeNumber rounds = rounding.fact();
        Core value = rounding.applied().argument(rounds.value());
        Core policy = rounding.applied().argument(rounds.mode());
        WholeRounding way = policy == null ? null
                : rounds.wayOf(sides.standing(policy, rounding.at()).value());
        if (value == null || way == null) {
            return null;
        }
        // What is rounded to is an Int, which is what the fact was held to where it was bound.
        OrderedInterval ends = Carrier.ofValue(Type.INT, sides.declarations()).extent();
        BigInteger least = WholeUnitsBetween.wholeNumberOf(ends.low());
        BigInteger most = WholeUnitsBetween.wholeNumberOf(ends.high());
        return least == null || most == null ? null : new Read<>(value, rounding.at(),
                statementOf(way, rounding.written(), whole, least, most));
    }

    /**
     * What the number before rounding stands to where its rounding by {@code way} stands
     * {@code rel} to {@code k}, for a rounded number from {@code least} to {@code most}.
     */
    static ConstantComparison statementOf(WholeRounding way, Rel rel, BigInteger k,
                                          BigInteger least, BigInteger most) {
        return ConstantComparison.ofAWholeNumber(rel, k, n -> atLeast(way, n, least, most));
    }

    /**
     * What holds of the number before rounding exactly where its rounding by {@code way} is at least
     * {@code k}, for a rounded number from {@code least} to {@code most}.
     */
    private static ConstantComparison atLeast(WholeRounding way, BigInteger k, BigInteger least,
                                              BigInteger most) {
        ConstantComparison rounded = ConstantComparison.of(Rel.GE, k, least, most);
        return rounded instanceof ConstantComparison.Against ? way.atLeast(k) : rounded;
    }
}
