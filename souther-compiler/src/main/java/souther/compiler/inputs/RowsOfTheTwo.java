package souther.compiler.inputs;

import souther.compiler.inputs.WhatARelationLeavesUndivided.IntSum;
import souther.compiler.inputs.WhatARelationLeavesUndivided.Operations;
import souther.compiler.numeric.ExactRatio;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;

/**
 * Where the rows of two terms are computed, read off the operations the program works out and
 * nothing else.
 *
 * <p>With every operation told ({@link WhatARelationLeavesUndivided.Told#EVERY}) a row is
 * computed where each operation comes to a number its type holds. Put the third terms at the
 * values they are held at, and each operation is a condition
 * {@code low <= onAsked * x + onPartner * y <= high} on the two whole numbers {@code x}, the term
 * asked of, and {@code y}, its partner. The values of {@code x} that some {@code y} computes
 * with are then found exactly: a condition reads {@code y} with a coefficient of nought, one or
 * minus one, so it bounds {@code y} between two whole-numbered functions of {@code x}, and a whole
 * {@code y} lies between the greatest of the lower bounds and the least of the upper ones where
 * each lower bound is at or below each upper one, which is a condition on {@code x} alone.
 *
 * <p>The operations are not the form's addends: a constant the program only compares the sum
 * with is in none of them, and a sum of terms weighed one is worked out at the least value of the
 * type, which no addend is. So nothing here reads the sizes of the form.
 *
 * <p>Built only where that holds, otherwise null ({@link #of}); a caller that has none keeps to
 * what it could say without the operations.
 */
final class RowsOfTheTwo {

    /** The whole numbers from {@code low} to {@code high}, each end inclusive, null where
     *  nothing bounds that side. */
    record Span(BigInteger low, BigInteger high) {

        static final Span ANY = new Span(null, null);

        boolean isEmpty() {
            return low != null && high != null && low.compareTo(high) > 0;
        }

        Span meet(Span other) {
            BigInteger lower = low == null ? other.low
                    : other.low == null ? low : low.max(other.low);
            BigInteger upper = high == null ? other.high
                    : other.high == null ? high : high.min(other.high);
            return new Span(lower, upper);
        }
    }

    /**
     * How the partner is written in a variable {@code z} that is not itself: {@code y} is
     * {@code onAsked * x + onFree * z}, with {@code onFree} one or minus one.
     */
    record Frame(int onAsked, int onFree) {

        /** The partner itself. */
        static final Frame THE_PARTNER = new Frame(0, 1);

        /** The partner of a sum of the two: {@code y = z - x}. */
        static final Frame OF_THE_SUM = new Frame(-1, 1);

        /** The partner of a difference of the first less the second, the asked being the first:
         *  {@code y = x - z}. */
        static final Frame FROM_ABOVE = new Frame(1, -1);

        /** The same, the asked being the second: {@code y = x + z}. */
        static final Frame FROM_BELOW = new Frame(1, 1);
    }

    /** {@code low <= onAsked * x + onPartner * y <= high}: one operation with the terms held
     *  still put in. */
    private record Operation(BigInteger onAsked, BigInteger onPartner, BigInteger low,
                             BigInteger high) {}

    /** {@code low <= onX * x + onZ * z <= high}, an end null where nothing bounds it. */
    private record Condition(BigInteger onX, BigInteger onZ, BigInteger low, BigInteger high) {}

    /** {@code onX * x + constant}. */
    private record Line(BigInteger onX, BigInteger constant) {}

    private final List<Operation> operations;

    private RowsOfTheTwo(List<Operation> operations) {
        this.operations = operations;
    }

    /**
     * The rows of the operations, or null where they cannot be read exactly: not every operation
     * is told, one is of decimals, none is there to read, or one weighs a term other than the two
     * and those held still, weighs the partner other than by nought, one or minus one, or comes
     * to a number that is not whole at the values the others are held at.
     *
     * @param asked    the key of the term whose values are asked of ({@link
     *                 WhatARelationLeavesUndivided.Term#key})
     * @param partner  the key of the term beside it
     * @param standing the values of the terms held still, by key
     */
    static RowsOfTheTwo of(Operations operations, Object asked, Object partner,
                           Map<Object, ExactRatio> standing) {
        if (operations.told() != WhatARelationLeavesUndivided.Told.EVERY
                || !operations.decimals().isEmpty() || operations.sums().isEmpty()
                || asked == null || partner == null || asked.equals(partner)) {
            return null;
        }
        List<Operation> read = new ArrayList<>();
        for (IntSum each : operations.sums()) {
            Operation operation = read(each, asked, partner, standing);
            if (operation == null) {
                return null;
            }
            read.add(operation);
        }
        return new RowsOfTheTwo(List.copyOf(read));
    }

    private static Operation read(IntSum sum, Object asked, Object partner,
                                  Map<Object, ExactRatio> standing) {
        ExactRatio constant = sum.constant();
        BigInteger onAsked = BigInteger.ZERO;
        BigInteger onPartner = BigInteger.ZERO;
        for (Map.Entry<Object, ExactRatio> each : sum.coefs().entrySet()) {
            if (each.getKey().equals(asked)) {
                onAsked = whole(each.getValue());
            } else if (each.getKey().equals(partner)) {
                onPartner = whole(each.getValue());
            } else {
                ExactRatio value = standing.get(each.getKey());
                constant = value == null ? null
                        : value.times(each.getValue()).flatMap(constant::plus).orNull();
            }
            if (constant == null || onAsked == null || onPartner == null) {
                return null;
            }
        }
        BigInteger put = whole(constant);
        if (put == null || onPartner.abs().compareTo(BigInteger.ONE) > 0) {
            return null;
        }
        return new Operation(onAsked, onPartner, sum.least().subtract(put),
                sum.greatest().subtract(put));
    }

    private static BigInteger whole(ExactRatio number) {
        return number.isWhole() ? number.floor().orNull() : null;
    }

    /**
     * The values of {@code x} at which some whole {@code z} in {@code free} makes the partner,
     * written in {@code frame}, a number in {@code partner} and every operation come to a number
     * its type holds.
     *
     * @param partner where the partner lies, or null where it may lie anywhere
     */
    Span askedWhere(Frame frame, Span free, Span partner) {
        List<Condition> conditions = new ArrayList<>();
        for (Operation each : operations) {
            conditions.add(substituted(each.onAsked(), each.onPartner(), each.low(), each.high(),
                    frame));
        }
        conditions.add(new Condition(BigInteger.ZERO, BigInteger.ONE, free.low(), free.high()));
        if (partner != null) {
            conditions.add(substituted(BigInteger.ZERO, BigInteger.ONE, partner.low(),
                    partner.high(), frame));
        }
        return solved(conditions);
    }

    /**
     * The values of the partner within {@code partner} that every operation comes to a number its
     * type holds with, the term asked of standing at {@code x}.
     */
    Span partnersAt(BigInteger x, Span partner) {
        Span out = partner;
        for (Operation each : operations) {
            BigInteger moved = each.onAsked().multiply(x);
            BigInteger low = each.low().subtract(moved);
            BigInteger high = each.high().subtract(moved);
            Span here = switch (each.onPartner().signum()) {
                case 0 -> low.signum() <= 0 && high.signum() >= 0 ? Span.ANY
                        : new Span(BigInteger.ONE, BigInteger.ZERO);
                case 1 -> new Span(low, high);
                default -> new Span(high.negate(), low.negate());
            };
            out = out.meet(here);
        }
        return out;
    }

    private static Condition substituted(BigInteger onAsked, BigInteger onPartner,
                                         BigInteger low, BigInteger high, Frame frame) {
        return new Condition(onAsked.add(onPartner.multiply(BigInteger.valueOf(frame.onAsked()))),
                onPartner.multiply(BigInteger.valueOf(frame.onFree())), low, high);
    }

    /** The values of {@code x} some whole {@code z} satisfies every condition at. */
    private static Span solved(List<Condition> conditions) {
        List<Line> lowers = new ArrayList<>();
        List<Line> uppers = new ArrayList<>();
        Span x = Span.ANY;
        for (Condition each : conditions) {
            switch (each.onZ().signum()) {
                case 0 -> x = x.meet(xAlone(each));
                case 1 -> {
                    if (each.low() != null) {
                        lowers.add(new Line(each.onX().negate(), each.low()));
                    }
                    if (each.high() != null) {
                        uppers.add(new Line(each.onX().negate(), each.high()));
                    }
                }
                default -> {
                    if (each.high() != null) {
                        lowers.add(new Line(each.onX(), each.high().negate()));
                    }
                    if (each.low() != null) {
                        uppers.add(new Line(each.onX(), each.low().negate()));
                    }
                }
            }
        }
        for (Line lower : lowers) {
            for (Line upper : uppers) {
                // lower <= upper, which is (lower.onX - upper.onX) * x <= upper.constant -
                // lower.constant.
                x = x.meet(atMost(lower.onX().subtract(upper.onX()),
                        upper.constant().subtract(lower.constant())));
            }
        }
        return x;
    }

    /** The values of {@code x} with {@code low <= onX * x <= high}. */
    private static Span xAlone(Condition condition) {
        BigInteger onX = condition.onX();
        Span fromAbove = condition.high() == null ? Span.ANY
                : atMost(onX, condition.high());
        Span fromBelow = condition.low() == null ? Span.ANY
                : atMost(onX.negate(), condition.low().negate());
        return fromAbove.meet(fromBelow);
    }

    /** The values of {@code x} with {@code by * x <= bound}. */
    private static Span atMost(BigInteger by, BigInteger bound) {
        return switch (by.signum()) {
            case 0 -> bound.signum() >= 0 ? Span.ANY : new Span(BigInteger.ONE, BigInteger.ZERO);
            case 1 -> new Span(null, floorDiv(bound, by));
            default -> new Span(floorDiv(bound, by.negate()).negate(), null);
        };
    }

    private static BigInteger floorDiv(BigInteger number, BigInteger by) {
        BigInteger[] quotientAndRemainder = number.divideAndRemainder(by);
        return quotientAndRemainder[1].signum() != 0
                && quotientAndRemainder[1].signum() != by.signum()
                ? quotientAndRemainder[0].subtract(BigInteger.ONE) : quotientAndRemainder[0];
    }
}
