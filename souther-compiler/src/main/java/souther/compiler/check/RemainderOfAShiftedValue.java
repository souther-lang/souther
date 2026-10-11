package souther.compiler.check;

import souther.compiler.core.Core;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.Rel;
import souther.compiler.types.BinOp;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;
import java.util.Objects;
import java.util.OptionalInt;

/**
 * A comparison of what a division leaves of a value that is a place moved by a number, read as a
 * comparison of what the division leaves of the place.
 *
 * <p>{@code Int.floorMod(x + 1, 7) == 0} is no number taken of {@code x}: the number taken of a
 * place is taken of what stands there, and what stands there is {@code x} and not one more. It is
 * exact all the same. Moving a value by {@code k} moves its remainder by {@code k}, round the
 * divisor, so with {@code r} the remainder of {@code x} and {@code d} the divisor, the remainder of
 * {@code x + k} is {@code r + k} below {@code d - k} and {@code r + k - d} from there — and any
 * comparison of it is the comparison of {@code r} each of those two stretches says, the one stretch
 * or the other. A value taken from a number instead, {@code k - x}, is {@code k - r} where {@code r}
 * is no more than {@code k} and {@code k - r + d} above it.
 *
 * <p>So what is handed over is a tree of comparisons of the remainder of the place itself
 * ({@link ConstantComparison}), and the reading that holds those is the reading of any remainder of
 * a place. Nothing here is a second account of a remainder: a number taken of a place is still taken
 * of the place, and what moved it is arithmetic round the call that is peeled off before the call is
 * asked.
 *
 * <p>What it reads is the arithmetic that leaves a place a place: a sum or a difference with a
 * written number, however it is spelled and however many deep, which is arithmetic the library
 * states of its operations ({@link DischargeRules#operator}). A divisor below nought is not read —
 * it answers the other side of nought and the stretches above are not its — and neither is a value
 * scaled or made of two places.
 */
public final class RemainderOfAShiftedValue {

    private RemainderOfAShiftedValue() {}

    /**
     * What a comparison states of the remainder of the place a value is moved from.
     *
     * @param <E> the environment the call is read in
     * @param remainder the call of the same operation over the place itself and the same divisor
     * @param at where the call was applied, which is where its arguments are read
     * @param statement what holds of {@code remainder} exactly where the comparison holds
     */
    public record Read<E>(Core.PreservedCall remainder, E at, ConstantComparison statement) {

        public Read {
            Objects.requireNonNull(remainder, "a remainder is of something");
            Objects.requireNonNull(at, "read somewhere");
            Objects.requireNonNull(statement, "and the comparison states something of it");
        }
    }

    /**
     * What {@code comparison}, read in {@code at}, states of the remainder of the place one of its
     * sides is the remainder of a moved value of — or null where neither side is such a remainder,
     * the other side is no whole number the same on every run, or the divisor is no number above
     * nought.
     */
    public static <E> Read<E> read(StatedComparison comparison, E at,
                                   TheSignOfAnOrder.Sides<E> sides) {
        for (boolean remainderFirst : List.of(true, false)) {
            Located<E> found = locate(comparison, at, sides, remainderFirst);
            if (found == null) {
                continue;
            }
            Moved moved = Moved.of(found.call().args().getFirst(), found.at(), sides);
            if (moved == null) {
                continue;
            }
            if (found.divisor() == null || found.against() == null
                    || found.divisor().signum() <= 0) {
                return null;
            }
            ConstantComparison statement =
                    statementOf(found.written(), found.against(), found.divisor(), moved);
            if (statement == null) {
                return null;
            }
            List<Core> over = new ArrayList<>(found.call().args());
            over.set(0, moved.place());
            Core.PreservedCall call = found.call();
            return new Read<>(new Core.PreservedCall(call.declared(), over, call.place(),
                    call.settled(), call.type(), call.pos()), found.at(), statement);
        }
        return null;
    }

    /**
     * What a comparison states of the remainder of a dividend taken whole, read as the remainder of
     * a form of the input's numbers where the dividend is no place moved by a number — or null where
     * neither side is such a remainder, the other side is no whole number the same on every run, or
     * the divisor is no number above nought.
     *
     * <p>The statement is of the remainder the call answers, between nought and one below the
     * divisor: nothing of the dividend is peeled, because what a form is moved by is the form's own
     * constant.
     *
     * @param <E> the environment the call is read in
     * @param dividend the first argument of the call, which is the form the division is of
     * @param at where the call was applied, which is where its arguments are read
     * @param divisor the number the dividend is divided by
     * @param statement what holds of the remainder exactly where the comparison holds
     */
    public record OfAForm<E>(Core dividend, E at, BigInteger divisor,
                             ConstantComparison statement) {

        public OfAForm {
            Objects.requireNonNull(dividend, "a remainder is of something");
            Objects.requireNonNull(at, "read somewhere");
            Objects.requireNonNull(divisor, "by something");
            Objects.requireNonNull(statement, "and the comparison states something of it");
        }
    }

    /** The same, of the dividend as the call has it: no moving is peeled off it. */
    public static <E> OfAForm<E> readOverAForm(StatedComparison comparison, E at,
                                                TheSignOfAnOrder.Sides<E> sides) {
        for (boolean remainderFirst : List.of(true, false)) {
            Located<E> found = locate(comparison, at, sides, remainderFirst);
            if (found == null) {
                continue;
            }
            if (found.divisor() == null || found.against() == null
                    || found.divisor().signum() <= 0) {
                return null;
            }
            ConstantComparison statement = ConstantComparison.of(found.written(), found.against(),
                    BigInteger.ZERO, found.divisor().subtract(BigInteger.ONE));
            return statement == null ? null : new OfAForm<>(found.call().args().getFirst(),
                    found.at(), found.divisor(), statement);
        }
        return null;
    }

    /**
     * The call of a floor remainder that one side of {@code comparison} is, and what the other side
     * and the divisor are as whole numbers — or null where this side is no such call.
     */
    private static <E> Located<E> locate(StatedComparison comparison, E at,
                                         TheSignOfAnOrder.Sides<E> sides,
                                         boolean remainderFirst) {
        Core spelled = remainderFirst ? comparison.left() : comparison.right();
        // The call itself and not a name given it: a guard over a bound value is a fact about
        // that value, which a path holds as the number it is, and a disjunction of stretches
        // of the place's remainder is a fact it cannot take in its place.
        if (Core.withoutStanding(spelled) instanceof Core.Read) {
            return null;
        }
        AffineForms.ReadThrough<E> side = sides.standing(spelled, at);
        if (!(Core.withoutStanding(side.value()) instanceof Core.PreservedCall call)) {
            return null;
        }
        OptionalInt divides = DefaultBoundOperationFacts.get()
                .divisorOfAFloorRemainder(call.operation());
        if (divides.isEmpty() || call.args().size() <= divides.getAsInt()) {
            return null;
        }
        BigInteger divisor =
                wholeNumberOf(sides.constant(call.args().get(divides.getAsInt()), side.at()));
        BigInteger against = wholeNumberOf(
                sides.constant(remainderFirst ? comparison.right() : comparison.left(), at));
        Rel written = (remainderFirst ? comparison.claim() : comparison.claim().turned())
                .statedRelation();
        return new Located<>(call, side.at(), divisor, against, written);
    }

    /** A floor remainder one side of a comparison is, with the numbers it is read against. */
    private record Located<E>(Core.PreservedCall call, E at, BigInteger divisor,
                              BigInteger against, Rel written) {}

    /**
     * What holds of the remainder {@code r} of the place, by {@code divisor}, where the remainder of
     * the moved value stands {@code rel} to {@code against}.
     */
    static ConstantComparison statementOf(Rel rel, BigInteger against, BigInteger divisor,
                                          Moved moved) {
        BigInteger most = divisor.subtract(BigInteger.ONE);
        BigInteger by = moved.by().mod(divisor);
        if (!moved.negated()) {
            if (by.signum() == 0) {
                return ConstantComparison.of(rel, against, BigInteger.ZERO, most);
            }
            // The remainder of the place plus `by`, which falls back round the divisor once the
            // sum reaches it: below the turn the moved remainder is `r + by`, and from it
            // `r + by - divisor`.
            BigInteger turn = divisor.subtract(by);
            return ConstantComparison.either(
                    inStretch(rel, against.subtract(by), BigInteger.ZERO,
                            turn.subtract(BigInteger.ONE), most),
                    inStretch(rel, against.subtract(by).add(divisor), turn, most, most));
        }
        // `by` less the remainder, which is no more than `by` while the remainder is, and a
        // divisor more above it. A comparison of what is taken from a number is the comparison the
        // other way round of the number it is taken from.
        return ConstantComparison.either(
                inStretch(turned(rel), by.subtract(against), BigInteger.ZERO, by, most),
                inStretch(turned(rel), by.add(divisor).subtract(against),
                        by.add(BigInteger.ONE), most, most));
    }

    /**
     * That the remainder is between {@code from} and {@code to} and stands {@code rel} to
     * {@code against}, said as little as says it.
     *
     * <p>A stretch the comparison already lies inside needs no saying — {@code r == 6} is
     * {@code r >= 6 && r == 6} — and one it cannot reach is no stretch at all. Said in full, a
     * comparison whose two halves part would be read as a conjunction of two lines, and the rows on
     * the near side of either would be rows the other half refuses: the single line it is, drawn
     * twice, owed none of the rows it was owed written without the moving.
     */
    private static ConstantComparison inStretch(Rel rel, BigInteger against, BigInteger from,
                                                BigInteger to, BigInteger most) {
        if (from.compareTo(to) > 0) {
            return new ConstantComparison.Settled(false);
        }
        // What the comparison holds of, as the runs of remainders it holds on within the range.
        List<BigInteger[]> holdsOn = new ArrayList<>();
        BigInteger below = against.subtract(BigInteger.ONE);
        BigInteger above = against.add(BigInteger.ONE);
        switch (rel) {
            case EQ -> holdsOn.add(new BigInteger[] {against, against});
            case GE -> holdsOn.add(new BigInteger[] {against, most});
            case GT -> holdsOn.add(new BigInteger[] {above, most});
            case LE -> holdsOn.add(new BigInteger[] {BigInteger.ZERO, against});
            case LT -> holdsOn.add(new BigInteger[] {BigInteger.ZERO, below});
            case NE -> {
                holdsOn.add(new BigInteger[] {BigInteger.ZERO, below});
                holdsOn.add(new BigInteger[] {above, most});
            }
        }
        boolean reaches = false;
        boolean insideAll = true;
        BigInteger covered = BigInteger.ZERO;
        for (BigInteger[] run : holdsOn) {
            BigInteger low = run[0].max(BigInteger.ZERO);
            BigInteger high = run[1].min(most);
            if (low.compareTo(high) > 0) {
                continue;
            }
            BigInteger meetLow = low.max(from);
            BigInteger meetHigh = high.min(to);
            if (meetLow.compareTo(meetHigh) <= 0) {
                reaches = true;
                covered = covered.add(meetHigh.subtract(meetLow)).add(BigInteger.ONE);
            }
            insideAll &= low.compareTo(from) >= 0 && high.compareTo(to) <= 0;
        }
        if (!reaches) {
            return new ConstantComparison.Settled(false);
        }
        ConstantComparison saying = ConstantComparison.of(rel, against, BigInteger.ZERO, most);
        if (insideAll) {
            return saying;
        }
        ConstantComparison stretch = ConstantComparison.both(
                ConstantComparison.of(Rel.GE, from, BigInteger.ZERO, most),
                ConstantComparison.of(Rel.LE, to, BigInteger.ZERO, most));
        boolean wholeStretch = covered.equals(to.subtract(from).add(BigInteger.ONE));
        return wholeStretch ? stretch : ConstantComparison.both(stretch, saying);
    }

    private static Rel turned(Rel rel) {
        return switch (rel) {
            case GE -> Rel.LE;
            case GT -> Rel.LT;
            case LE -> Rel.GE;
            case LT -> Rel.GT;
            case EQ -> Rel.EQ;
            case NE -> Rel.NE;
        };
    }

    private static BigInteger wholeNumberOf(ExactRatio number) {
        return number != null && number.isWhole()
                && number.floor() instanceof ExactAnswer.Held<BigInteger> whole
                ? whole.value() : null;
    }

    /**
     * A place moved by a number: the value is {@code by} added to the place, or {@code by} less the
     * place where {@code negated}.
     *
     * @param place the expression that is no further sum or difference with a written number
     */
    record Moved(Core place, BigInteger by, boolean negated) {

        /**
         * The place {@code value} is moved from, peeled one sum or difference at a time and kept as
         * one number moved the one way or the other — or null where {@code value} is no moved place
         * at all, which is a place or something this does not take apart.
         */
        static <E> Moved of(Core value, E at, TheSignOfAnOrder.Sides<E> sides) {
            Core place = value;
            BigInteger by = BigInteger.ZERO;
            boolean negated = false;
            boolean peeled = false;
            E here = at;
            while (true) {
                AffineForms.ReadThrough<E> through = sides.standing(place, here);
                here = through.at();
                SumOrDifference arithmetic = SumOrDifference.of(through.value());
                if (arithmetic == null) {
                    break;
                }
                BigInteger left = wholeNumberOf(sides.constant(arithmetic.left(), here));
                BigInteger right = wholeNumberOf(sides.constant(arithmetic.right(), here));
                if (left != null == (right != null)) {
                    break;
                }
                BigInteger sign = negated ? BigInteger.ONE.negate() : BigInteger.ONE;
                if (!arithmetic.subtracts()) {
                    by = by.add(sign.multiply(left != null ? left : right));
                    place = left != null ? arithmetic.right() : arithmetic.left();
                } else if (right != null) {
                    by = by.subtract(sign.multiply(right));
                    place = arithmetic.left();
                } else {
                    by = by.add(sign.multiply(left));
                    negated = !negated;
                    place = arithmetic.right();
                }
                peeled = true;
            }
            return peeled ? new Moved(place, by, negated) : null;
        }
    }

    /** A sum or a difference of two expressions, however it was written. */
    private record SumOrDifference(Core left, Core right, boolean subtracts) {

        /** The sum or difference {@code e} is, as the operator wrote it or as the library's
         *  operation that computes the same, or null where it is neither. */
        static SumOrDifference of(Core standing) {
            Core e = Core.withoutStanding(standing);
            BinOp op = e instanceof Core.Binary written ? written.op()
                    : e instanceof Core.PreservedCall call ? DischargeRules.operator(
                            call.operation()) : null;
            if (op != BinOp.ADD && op != BinOp.SUB) {
                return null;
            }
            List<Core> operands = e instanceof Core.Binary written
                    ? List.of(written.left(), written.right()) : ((Core.PreservedCall) e).args();
            return operands.size() == 2
                    ? new SumOrDifference(operands.get(0), operands.get(1), op == BinOp.SUB) : null;
        }
    }
}
