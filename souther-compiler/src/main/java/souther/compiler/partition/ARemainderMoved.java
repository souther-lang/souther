package souther.compiler.partition;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.WholeNumberRuns;

import java.math.BigInteger;
import java.util.Map;
import java.util.Optional;

/**
 * A floor remainder of a form moved by a whole number, read as the remainder of the form unmoved
 * and the number it is moved by.
 *
 * <p>{@code floorMod(f + c, m)} is {@code r} exactly where {@code floorMod(f, m)} is
 * {@code floorMod(r - c, m)}, for any {@code f} and whole {@code c}. So statements of remainders
 * of one form by one divisor, moved by whatever whole numbers, are statements of one remainder, and
 * what each leaves of another of them is what it leaves turned round the divisor by the difference
 * of the two moves.
 *
 * <p>The one place that says when two statements are of one remainder, for every reader that holds
 * one against another: what the way leaves of a remainder a row is composed at, what it leaves of
 * the remainder a relation is over, which statements of a remainder a free number meets together,
 * and which statements of a way leave none of it in common. A form is read so only where it is
 * weighed by whole numbers and moved by a whole number, over numbers each of one position outside
 * every container ({@link WhatStatementsOfOneFormDecide#outsideEveryContainer}). A number inside a
 * container may be of another element in each statement, and a form weighed by what is not whole
 * may stand between whole numbers; nothing shows either comes round as the form's remainder does,
 * so no statement of them is read as one with another.
 *
 * @param of the remainder of the form unmoved
 * @param by the whole number the form is moved by
 */
record ARemainderMoved(Unmoved of, BigInteger by) {

    /** A remainder of a form with no constant, by a divisor above nought. */
    record Unmoved(Map<NumericTerm, ExactRatio> weighing, BigInteger divisor) {

        Unmoved {
            weighing = Map.copyOf(weighing);
        }
    }

    /** The remainder by {@code divisor} of {@code dividend}, or empty where it is not read as one
     *  with others. */
    static Optional<ARemainderMoved> of(LinearForm<NumericTerm> dividend, BigInteger divisor) {
        if (dividend.coefs().isEmpty() || divisor.signum() <= 0
                || !WhatStatementsOfOneFormDecide.outsideEveryContainer(dividend.coefs().keySet())
                || !(whole(dividend.constant()) instanceof BigInteger moved)) {
            return Optional.empty();
        }
        for (ExactRatio each : dividend.coefs().values()) {
            if (whole(each) == null) {
                return Optional.empty();
            }
        }
        return Optional.of(new ARemainderMoved(new Unmoved(dividend.coefs(), divisor), moved));
    }

    /** The remainder {@code statement} states, or empty where it is not read as one with
     *  others. */
    static Optional<ARemainderMoved> of(RowDemand.OnARemainder statement) {
        return saidBy(statement).map(Said::stated);
    }

    /**
     * What a statement says of its remainder: the remainder, and what the statement leaves of the
     * remainder of the form unmoved ({@link #unmoved}).
     *
     * @param stated  the remainder the statement states
     * @param unmoved what it leaves of the remainder of the form unmoved
     */
    record Said(ARemainderMoved stated, WholeNumberRuns unmoved) {}

    /**
     * What {@code statement} says of its remainder, or empty where it is not read as one with
     * others.
     *
     * <p>A function of the statement alone, which every reader that holds one statement of a
     * remainder against another asks of the same statements over and over: read once a reading
     * ({@link OneReading#remainderSaidBy}).
     */
    static Optional<Said> saidBy(RowDemand.OnARemainder statement) {
        return OneReading.remainderSaidBy(statement, () ->
                of(statement.dividend(), statement.remainder().divisor())
                        .map(stated -> new Said(stated, stated.unmoved(statement.leaves()))));
    }

    /** Whether {@code one} and {@code other} state one remainder, which is where either leaves
     *  something of the other's ({@link #leftBy}). */
    static boolean ofOneRemainder(RowDemand.OnARemainder one, RowDemand.OnARemainder other) {
        return of(one).filter(own -> own.isStatedBy(other)).isPresent();
    }

    /** Whether {@code statement} states this remainder, moved by whatever number: where it
     *  leaves something of it ({@link #leftBy}). */
    boolean isStatedBy(RowDemand.OnARemainder statement) {
        return of(statement).filter(stated -> stated.of.equals(of)).isPresent();
    }

    /** What {@code statement} leaves of this remainder, or empty where it states another. */
    Optional<WholeNumberRuns> leftBy(RowDemand.OnARemainder statement) {
        return of(statement).filter(stated -> stated.of.equals(of))
                .map(stated -> turnedBack(statement.leaves(), stated.by.subtract(by),
                        of.divisor()));
    }

    /** What the statements of {@code way} leave of this remainder, or empty where none states
     *  it. */
    Optional<WholeNumberRuns> leftAlong(Reachability.Reaching way) {
        WholeNumberRuns left = null;
        for (OnTheWay.TakenIn cut : way.boundedOnTheWay()) {
            if (cut.demand() instanceof RowDemand.OnARemainder asked
                    && leftBy(asked).orElse(null) instanceof WholeNumberRuns leaves) {
                left = left == null ? leaves : left.and(leaves);
            }
        }
        return Optional.ofNullable(left);
    }

    /** What {@code leaves} of this remainder leaves of the remainder of the form unmoved. */
    WholeNumberRuns unmoved(WholeNumberRuns leaves) {
        return turnedBack(leaves, by, of.divisor());
    }

    /**
     * The remainders {@code r} by {@code divisor} with {@code floorMod(r + moved, divisor)} among
     * {@code runs}: what a statement of the remainder of a form moved by {@code moved} leaves of the
     * remainder of the form.
     */
    static WholeNumberRuns turnedBack(WholeNumberRuns runs, BigInteger moved, BigInteger divisor) {
        WholeNumberRuns every = Standing.OfARemainderAndAForm.every(divisor);
        WholeNumberRuns out = WholeNumberRuns.NONE;
        for (WholeNumberRuns.Run run : runs.and(every).runs()) {
            BigInteger from = run.from().subtract(moved).mod(divisor);
            BigInteger to = run.to().subtract(moved).mod(divisor);
            out = out.or(from.compareTo(to) <= 0 ? WholeNumberRuns.one(from, to)
                    : WholeNumberRuns.one(from, divisor.subtract(BigInteger.ONE))
                            .or(WholeNumberRuns.one(BigInteger.ZERO, to)));
        }
        return out;
    }

    private static BigInteger whole(ExactRatio ratio) {
        return ratio.isWhole() && ratio.floor() instanceof ExactAnswer.Held<BigInteger>(var value)
                ? value : null;
    }
}
