package souther.compiler.inputs;

import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.types.BinOp;
import souther.exact.ExactDecimals;

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;
import java.util.TreeSet;

/**
 * A sum, a difference or a product of decimals a comparison works out, told so that a row can be
 * asked whether the program gets past it.
 *
 * <p>Whether a decimal operation has room for its digits and scale is not a region of the numbers
 * its operands come to: {@code 0} written at the scale of an {@code int}'s greatest value is the
 * number {@code 0}, and its product with {@code 4.0} has no room. So no region is stated here. A
 * row is asked by working the operation out on the row's own values by the rule the run time
 * works it out by ({@link ExactDecimals#timesWhereThereIsRoom}), and the row is computed where
 * every operation told is worked out. What is shown of a row is shown only by a row that was
 * built, and not of the rows the number stands for.
 *
 * <p>An operand is a decimal as the program wrote it ({@link Written}), the result of an operation
 * worked out before ({@link Worked}), or a place of the input ({@link Formed}), which a row is
 * built with at the fewest digits its number can be written with. Those are the operands whose
 * scale is known, and the scale is what the room is for: an operand of any other kind is not
 * told, and the operation with it.
 *
 * @param op       the operator: add, subtract or multiply
 * @param operands the two operands, in the order written
 * @param after    the operations, by where they are among those told, whose result this one is
 *                 worked out of, and theirs: each is worked out before it on every run
 */
public record DecimalOperation(BinOp op, List<Operand> operands, List<Integer> after) {

    public DecimalOperation {
        operands = List.copyOf(operands);
        after = List.copyOf(new TreeSet<>(after));
        if (operands.size() != 2 || (op != BinOp.ADD && op != BinOp.SUB && op != BinOp.MUL)) {
            throw new IllegalArgumentException("a decimal operation is the sum, difference or"
                    + " product of two decimals: " + op + " " + operands);
        }
    }

    /**
     * The most places before or after the point, as a scale, at which a row is built: the budget
     * for building one, and no fact about a decimal. A run needing more places than this has no
     * row built in it, which is a row not built and not a row there is none of.
     *
     * <p>It is also what a number the analysis chooses is held to, so that the room an operation
     * has for it is shown once ({@link #allowAClaimOver}) and does not depend on which number
     * of a run it was chosen near.
     *
     * <p>And it is why the room does not turn on how large a number is. A row is built from
     * numbers written at most this many places before or after the point, so two operands of a
     * sum differ in scale by at most twice it, whatever their digits are, and the sum lines them
     * up. {@code 1E+2147483647 + 5.0} has no room because the scales are the whole range apart,
     * and the number is no row: a row is not built at it. A number far out is stood beside by
     * numbers written at few places however large it is, so the sum lines up scales no further
     * apart than at the end of a run, and a run with no end is asked at a point far out
     * ({@link DecimalPoints#edgeOfWhatIsBuilt}) as at any end.
     */
    public static final int PLACES_A_ROW_IS_BUILT_AT = 1 << 12;

    /**
     * The greatest scale an operation is shown to have room for, whatever the numbers it is worked
     * out over. Two scales this great sum to a scale an {@code int} holds with room to spare, and
     * the digits an addition lines up are fewer than a {@code BigInteger} holds.
     */
    private static final long SCALE_THE_ROOM_IS_SHOWN_FOR = 1L << 27;

    /**
     * The places of the input each of {@code all} reads, by the key of the term, through the
     * operations it is worked out of.
     */
    static List<Set<Object>> readsOf(List<DecimalOperation> all) {
        List<Set<Object>> reads = new ArrayList<>();
        for (DecimalOperation each : all) {
            Set<Object> here = new LinkedHashSet<>();
            for (Operand operand : each.operands) {
                switch (operand) {
                    case Formed formed -> here.addAll(formed.coefs().keySet());
                    case Worked worked -> {
                        if (worked.operation() < reads.size()) {
                            here.addAll(reads.get(worked.operation()));
                        }
                    }
                    case Written _ -> { }
                }
            }
            reads.add(here);
        }
        return reads;
    }

    /**
     * Whether what rows built at the ends of a run find of the operations holds of every number of
     * the run, for a claim that every value of the term {@code asked} has a row on each side of a
     * line, a row of the term {@code partner} being put there.
     *
     * <p>A row is a row where the program gets to the end of working it out
     * ({@link RowsComputed}), and a number at which it does not is no row: the claim is about the
     * numbers that have one, as it is for a whole number past where its type stops. Whether an
     * operation has room turns on the scale a number is written at and not on how large it is, so
     * what is found at the ends of a run says nothing of the numbers between, and what is claimed
     * of them is read off the operations:
     *
     * <ul>
     * <li>An operation reading {@code asked} and nothing else has room at a number or has none,
     * whichever other term is put where; where it has none there is no row at the number, and
     * where it has, the term put as the partner finds the operation as it was found.
     * <li>An operation reading both, or {@code asked} with another term, has room at a number or
     * not by what the other is put at, which is no fact about the number: nothing is claimed.
     * <li>An operation reading {@code partner} and nothing of {@code asked} is worked out over the
     * number the partner is put at, which is chosen at no more than {@link #PLACES_A_ROW_IS_BUILT_AT}
     * places whichever number of the run it is chosen for, and has room for every such number when
     * the scale it leaves is kept to what a {@code BigDecimal} and an {@code int} hold.
     * <li>Any other operation reads neither, and is found as it is worked out.
     * </ul>
     *
     * <p>The guarantee is of the operations together with how the partner is put: a row on each
     * side of the line at a number of {@code asked} has the partner at numbers written at few
     * places beside the line ({@link DecimalPoints#besideTheLine}), wherever the line is, and the
     * third item above is that. An operation added here is read as one of the four, and one that
     * cannot be is not claimed over; one that needs the partner put in another way needs that way
     * stated with it.
     */
    public static boolean allowAClaimOver(List<DecimalOperation> all, Object asked,
                                          Object partner) {
        List<Set<Object>> reads = readsOf(all);
        long[] scaleOf = new long[all.size()];
        for (int i = 0; i < all.size(); i++) {
            DecimalOperation each = all.get(i);
            long[] over = new long[2];
            for (int o = 0; o < 2; o++) {
                switch (each.operands.get(o)) {
                    case Written written -> over[o] = Math.abs((long) written.value().scale());
                    case Formed _ -> over[o] = PLACES_A_ROW_IS_BUILT_AT;
                    case Worked worked -> {
                        if (worked.operation() >= i) {
                            return false;
                        }
                        over[o] = scaleOf[worked.operation()];
                    }
                }
            }
            scaleOf[i] = each.op == BinOp.MUL ? over[0] + over[1] : Math.max(over[0], over[1]);
            boolean readsAsked = reads.get(i).contains(asked);
            if (readsAsked && reads.get(i).size() > 1) {
                return false;
            }
            if (!readsAsked && reads.get(i).contains(partner)
                    && (over[0] > SCALE_THE_ROOM_IS_SHOWN_FOR || over[1] > SCALE_THE_ROOM_IS_SHOWN_FOR
                    || scaleOf[i] > SCALE_THE_ROOM_IS_SHOWN_FOR)) {
                return false;
            }
        }
        return true;
    }

    /** What an operation is worked out of. */
    public sealed interface Operand {
    }

    /** A decimal written in the program, at the scale it is written. */
    public record Written(BigDecimal value) implements Operand {
        public Written {
            Objects.requireNonNull(value, "a decimal written in the program");
        }
    }

    /** What the operation told at {@code operation}, by where it is among those told, came to. */
    public record Worked(int operation) implements Operand {
    }

    /**
     * The number the terms of a row come to, each weighed, with {@code constant} added: a term
     * called by a key that the row does not name is a number the row does not have.
     */
    public record Formed(Map<Object, ExactRatio> coefs, ExactRatio constant) implements Operand {

        public Formed {
            if (coefs == null || constant == null
                    || coefs.keySet().stream().anyMatch(Objects::isNull)
                    || coefs.values().stream().anyMatch(Objects::isNull)) {
                throw new IllegalArgumentException("a number a row comes to weighs each of its"
                        + " terms by a number: " + coefs);
            }
            coefs = Map.copyOf(coefs);
        }

        /** The decimal this comes to at {@code values}, each term's value by its key; empty where
         *  a term has no value there, the number is none a decimal writes, or it is written at
         *  more places than a row is built at ({@link #PLACES_A_ROW_IS_BUILT_AT}), which is what
         *  the room is shown for ({@link #allowAClaimOver}). */
        Optional<BigDecimal> at(Map<Object, ExactRatio> values) {
            ExactRatio sum = constant;
            for (Map.Entry<Object, ExactRatio> each : coefs.entrySet()) {
                ExactRatio value = values.get(each.getKey());
                if (value == null || sum == null) {
                    return Optional.empty();
                }
                sum = value.times(each.getValue()).flatMap(sum::plus).orNull();
            }
            if (sum == null) {
                return Optional.empty();
            }
            return switch (sum.writtenDecimal()) {
                case ExactAnswer.Held<Optional<BigDecimal>> written -> written.value()
                        .filter(number -> Math.abs((long) number.scale())
                                <= PLACES_A_ROW_IS_BUILT_AT);
                case ExactAnswer.Unheld<Optional<BigDecimal>> _ -> Optional.empty();
            };
        }
    }

    /**
     * Whether every operation of {@code all} is worked out on a row whose terms stand at
     * {@code values}, each by its key, in the order they are told — and so whether a run that
     * works them out gets past them. False where an operand is a number the row does not have.
     */
    public static boolean allCompleteAt(List<DecimalOperation> all, Map<Object, ExactRatio> values) {
        if (all.isEmpty()) {
            return true;
        }
        BigDecimal[] results = new BigDecimal[all.size()];
        for (int i = 0; i < all.size(); i++) {
            results[i] = all.get(i).workedOut(results, values);
            if (results[i] == null) {
                return false;
            }
        }
        return true;
    }

    /** The number this comes to, or null where the row has no operand for it or the run time has
     *  no room for the answer. */
    private BigDecimal workedOut(BigDecimal[] results, Map<Object, ExactRatio> values) {
        BigDecimal[] taken = new BigDecimal[operands.size()];
        for (int i = 0; i < taken.length; i++) {
            taken[i] = switch (operands.get(i)) {
                case Written written -> written.value();
                case Worked worked -> worked.operation() < results.length
                        ? results[worked.operation()] : null;
                case Formed formed -> formed.at(values).orElse(null);
            };
            if (taken[i] == null) {
                return null;
            }
        }
        return switch (op) {
            case ADD -> ExactDecimals.sumWhereThereIsRoom(taken[0], taken[1]);
            case SUB -> ExactDecimals.differenceWhereThereIsRoom(taken[0], taken[1]);
            default -> ExactDecimals.timesWhereThereIsRoom(taken[0], taken[1]);
        };
    }

    /** The same, with the operations it is worked out of moved {@code by} places later among
     *  those told. */
    public DecimalOperation shifted(int by) {
        return new DecimalOperation(op,
                operands.stream().map(each -> each instanceof Worked worked
                        ? (Operand) new Worked(worked.operation() + by) : each).toList(),
                after.stream().map(at -> at + by).toList());
    }
}
