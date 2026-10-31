package souther.compiler.inputs;

import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.types.BinOp;
import souther.exact.ExactDecimals;

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.BitSet;
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
 * built with at the fewest digits its number can be written with, or a total of a list of
 * decimals ({@link Total}), which is the sum of the list of that one number. Those are the
 * operands whose scale is known, and the scale is what the room is for: an operand of any other
 * kind is not told, and the operation with it.
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
                    case Total total -> here.add(total.term());
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
     * not by what the other is put at, which is no fact about the number: nothing is claimed,
     * unless the room does not turn on the numbers at all ({@link #roomsOf}). That is so where
     * every operand is a place of the input as it stands or a total, so that it is written at no
     * more places than a row is built at ({@link #PLACES_A_ROW_IS_BUILT_AT}) whenever there is a
     * row, and the scales of the operands and of the answer are kept to what is shown room for.
     * Then it has room at every pair of numbers a row is built at.
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
        Rooms rooms = roomsOf(all);
        if (rooms == null) {
            return false;
        }
        for (int i = 0; i < all.size(); i++) {
            boolean readsAsked = reads.get(i).contains(asked);
            if (readsAsked && reads.get(i).size() > 1 && !rooms.atEveryNumber().get(i)) {
                return false;
            }
            if (!readsAsked && reads.get(i).contains(partner) && !rooms.bounded().get(i)) {
                return false;
            }
        }
        return true;
    }

    /**
     * Whether every operation of {@code all} that reads {@code asked} reads another term with it
     * and has room at every number ({@link #roomsOf}). A run with no end on a side is asked at the
     * edge of what is built for such operations: the room is the same there as at any number. An
     * operation reading the term alone has room by the scale the term is written at, which the far
     * side of a run with no end does not say, and is not taken here.
     */
    static boolean everyOperationReadingItHasRoomAtEveryNumber(List<DecimalOperation> all,
                                                               Object asked) {
        List<Set<Object>> reads = readsOf(all);
        Rooms rooms = roomsOf(all);
        if (rooms == null) {
            return false;
        }
        for (int i = 0; i < all.size(); i++) {
            if (reads.get(i).contains(asked)
                    && (reads.get(i).size() < 2 || !rooms.atEveryNumber().get(i))) {
                return false;
            }
        }
        return true;
    }

    /**
     * Whether every operation of {@code all} has room at every number ({@link #roomsOf}). The
     * sizes of the addends of a form then say nothing of whether a row completes them: a row that
     * is built completes every one of them.
     */
    static boolean everyOperationHasRoomAtEveryNumber(List<DecimalOperation> all) {
        Rooms rooms = roomsOf(all);
        if (rooms == null) {
            return false;
        }
        return rooms.atEveryNumber().cardinality() == all.size();
    }

    /**
     * Whether what {@code all} complete at is left to the numbers and not to how a total is
     * written. A total is worked out as the sum of a list a row holds, and a list is no one thing:
     * the same number is the sum of lists of elements written at any scale, so a total's scale is
     * not a fact of its number. An operation worked out of a total, directly or through those
     * before it, is therefore worked out on a row only where its room does not turn on that scale:
     * its operands and its answer are kept to what is shown room for. One that is not (a factor at
     * the edge of the scale range has room for a total at one scale and none at the next) is
     * completed at no row, whichever representative of the total a row is worked out with.
     */
    static boolean leavesNoCompletionToHowATotalIsWritten(List<DecimalOperation> all) {
        if (all.stream().noneMatch(each -> each.operands.stream().anyMatch(Total.class::isInstance))) {
            return true;
        }
        boolean[] dependsOnATotal = new boolean[all.size()];
        boolean any = false;
        for (int i = 0; i < all.size(); i++) {
            for (Operand operand : all.get(i).operands) {
                dependsOnATotal[i] |= operand instanceof Total
                        || (operand instanceof Worked worked && worked.operation() < i
                        && dependsOnATotal[worked.operation()]);
            }
            any |= dependsOnATotal[i];
        }
        if (!any) {
            return true;
        }
        Rooms rooms = roomsOf(all);
        if (rooms == null) {
            return false;
        }
        for (int i = 0; i < all.size(); i++) {
            if (dependsOnATotal[i] && !rooms.bounded().get(i)) {
                return false;
            }
        }
        return true;
    }

    /**
     * What each operation of {@code all} has room for, in the order told.
     *
     * @param bounded       whether its operands and its answer are written at no more places than
     *                      room is shown for ({@link #SCALE_THE_ROOM_IS_SHOWN_FOR})
     * @param atEveryNumber whether it has room at every pair of numbers a row is built at, and so
     *                      completes at every row that is built: it is bounded, and each operand
     *                      is a decimal wherever there is a row, since it is a place of the input
     *                      as it stands ({@link #isAPlaceAsItStands}), a total, a literal or the
     *                      answer of an operation told before. A place weighed or moved is a
     *                      decimal only where the number it comes to is written at no more places
     *                      than a row is built at, which turns on the other terms.
     */
    private record Rooms(BitSet bounded, BitSet atEveryNumber) {
    }

    /** The rooms of {@code all}; null where an operation is worked out of one told after it. */
    private static Rooms roomsOf(List<DecimalOperation> all) {
        BitSet bounded = new BitSet(all.size());
        BitSet atEveryNumber = new BitSet(all.size());
        long[] scaleOf = new long[all.size()];
        for (int i = 0; i < all.size(); i++) {
            DecimalOperation each = all.get(i);
            long[] over = new long[2];
            boolean standing = true;
            for (int o = 0; o < 2; o++) {
                switch (each.operands.get(o)) {
                    case Written written -> over[o] = Math.abs((long) written.value().scale());
                    case Formed formed -> {
                        over[o] = PLACES_A_ROW_IS_BUILT_AT;
                        standing &= isAPlaceAsItStands(formed);
                    }
                    case Total _ -> over[o] = PLACES_A_ROW_IS_BUILT_AT;
                    case Worked worked -> {
                        if (worked.operation() >= i) {
                            return null;
                        }
                        over[o] = scaleOf[worked.operation()];
                        standing &= atEveryNumber.get(worked.operation());
                    }
                }
            }
            scaleOf[i] = each.op == BinOp.MUL ? over[0] + over[1] : Math.max(over[0], over[1]);
            boolean fits = over[0] <= SCALE_THE_ROOM_IS_SHOWN_FOR
                    && over[1] <= SCALE_THE_ROOM_IS_SHOWN_FOR
                    && scaleOf[i] <= SCALE_THE_ROOM_IS_SHOWN_FOR;
            bounded.set(i, fits);
            atEveryNumber.set(i, fits && standing);
        }
        return new Rooms(bounded, atEveryNumber);
    }

    /** Whether {@code formed} is one place of the input, as it stands or negated: the number a
     *  row is built with there, which is a decimal wherever the row is built. */
    private static boolean isAPlaceAsItStands(Formed formed) {
        return formed.constant().isZero() && formed.coefs().size() == 1
                && formed.coefs().values().stream().allMatch(weight ->
                        ExactRatio.ONE.equals(weight) || ExactRatio.ONE.negated().equals(weight));
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
            return builtAt(sum);
        }
    }

    /**
     * The total of a list of decimals, the term called {@code term}.
     *
     * <p>The scale of a total is that of the list it is the sum of ({@code max(0, scales of the
     * elements)}), and the same number is the sum of lists whose elements are written at any
     * scale: it is no fact of the number, and the list a row holds is the builder's to choose
     * ({@code ContainersAddingUp}), not this analysis'. What is claimed of the rows is claimed of
     * the rows that are built, and the builder writes every element through
     * {@link #writtenForARow}, so the scale of any list it builds, and of its sum, is no more than
     * {@link #PLACES_A_ROW_IS_BUILT_AT}: that is the bound a total is given here, and it is the
     * builder's own, not an assumption made about it. A list written at any other scale (the sum
     * of {@code [0E-2147483647]} is the number nought at the greatest scale) is not one that is
     * built.
     *
     * <p>Within that bound the scale is still the builder's choice ({@code [0.5, 0.5]} sums to one
     * at a place, and {@code [1]} at none), so a total is told only to operations whose room does
     * not turn on it ({@link #leavesNoCompletionToHowATotalIsWritten}), and is worked out here at
     * the fewest places its number is written with, as a representative that completes where
     * every scale within the bound does.
     *
     * @param term the key of the total, as {@link Formed} keys its places
     */
    public record Total(Object term) implements Operand {
        public Total {
            Objects.requireNonNull(term, "the total of a list of decimals");
        }

        /** The decimal this stands for at {@code values}; empty where the total has no value
         *  there or the number is written at more places than a row is built at. */
        Optional<BigDecimal> at(Map<Object, ExactRatio> values) {
            ExactRatio value = values.get(term);
            return value == null ? Optional.empty() : builtAt(value);
        }
    }

    /**
     * The number {@code number} as a row is built with it: written at the fewest places, and
     * empty where it is no decimal or is written at more places than a row is built at
     * ({@link #PLACES_A_ROW_IS_BUILT_AT}).
     *
     * <p>The one place that says what a decimal of a row is. What the analysis shows of a row is
     * shown of the decimals it is built with, so whatever writes a decimal into a row (a place of
     * the input, an element of a list a total is the sum of) writes it through here, and the
     * analysis may take what it reads off the rows from this alone: the scale of a decimal of a
     * row, and so of the total of a list of them, is no more than the places a row is built at.
     * Written elsewhere, a decimal could have a scale this does not bound, and no claim made
     * of the rows would be a claim of the rows that are built.
     */
    public static ExactAnswer<Optional<BigDecimal>> writtenForARow(ExactRatio number) {
        return switch (number.writtenDecimal()) {
            case ExactAnswer.Held<Optional<BigDecimal>> written -> ExactAnswer.held(written.value()
                    .filter(each -> Math.abs((long) each.scale()) <= PLACES_A_ROW_IS_BUILT_AT));
            case ExactAnswer.Unheld<Optional<BigDecimal>> unheld ->
                    ExactAnswer.unheld(unheld.why());
        };
    }

    private static Optional<BigDecimal> builtAt(ExactRatio number) {
        return number != null && writtenForARow(number)
                instanceof ExactAnswer.Held<Optional<BigDecimal>> written
                ? written.value() : Optional.empty();
    }

    /**
     * Whether every operation of {@code all} is worked out on a row whose terms stand at
     * {@code values}, each by its key, in the order they are told — and so whether a run that
     * works them out gets past them. False where an operand is a number the row does not have,
     * and where an operation's room turns on how a total is written
     * ({@link #leavesNoCompletionToHowATotalIsWritten}): a row has a representative of a total,
     * and an operation it is no fact of is not shown worked out on it.
     */
    public static boolean allCompleteAt(List<DecimalOperation> all, Map<Object, ExactRatio> values) {
        if (all.isEmpty()) {
            return true;
        }
        if (!leavesNoCompletionToHowATotalIsWritten(all)) {
            return false;
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
                case Total total -> total.at(values).orElse(null);
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
