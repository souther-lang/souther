package souther.compiler.inputs;

import souther.compiler.numeric.ExactRatio;
import souther.exact.ExactDecimals;

import java.math.BigDecimal;
import java.util.List;
import java.util.Map;
import java.util.Objects;

/**
 * A walk that adds each element of a list of the input, as the row holds it, to the answer so far,
 * from a seed the program writes: {@code List.fold((acc, n) -> Decimal.add(acc, n.gross.value),
 * 0.0m, notes)}. Its answer is the seed and the total of the elements, the term {@code total}; a
 * run works it out one addition per element, and each can stop it for want of room.
 *
 * <p>That every addition has room is shown by induction over the walk, and not by asking one sum
 * of the seed and the total: a sum of the same number worked out once lines up other scales than
 * the steps do. The answer so far starts at the seed's scale. An element is a decimal of a row,
 * which the builder writes at no more than {@link DecimalOperation#PLACES_A_ROW_IS_BUILT_AT}
 * places before or after the point ({@link DecimalOperation#writtenForARow}), and a sum is at the
 * greater of its operands' scales. So the answer after any number of steps, and both operands of
 * every step, are at a scale no further from nought than the seed's or that bound, whichever is
 * further, and where that is within what room is shown for, every step has room, on every list a
 * row is built with. The scale the walk ends at is the greatest of the seed's and the elements',
 * which is how the list is written and not a fact of the total, so what is worked out of the
 * answer is asked as what is worked out of a total is
 * ({@link DecimalOperation#leavesNoCompletionToHowATotalIsWritten}).
 *
 * <p>Told only where the step adds the element and does nothing else, the seed is written out at
 * the scale it is written, and the list is a place of the input: anything else the walk works out
 * is no step of this one.
 *
 * @param seed  the decimal the walk starts from, at the scale the program writes it
 * @param total the key of the term the walk adds up, as {@link DecimalOperation.Formed} keys its
 *              places
 */
public record DecimalAdditiveWalk(BigDecimal seed, Object total) implements DecimalWork {

    public DecimalAdditiveWalk {
        Objects.requireNonNull(seed, "the decimal a walk starts from");
        Objects.requireNonNull(total, "the total a walk adds up");
    }

    /** The scale furthest from nought that the answer so far and any element of a row are at, on
     *  every step of the walk. */
    long scaleOfEveryStep() {
        return Math.max(Math.abs((long) seed.scale()), DecimalOperation.PLACES_A_ROW_IS_BUILT_AT);
    }

    /** Whether every step of the walk has room on every row: its operands and its answer are at
     *  no scale further from nought than room is shown for. */
    boolean everyStepHasRoom() {
        return scaleOfEveryStep() <= DecimalOperation.SCALE_THE_ROOM_IS_SHOWN_FOR;
    }

    /**
     * What the walk answers on a row whose terms stand at {@code values}: the seed added to the
     * total at the fewest places its number is written with, the representative a total is worked
     * out with ({@link DecimalOperation.Total}). Null where the row has no total.
     */
    BigDecimal workedOut(Map<Object, ExactRatio> values) {
        return new DecimalOperation.Total(total).at(values)
                .map(sum -> ExactDecimals.sumWhereThereIsRoom(seed, sum)).orElse(null);
    }

    @Override
    public List<Integer> after() {
        return List.of();
    }

    /** Itself: a walk is worked out of the seed and the input, and of nothing told before it. */
    @Override
    public DecimalAdditiveWalk shifted(int by) {
        return this;
    }
}
