package souther.compiler.inputs;

import java.math.BigDecimal;
import java.util.List;
import java.util.Objects;

/**
 * A walk over a list of the input that adds a part of each element to the answer so far, or takes
 * it away, from a seed the program writes: {@code List.fold((acc, n) -> Decimal.add(acc,
 * n.gross.value), 0.0m, notes)}. A part is a path of the element, or {@code factors} paths of it
 * multiplied. Its answer is the seed and {@code added}, the total of the parts as the relation
 * names its terms; a run
 * works it out one step per element, a product and a sum or a difference, and each can stop it
 * for want of room. A total of what a closure makes of each element ({@code List.sum(List.map(l
 * -> Decimal.multiply(l.price, l.qty), lines))}) is the same walk from nought: the library adds
 * the parts up exactly, at the scale the walk ends at.
 *
 * <p>That every step has room is shown by induction over the walk, and not by asking one sum of
 * the seed and the total: a sum of the same number worked out once lines up other scales than
 * the steps do. A number of a row is written at no more than
 * {@link DecimalOperation#PLACES_A_ROW_IS_BUILT_AT} places before or after the point
 * ({@link DecimalOperation#writtenForARow}), a product is at the sum of its factors' scales, and a
 * sum or a difference is at the greater of its operands'. So each part, and each product on the
 * way to it, is at no more than {@code factors} times that bound, and the answer so far, starting
 * at the seed's scale, after any number of steps is at a scale no further from nought than the
 * seed's or the parts', whichever is further. Where that is within what room is shown for, every
 * step has room, on every list a row is built with. The scale the walk ends at is how the list is
 * written and not a fact of the total, so what is worked out of the answer is asked as what is
 * worked out of a total is ({@link DecimalOperation#leavesNoCompletionToHowATotalIsWritten}).
 *
 * <p>Told only where the step works out the part and the sum or difference and nothing else, the
 * seed is written out at the scale it is written, and the list is a place of the input: anything
 * else the walk works out is no step of this one.
 *
 * @param seed    the decimal the walk starts from, at the scale the program writes it
 * @param added   what the walk adds to the seed, over the terms of a row: the total it adds up, or
 *                that total taken away
 * @param factors how many paths of an element each part multiplies, one where it is a path alone
 */
public record DecimalAdditiveWalk(BigDecimal seed, DecimalOperation.Formed added, int factors)
        implements DecimalWork {

    public DecimalAdditiveWalk {
        Objects.requireNonNull(seed, "the decimal a walk starts from");
        Objects.requireNonNull(added, "the total a walk adds up");
        if (factors < 1) {
            throw new IllegalArgumentException("a part of an element multiplies at least one path"
                    + " of it: " + factors);
        }
    }

    /** The scale furthest from nought that the answer so far, a part, or a product on the way to
     *  one is at, on every step of the walk. */
    long scaleOfEveryStep() {
        return Math.max(Math.abs((long) seed.scale()),
                (long) factors * DecimalOperation.PLACES_A_ROW_IS_BUILT_AT);
    }

    /** Whether every step of the walk has room on every row: what it works out is at no scale
     *  further from nought than room is shown for. */
    boolean everyStepHasRoom() {
        return scaleOfEveryStep() <= DecimalOperation.SCALE_THE_ROOM_IS_SHOWN_FOR;
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
