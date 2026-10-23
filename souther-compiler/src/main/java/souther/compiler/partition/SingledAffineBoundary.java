package souther.compiler.partition;

import souther.compiler.check.ComparisonClaim;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.Place;

import java.util.Map;
import java.util.Optional;

/**
 * A border read as the one value its rule singles out over the positions it is drawn on.
 *
 * <p>What {@code payment.amount == invoice.gross} says, with the shape it was written in gone: a
 * direction over the positions, the place along it the rule names, and whether the rule holds at
 * that place or everywhere else. No side is kept: a row at the place is kept by an equality and
 * refused by its denial, and every other row the other way round.
 *
 * @param of               the quantity
 * @param at               the place along {@code direction} the rule names, in the quantity's own
 *                         units
 * @param holdsAtTheValue  whether the rule holds at {@code at} and nowhere else, rather than
 *                         everywhere but there
 * @param direction        the quantity with its common divisor taken out
 */
public record SingledAffineBoundary(LinearQuantity of, CutPosition at, boolean holdsAtTheValue,
                                    QuantityKey direction) implements DrawnBoundary {

    public SingledAffineBoundary {
        if (of == null || at == null || direction == null) {
            throw new IllegalArgumentException("a value singled out is a place on a quantity: "
                    + of + " " + at);
        }
        if (!direction.equals(QuantityKey.of(of.direction()))) {
            throw new IllegalArgumentException("a line runs the way its quantity does: "
                    + direction + " for " + of);
        }
    }

    /**
     * How {@code border} reads as one value singled out, empty where its rule orders the values
     * rather than naming one or is no form a weight could be written for, and unheld where the place
     * was not worked out.
     *
     * <p>The place is the seam's ({@link Seam#where}), which for a rule naming a value is where the
     * values part under it and over it — the place itself.
     */
    public static ExactAnswer<Optional<SingledAffineBoundary>> of(Border border) {
        ComparisonClaim claim = border.origin().lineFacts().claim();
        if (!(claim instanceof ComparisonClaim.Singled singled)
                || !(border.cut().of() instanceof LinearQuantity of)
                || !OrderedAffineBoundary.weighable(of)) {
            return ExactAnswer.held(Optional.empty());
        }
        return Seam.where(of, border.cut().at(), claim).map(seam -> Optional.of(
                new SingledAffineBoundary(of, seam.at(), singled.holdsAtTheValue(),
                        QuantityKey.of(of.direction()))));
    }

    /** Whether a row at {@code values} is at the place singled out, as the rule would have it. */
    @Override
    public ExactAnswer<Boolean> satisfies(Map<NumericTerm, Place> values) {
        return OrderedAffineBoundary.along(direction, values)
                .map(value -> (at.compare(value) == 0) == holdsAtTheValue);
    }

    /** The place singled out, as a number along the direction. */
    public ExactRatio value() {
        return at.exactly();
    }
}
