package souther.compiler.partition;

import souther.compiler.check.ComparisonClaim;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.Place;

import java.util.Map;
import java.util.Optional;

/**
 * A border read as the line its rule draws over the positions it is on, for a reader holding that
 * line against a line the model did not draw.
 *
 * <p>Two shapes, because a rule says one of two things about a value: that the values either side
 * of it are kept and refused ({@link OrderedAffineBoundary}), or that the value itself is singled
 * out ({@link SingledAffineBoundary}). Both read a row the same way — what the direction comes to
 * there — and differ in which rows they keep, which is what {@link #satisfies} answers.
 */
public sealed interface DrawnBoundary permits OrderedAffineBoundary, SingledAffineBoundary {

    /** The quantity, which is what reads a row's positions and what names the line. */
    LinearQuantity of();

    /** The quantity with its common divisor taken out, which every row is read along. */
    QuantityKey direction();

    /** Whether a row whose positions read as {@code values} satisfies the rule that drew this, or
     *  why its sum could not be worked out. */
    ExactAnswer<Boolean> satisfies(Map<NumericTerm, Place> values);

    /**
     * How {@code border} reads as a line, empty where it is no form over positions a weight could be
     * written for, and unheld where the place its values part at was not worked out.
     */
    static ExactAnswer<Optional<DrawnBoundary>> of(Border border) {
        return switch (border.origin().lineFacts().claim()) {
            case ComparisonClaim.Cut _ -> OrderedAffineBoundary.of(border)
                    .map(drawn -> drawn.map(DrawnBoundary.class::cast));
            case ComparisonClaim.Singled _ -> SingledAffineBoundary.of(border)
                    .map(drawn -> drawn.map(DrawnBoundary.class::cast));
        };
    }
}
