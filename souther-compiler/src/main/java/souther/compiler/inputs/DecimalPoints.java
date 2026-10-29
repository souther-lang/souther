package souther.compiler.inputs;

import souther.compiler.numeric.ExactCut;
import souther.compiler.numeric.ExactRatio;

import java.math.BigInteger;

/**
 * The decimals a row is built from, chosen near the ends of a run of numbers.
 *
 * <p>A relation draws its lines at rational numbers: {@code 3x >= y} over the unit run turns at a
 * third. A row stands at decimals, so a row is never built at the line itself or at an end of a
 * run that is no decimal, and a run whose end is left out has no row at that end. A row is built
 * near the end instead, inside the run, at the fewest places that has one. Which row is built does
 * not matter to what is asked of it, that the program gets to the end of working it out, beyond
 * that it stands in the run.
 */
final class DecimalPoints {

    /** The most places after the point a row is built at; a run too narrow for a decimal of
     *  this many has no row built in it. */
    private static final int MOST_PLACES = 40;

    private DecimalPoints() {
    }

    /**
     * A decimal in the run {@code near} bounds on one side and {@code far} on the other, nearest
     * {@code near}: the end itself where it is held and a decimal, and otherwise the first decimal
     * inside it at the fewest places. Null where the run has none that is built, or where
     * {@code far} is not past {@code near}.
     *
     * @param nearIsLower whether {@code near} is the lower end of the run, and so {@code far} the
     *                    upper; {@code far} is null where the run has no end that way
     */
    static ExactRatio within(ExactCut near, ExactCut far, boolean nearIsLower) {
        ExactRatio at = near.at();
        if (near.inclusive() && at.fitsWrittenDecimal() && lies(at, far, nearIsLower)) {
            return at;
        }
        for (int places = 0; places <= MOST_PLACES; places++) {
            ExactRatio scale = ExactRatio.of(BigInteger.TEN.pow(places));
            ExactRatio scaled = at.times(scale).orNull();
            BigInteger count = scaled == null ? null : countInside(scaled, near, nearIsLower);
            ExactRatio candidate = count == null ? null
                    : ExactRatio.of(count).dividedBy(scale).orNull();
            if (candidate != null && lies(candidate, far, nearIsLower)) {
                return candidate;
            }
        }
        return null;
    }

    /** The whole number of steps nearest {@code scaled} that lies inside {@code near}, going
     *  inward from it. */
    private static BigInteger countInside(ExactRatio scaled, ExactCut near, boolean nearIsLower) {
        if (scaled.isWhole()) {
            BigInteger held = scaled.floor().orNull();
            if (held == null || near.inclusive()) {
                return held;
            }
            return nearIsLower ? held.add(BigInteger.ONE) : held.subtract(BigInteger.ONE);
        }
        return nearIsLower ? scaled.ceiling().orNull() : scaled.floor().orNull();
    }

    /** Whether {@code value} is on the near side of {@code far}, which is null where there is no
     *  end that way. */
    private static boolean lies(ExactRatio value, ExactCut far, boolean nearIsLower) {
        if (far == null) {
            return true;
        }
        int order = value.compareTo(far.at());
        if (order == 0) {
            return far.inclusive();
        }
        return nearIsLower ? order < 0 : order > 0;
    }
}
