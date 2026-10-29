package souther.compiler.inputs;

import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactCut;
import souther.compiler.numeric.ExactRatio;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

/**
 * The decimals a row is built from, chosen inside a run of numbers.
 *
 * <p>A relation draws its lines at rational numbers: {@code 3x >= y} over the unit run turns at a
 * third. A row stands at decimals, so a row is never built at the line itself or at an end of a
 * run that is no decimal, and a run whose end is left out has no row at that end. A row is built
 * inside the run instead, nearest the end asked at, at the fewest places that has one. Which row
 * is built does not matter to what is asked of it, that the program gets to the end of working it
 * out, beyond that it stands in the run.
 *
 * <p>The places are worked out from the width of the run and not searched for: a step of at most
 * half the width has a multiple strictly inside any run of that width. A run needing more places
 * than a row is built at ({@link DecimalOperation#PLACES_A_ROW_IS_BUILT_AT}) has no row built in
 * it from its width, which is a row not built and not a row there is none of; the end of the run
 * far from the line is then the row, where it is a decimal.
 */
final class DecimalPoints {

    /** The digits one binary digit is worth, to start the count of places below the answer. */
    private static final double DIGITS_PER_BIT = 0.30102999566398;

    /**
     * Where a side of a run with no end is asked: ten to the places a row is built at
     * ({@link DecimalOperation#PLACES_A_ROW_IS_BUILT_AT}) and its opposite. A number of that many
     * digits before the point, as a row's numbers have that many places after it.
     *
     * <p>A point to build the rows at and see that they stand, and no limit of the numbers a
     * decimal holds nor of the rows that can be built: a row at ten to the hundred thousand
     * computes as well. What the run claims of the numbers past it is not that rows are built
     * there but what claims it of the numbers between: the room of an operation turns on the
     * scales of its operands, and the numbers a row stands the partner at are written at few
     * places however far out the line is ({@link #besideTheLine}), so the scales stay as they
     * are. The digits a host can hold of a number are its resource and no statement about the
     * arithmetic, and {@code 1E+2147483647 + 5.0}, whose scales are the whole range apart, is a
     * sum of a number written at the edge of the scale range, which no row is built at.
     */
    private static final ExactRatio EDGE_OF_WHAT_IS_BUILT = ExactRatio.of(
            BigInteger.TEN.pow(DecimalOperation.PLACES_A_ROW_IS_BUILT_AT));

    private DecimalPoints() {
    }

    /** The number a row is built at to ask the side of a run that has no end: the greatest
     *  number built for the upper side, and the least for the lower. */
    static ExactRatio edgeOfWhatIsBuilt(boolean upper) {
        return upper ? EDGE_OF_WHAT_IS_BUILT : EDGE_OF_WHAT_IS_BUILT.negated();
    }

    /**
     * A decimal in the run {@code near} bounds on one side and {@code far} on the other, nearest
     * {@code near}: the end itself where it is held and a decimal, and otherwise the first multiple
     * of the step the run's width asks for that is inside it. Null where no row is built in the
     * run, or where {@code far} is not past {@code near}.
     *
     * @param nearIsLower whether {@code near} is the lower end of the run, and so {@code far} the
     *                    upper; {@code far} is null where the run has no end that way
     */
    static ExactRatio within(ExactCut near, ExactCut far, boolean nearIsLower) {
        ExactRatio at = near.at();
        if (near.inclusive() && at.fitsWrittenDecimal() && lies(at, far, nearIsLower)) {
            return at;
        }
        int places = placesToFit(near, far);
        if (places < 0) {
            return null;
        }
        ExactRatio scale = ExactRatio.of(BigInteger.TEN.pow(places));
        ExactRatio scaled = at.times(scale).orNull();
        BigInteger count = scaled == null ? null : countInside(scaled, near, nearIsLower);
        ExactRatio candidate = count == null ? null : ExactRatio.of(count).dividedBy(scale).orNull();
        return candidate != null && lies(candidate, far, nearIsLower) ? candidate : null;
    }

    /**
     * A decimal on each side of {@code line} inside the run from {@code lower} to {@code upper},
     * each nearest the line where the width of the run allows, and the end of the run far from the
     * line where it does not: the ones a row stands at to be as near a line no decimal writes as
     * the term can. Written at no more places than a row is built at, whichever number the line
     * is for, so that what is found of the rows beside it does not turn on the number it was put
     * beside. A side with none is left out, and the caller that needs both asks for two.
     */
    static List<ExactRatio> besideTheLine(ExactRatio line, ExactCut lower, ExactCut upper) {
        List<ExactRatio> beside = new ArrayList<>();
        ExactCut belowTheLine = ExactCut.tighterUpper(ExactCut.exclusive(line), upper);
        ExactCut aboveTheLine = ExactCut.tighterLower(ExactCut.exclusive(line), lower);
        ExactRatio below = within(belowTheLine, lower, false);
        ExactRatio above = within(aboveTheLine, upper, true);
        below = below != null ? below : theFarEnd(lower, belowTheLine, true);
        above = above != null ? above : theFarEnd(upper, aboveTheLine, false);
        if (below != null) {
            beside.add(below);
        }
        if (above != null) {
            beside.add(above);
        }
        return beside;
    }

    /** Whether {@code at} is a decimal written at no more places than a row is built at. */
    static boolean isBuiltAt(ExactRatio at) {
        return at.writtenDecimal() instanceof ExactAnswer.Held<Optional<BigDecimal>> written
                && written.value().filter(number -> Math.abs((long) number.scale())
                <= DecimalOperation.PLACES_A_ROW_IS_BUILT_AT).isPresent();
    }

    /**
     * The end {@code end} of a run, where it is held and a decimal built at, and is inside
     * {@code near}, the other end of the run on the line's side: null otherwise.
     */
    private static ExactRatio theFarEnd(ExactCut end, ExactCut near, boolean endIsLower) {
        if (end == null || !end.inclusive() || !isBuiltAt(end.at())) {
            return null;
        }
        return lies(end.at(), near, endIsLower) ? end.at() : null;
    }

    /**
     * The fewest places after the point at which a step is at most half the width between
     * {@code near} and {@code far}, so that a multiple of it lies strictly inside; nought where
     * the run has no far end, and negative where that is more than a row is built at.
     */
    private static int placesToFit(ExactCut near, ExactCut far) {
        if (far == null) {
            return 0;
        }
        ExactRatio width = far.at().minus(near.at()).orNull();
        if (width == null || width.signum() == 0) {
            return 0;
        }
        ExactRatio steps = ExactRatio.of(2).dividedBy(width.abs()).orNull();
        BigInteger most = steps == null ? null : steps.ceiling().orNull();
        if (most == null) {
            return -1;
        }
        int places = Math.max(0, (int) (most.bitLength() * DIGITS_PER_BIT) - 1);
        while (places <= DecimalOperation.PLACES_A_ROW_IS_BUILT_AT) {
            if (BigInteger.TEN.pow(places).compareTo(most) >= 0) {
                return places;
            }
            places++;
        }
        return -1;
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
