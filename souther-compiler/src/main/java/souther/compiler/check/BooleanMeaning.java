package souther.compiler.check;

import souther.compiler.core.Core;

import java.util.Optional;

/**
 * A value the body asks the truth of, in the words a comparison is read in — for a reader outside
 * this package that reads conditions that way.
 *
 * <p>The checker's reading and not a second one. Which spellings deny what is under them is
 * {@link ClauseExpr}'s answer, and which operations mean a size compared against nought is
 * {@link Conditions#asSizeComparison}'s; a reader that worked either out for itself would be a
 * second account of what a condition says, free to disagree with the one a guard is settled by.
 *
 * <p>Two questions and not one, because what is under a denial may be a name. Where a name stands
 * for a value is the asker's reading of the body, which this has none of, so the denials are taken
 * off here and the asker follows what is left before asking what it means.
 */
public final class BooleanMeaning {

    private BooleanMeaning() {
    }

    /**
     * What a denial stands over, and whether the whole states it or denies it.
     *
     * @param part     what is under every denial, with none of them left on it
     * @param positive whether the whole coming out the way asked is {@code part} holding
     */
    public record UnderADenial(Core part, boolean positive) {}

    /**
     * What {@code truth}, asserted where {@code positive}, says of the value under its denials — or
     * empty where nothing denies it, or where it is a connective rather than one value.
     */
    public static Optional<UnderADenial> underADenial(Core truth, boolean positive) {
        return ClauseExpr.of(truth, positive) instanceof ClauseExpr.Leaf leaf
                && leaf.spelled().size() > 1
                ? Optional.of(new UnderADenial(leaf.of(), leaf.positive()))
                : Optional.empty();
    }

    /**
     * The comparison {@code part} means, or empty where it means none.
     *
     * <p>A comparison is itself, and an emptiness check is its size against nought — a comparison
     * no source wrote, composed by this reading.
     */
    public static Optional<Comparison> asAComparison(Core part) {
        return Core.withoutStanding(Conditions.asSizeComparison(part)) instanceof Core.Binary binary
                ? Comparison.of(binary) : Optional.empty();
    }
}
