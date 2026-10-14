package souther.compiler.values;

import souther.compiler.observe.Figure;
import souther.compiler.observe.WorkFigure;
import souther.compiler.regex.PatternPlan;

import java.util.Comparator;

/**
 * Why a reading could not say which values a position holds, and the figure of this compiler's it
 * stopped at where a figure is what stopped it.
 *
 * <p>The figure travels beside the reason and is not read off it. Two of the reasons are an
 * allowance running out, and the allowance is one a run is handed: the same reason under two
 * policies is two numbers, and the reason alone names neither. So the figure is taken where the
 * machine was refused and carried from there, and a reader told this reading stopped at a figure
 * is told the one it stopped at.
 *
 * <p>Present exactly where the reason is one of those ({@link #carriesAFigure}). A reason no
 * allowance stopped holds none, and one that is a figure fixed where it is declared is said by
 * whoever reads the reason, since there is only one figure it can be.
 *
 * @param why    what stopped the reading
 * @param figure the figure it stopped at, or null where {@code why} carries none
 */
public record StoppedReading(UnreadReason why, Figure figure) {

    /**
     * In the vocabulary's declared order, and then by the figure: a steady order, which two of
     * these are equal in only where they are equal.
     */
    public static final Comparator<StoppedReading> IN_A_STEADY_ORDER =
            Comparator.comparing(StoppedReading::why)
                    .thenComparing(StoppedReading::figure, Comparator.nullsFirst(
                            Comparator.comparing(Figure::name).thenComparing(Figure::most)));

    public StoppedReading {
        if (why == null) {
            throw new IllegalArgumentException("a reading that stopped was stopped by something");
        }
        if ((figure != null) != carriesAFigure(why)) {
            throw new IllegalArgumentException(figure == null
                    ? "a reading stopped by an allowance says which figure it stopped at: " + why
                    : "a reading stopped by " + why + " stopped at no figure: " + figure);
        }
    }

    /** A reason no allowance stopped, which is every reason but the ones that carry a figure. */
    public static StoppedReading of(UnreadReason why) {
        return new StoppedReading(why, null);
    }

    /**
     * A reading of the values a position admits, stopped where its allowance refused.
     *
     * <p>Said as the figures of what a position admits, because that is the answer every reason
     * here is about: whichever allowance a caller built it out of, what was refused was the values
     * the position was being read to admit.
     */
    public static StoppedReading ofTheValues(UnreadReason why, PatternPlan.Refused refused) {
        return new StoppedReading(why, refused.as(WorkFigure.ADMITTED_VALUES_ONE_MACHINE,
                WorkFigure.ADMITTED_VALUES_IN_ALL));
    }

    /**
     * Whether a reading stopped by {@code why} carries the figure it stopped at.
     *
     * <p>A switch and no {@code default}, so a reason added to the vocabulary says whether it is an
     * allowance running out rather than arriving as one that is not.
     */
    public static boolean carriesAFigure(UnreadReason why) {
        return switch (why) {
            // An allowance a run is handed, refused at one of its two limits: which one, and at
            // what number, is what was compared.
            case PATTERN_TOO_COSTLY, EXACT_VALUES_TOO_COSTLY -> true;
            // The depth a walk could afford is a figure, and one fixed where it is declared, so
            // the reason says which and nothing need travel beside it.
            case NOT_REACHED_PAST_DEPTH_LIMIT -> false;
            case RELATES_TWO_POSITIONS, RELATES_ELEMENTS_OF_A_CONTAINER, FORM_NOT_READ,
                 ALTERNATIVE_NOT_READ, NOT_REACHED -> false;
        };
    }
}
