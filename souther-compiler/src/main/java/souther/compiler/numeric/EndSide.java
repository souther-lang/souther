package souther.compiler.numeric;

/**
 * Which of a range's two ends something is about.
 *
 * <p>Beside {@link Towards} and not the same thing said twice. That one is a direction along an
 * order and is asked by four different questions — which way a run lies, which side of a threshold
 * a rule is satisfied on, which way a place is rounded, which way to look for the nearest value.
 * This one names an end, and a caller holding both an end and something worked out against it needs
 * to say which end that was.
 *
 * <p><b>Because the two ends can be the same end.</b> A range holding one value stops at that value
 * both ways, so a lower end and an upper end can be {@link Endpoint#sameAs} each other. Told apart
 * by the number alone, what was worked out against one of them can be put beside the other and
 * nothing says so.
 *
 * <p>The end is taken from here rather than read off a range by the caller, so that choosing a side
 * and choosing which end to read are one act. A caller that could do them separately is a caller
 * that can name one side and hand over the other's end.
 */
public enum EndSide {
    LOWER,
    UPPER;

    /**
     * Which way the values lie from this end, which is what a search for the nearest one asks.
     *
     * <p>The one place the two vocabularies meet. Worked out at each caller, the pairing of a side
     * with a direction is remembered in as many places as there are callers, and a run read from the
     * wrong end of a range is what a slip there comes to.
     */
    public Towards inward() {
        return this == LOWER ? Towards.ABOVE : Towards.BELOW;
    }

    /** Which way lies past this end, which is where a run nothing stops runs off to. */
    public Towards outward() {
        return inward().opposite();
    }

    /**
     * The end the values run {@code inward} from, which is {@link #inward} read the other way.
     *
     * <p>Beside it rather than worked out by a caller, so that the pairing of an end with a
     * direction is one fact read in whichever direction a reader has. A caller holding the way a
     * rule is satisfied and wanting the end it keeps is asking this.
     */
    public static EndSide facing(Towards inward) {
        return inward == Towards.ABOVE ? LOWER : UPPER;
    }

    /** Where {@code bounds} stops on this side, or null where nothing stops it that way. */
    public Endpoint at(NumericDomain.Bounds bounds) {
        return bounds == null ? null : this == LOWER ? bounds.min() : bounds.max();
    }
}
