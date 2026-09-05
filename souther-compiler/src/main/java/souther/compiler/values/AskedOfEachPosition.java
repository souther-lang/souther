package souther.compiler.values;

/**
 * A question about what one position admits, for a reader that has to ask it of every position of
 * every alternative.
 *
 * <p>What is walked over and what is asked are two things, and this is the second. A reading holds
 * its alternatives, and which of them survives something said elsewhere is a question about the
 * whole product — so the walk belongs to whoever owns the alternatives and the question belongs to
 * whoever owns the other half. Written as one, a reader asking a new question would walk the
 * alternatives again, and the correlation between positions an alternative states is what a second
 * walk is free to lose.
 *
 * <p>Three answers, because a question about one position may be one this compiler has not worked
 * out — the strings a pattern admits are a machine somebody has to build. What that means for the
 * alternative it was asked about is {@link AdmissibleValues#anyAlternativeAdmits}'s to say.
 *
 * @param <A> what a position is called
 */
@FunctionalInterface
public interface AskedOfEachPosition<A> {

    /**
     * Whether anything {@code set} admits at {@code position} satisfies what is being asked.
     *
     * @param set what the alternative being walked admits at the position, which is never empty —
     *            an alternative with an empty side stands for nothing and is not one
     */
    Emptiness of(A position, ValueSet set);
}
