package souther.compiler.values;

/**
 * A question about what one block admits, for a reader that has to ask it of every block of every
 * alternative.
 *
 * <p>What is walked over and what is asked are two things, and this is the second. A reading holds
 * its alternatives, and which of them survives something said elsewhere is a question about the
 * whole product — so the walk belongs to whoever owns the alternatives and the question belongs to
 * whoever owns the other half. Written as one, a reader asking a new question would walk the
 * alternatives again, and the correlation between positions an alternative states is what a second
 * walk is free to lose.
 *
 * <p><b>A block and not a position.</b> An alternative is a product over the positions it holds as
 * one value ({@link Sameness}), and a side of that product is what a question about the product can
 * be asked of. Asked per position, a rule stating {@code p == r} would be answered twice, once
 * against each of two answers the reading no longer holds apart — and whoever asked would have to
 * put the two together to say what the alternative admits, which is the walk done again by
 * somebody who cannot see the alternatives.
 *
 * <p>Three answers, because a question about one block may be one this compiler has not worked
 * out — the strings a pattern admits are a machine somebody has to build. What that means for the
 * alternative it was asked about is {@link AdmissibleValues#anyAlternativeAdmits}'s to say.
 *
 * @param <A> what a position is called
 */
@FunctionalInterface
public interface AskedOfEachBlock<A> {

    /**
     * Whether anything {@code set} admits at {@code block} satisfies what is being asked.
     *
     * @param block the positions the alternative holds as one value, which is one position
     *              wherever no equality was read of it
     * @param set what the alternative being walked admits there, which is never empty — an
     *            alternative with an empty side stands for nothing and is not one
     */
    Emptiness of(Sameness.Block<A> block, ValueSet set);
}
