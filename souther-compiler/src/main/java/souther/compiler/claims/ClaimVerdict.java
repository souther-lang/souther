package souther.compiler.claims;

import souther.compiler.reach.WhyUnsettled;

/**
 * What the model's own rules say about a claim its body makes.
 *
 * <p>Three answers, and which of them a claim gets is one decision made in one place
 * ({@link Claims}). Written per measure instead, a claim was acted on by one and ignored by
 * another — and the one that acted on it took the case out of its denominator without anything
 * having asked whether the case can arrive.
 *
 * <p>None of these moves a denominator. What a row is owed at comes off the reading of the input,
 * and a claim is held against that reading rather than read into it: {@link Confirmed} says the
 * rules had already taken the case out, {@link Unproven} says nothing took it out, and
 * {@link Contradicted} says the rules put it in.
 */
public sealed interface ClaimVerdict {

    /**
     * The rules refuse the case, so the claim says what they say.
     *
     * <p>The case is out of every denominator already, by the rules. What the claim adds is the
     * author's own words for why, which a report keeps.
     */
    record Confirmed() implements ClaimVerdict {}

    /**
     * The rules leave the case standing, so a caller can supply one and the claim is wrong.
     *
     * <p>The one answer that refuses a build. Reaching the {@code unreachable} is E1911, so a model
     * saying this is a model whose own signature admits an input it aborts on.
     */
    record Contradicted() implements ClaimVerdict {}

    /**
     * Nothing settled it.
     *
     * <p>The case keeps whatever it was owed. A claim that is not proven does not take an
     * obligation away — what removes one is a proof, and the absence of a proof is not one — and
     * what a report says about it is that it was not proven, so that an exclusion is never both
     * unproven and silent.
     */
    record Unproven(WhyUnsettled why) implements ClaimVerdict {

        public Unproven {
            if (why == null) {
                throw new IllegalArgumentException("a claim unproven for no reason was proven");
            }
        }
    }
}
