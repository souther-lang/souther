package souther.compiler.coverage;

/**
 * A number a run is recorded at, of whichever family it was issued to.
 *
 * <p>What a recording is written in. One counter hands the numbers out because one set of numbers
 * is what a run leaves behind, so a recording holds arms and comparisons together and something has
 * to be able to say "a place, of either kind" without saying which.
 *
 * <p><b>Which is not the same as a reader being able to take either.</b> The two arms are the two
 * types they are, and a reader that wants an arm says {@link ArmProbe}: what it is asking is
 * answered by an arm and by nothing else, and a comparison handed to it would be a claim about a
 * place the reader was not asking about. This exists for the few that hold both — what records a
 * run, and what a run is read back as — and a reader that named it to avoid choosing has chosen
 * wrong.
 *
 * <p>Sealed, so the two are the whole of it and a third family added later arrives at every place
 * that takes one.
 */
public sealed interface RunSite permits ArmProbe, ComparisonEmissionSite {

    /** The numbering that handed this out, which is what says what the number means. */
    NumberingIdentity numbering();

    /**
     * The number itself, which is what a probed class is given and what a recording reads back.
     *
     * <p>The one way out of the typed vocabulary, and it goes to the code being emitted. Anything
     * else asking for it is turning an address back into something a caller can pair with a place
     * it was not issued for — which is what the numbering exists to stop, so who may ask is fixed
     * by a walk over the compiled classes rather than by this sentence.
     */
    int raw();
}
