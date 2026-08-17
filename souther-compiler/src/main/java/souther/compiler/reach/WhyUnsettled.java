package souther.compiler.reach;

/**
 * Why a reading could not say whether anything arrives.
 *
 * <p>Not the same question as why a position's declarations left a distinction open
 * ({@link souther.compiler.inputs.Unsettlement}), which is about what the rules of a type came to.
 * This is about a place in a body and the conditions on the way to it.
 *
 * <p>The reasons are kept apart because they are owed different things. A condition of a shape this
 * reading has no rule for is this compiler's limit, and widening the reading removes it. Nothing to
 * show that something arrives is not a limit at all — it is the ordinary state of a place nobody
 * built a value for and no run reached, and it stays that way however wide the reading gets.
 */
public sealed interface WhyUnsettled {

    /**
     * Nothing contradicted, and nothing shows anything arrives either.
     *
     * <p>The usual answer, and the one that keeps a claim from being refuted on a domain's silence.
     */
    record NoWitness() implements WhyUnsettled {}

    /**
     * A condition on the way here is of a shape this reading has no rule for, so what it settles
     * was not taken in.
     *
     * <p>Left out rather than guessed at, which is what keeps the proofs sound: a reading that took
     * nothing in ruled nothing out. What it costs is this answer.
     *
     * @param at where the condition is written
     */
    record AConditionWasNotRead(souther.compiler.diag.SourcePos at) implements WhyUnsettled {}

    /**
     * The rules of the position an arm matches on did not settle whether its cases can stand there.
     *
     * <p>Carried through rather than restated. Whether a distinction can stand at a position is the
     * position's own question and it has its own words for not settling it
     * ({@link souther.compiler.inputs.Unsettlement}); a reading that answered "no witness" here
     * would drop what the position already said about why.
     */
    record ThePositionDidNotSettleIt(souther.compiler.inputs.Unsettlement why)
            implements WhyUnsettled {

        public ThePositionDidNotSettleIt {
            if (why == null) {
                throw new IllegalArgumentException("a position unsettled by nothing settled it");
            }
        }
    }

    /** The walk did not get to it: something it could not read stood in the way, or it stopped at
     *  the depth it opens branches to. */
    record TheWalkDidNotReachIt() implements WhyUnsettled {}
}
