package souther.compiler.check;

/**
 * What in a clause a finished reading could not read.
 *
 * <p>Closed, and in this compiler's own words rather than an author's. What a document writes for one
 * of these is a projection made where the document is, so a published sentence never reaches back
 * into what a reading is allowed to record. Kept as prose, the reason a clause was not read could not
 * be matched on, could not be counted, and arrived in a second spelling the first time a second
 * reader wanted it — which is the arrangement the reading of coverage was written against
 * ({@link RuleAccounting.Why}).
 *
 * <p>Only what a reading that ran to the end can conclude. A reading that stopped concluded nothing
 * about the fragment, and its arm is {@link CapabilityResult.AnalysisStopped} rather than one of
 * these. There is no arm here for a clause that could not be typed: typing it is how a reading
 * begins, and one that did not begin did not finish either.
 */
public sealed interface FragmentReason {

    /**
     * It calls an operation the check reads as a value and not as a term.
     *
     * @param operation what it calls, which is the part of the clause an author can act on
     */
    record ItCallsAnOperation(String operation) implements FragmentReason {

        public ItCallsAnOperation {
            if (operation == null) {
                throw new IllegalArgumentException("a call the check could not read is named");
            }
        }
    }

    /** Some part of it is not one of the shapes the term grammar reads. */
    record ItsShapeIsNotRead() implements FragmentReason {}

    /**
     * Every part of it was read, and neither a bound nor a term came of it.
     *
     * <p>Told apart from the two above, which name something in the clause. Here there is nothing to
     * name: the grammar took all of it, and what it came to is not something a guard can be held
     * against.
     *
     * <p>No program is known to reach this, or either of the others. The reading that owes nothing
     * because the clause folded is answered before any of them, and every clause tried that this
     * compiler could not carry turned out to be one it could not type — which is a walk that never
     * began and is answered as {@link CapabilityResult.AnalysisStopped}. The arm is here because
     * {@link Predicates} can still answer that it read a clause and owes nothing that is not a fold,
     * and an answer with nowhere to go is how one gets described by whatever is nearest.
     */
    record NothingAGuardCouldBeHeldAgainst() implements FragmentReason {}
}
