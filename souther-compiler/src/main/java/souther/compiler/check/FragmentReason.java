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
     * against. Said as one of the others, a clause with nothing wrong in it was described as naming
     * a term the check cannot name.
     */
    record NothingAGuardCouldBeHeldAgainst() implements FragmentReason {}
}
