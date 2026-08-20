package souther.compiler.check;

import souther.compiler.core.Core;

/**
 * What in a clause the reading could not read.
 *
 * <p>Closed, and in this compiler's own words rather than an author's. What a document writes for one
 * of these is a projection made where the document is, so a published sentence never reaches back
 * into what a reading is allowed to record. Kept as prose, the reason could not be matched on, could
 * not be counted, and arrived in a second spelling the first time a second reader wanted it — which
 * is the arrangement the reading of coverage was written against ({@link RuleAccounting.Why}).
 *
 * <p>Taken from the part the reading stopped on rather than worked out afterwards. Asked of the
 * clause a second time, a walk can come back having read all of it while the first one gave up, and
 * the answer then has to be some word for the two disagreeing — which is what a clause with nothing
 * wrong in it used to be described by.
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

    /** It is not one of the shapes the check reads, and there is no call in it to name. */
    record ItsShapeIsNotRead() implements FragmentReason {}

    /** What the reading stopped on, said as one of these. */
    static FragmentReason of(Core stoppedOn) {
        return stoppedOn instanceof Core.PreservedCall call
                ? new ItCallsAnOperation(call.operation().name()) : new ItsShapeIsNotRead();
    }
}
