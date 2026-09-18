package souther.compiler.partition;

/**
 * One condition of a way that the row offered, or not offered, was composed without.
 *
 * <p><b>One list, because that is what a reader of a point wants, and two subjects underneath it.</b>
 * A way states conditions about the input a row writes values at and conditions about the answers a
 * row stands its dependencies in with, and the two are read by two projections with vocabularies of
 * their own ({@link ReachabilityGap}, {@link DemandGap}). Put into one type by flattening their
 * arms together, the sentence written for a shortfall of one subject would be reachable from the
 * other; put together only where the page is written, a reader would be assembling the account
 * instead of reading one.
 *
 * <p><b>And it is not the union of the two lists.</b> A condition about an answer is one the input
 * projection has no words for — always, whatever the demand reading then made of it, because the
 * region a row is searched in is over the input's positions and an answer is at none of them. So
 * the input side declines it whether or not anything was missed, and an account taking both lists
 * as they stand would report a condition this compiler composed a value against as one it left out.
 * What the entries are is settled by {@link CompositionAccount}, where both projections' answers
 * are in hand.
 */
public sealed interface ConditionGap {

    /** Which question a report about the condition asks for its place, which is the condition's
     *  own answer wherever it came from. */
    ConditionReportAnchor anchor();

    /** A condition about the input the row was composed without. */
    record OfTheInput(ReachabilityGap gap) implements ConditionGap {

        public OfTheInput {
            if (gap == null) {
                throw new IllegalArgumentException("a gap of the input is some gap");
            }
        }

        @Override
        public ConditionReportAnchor anchor() {
            return gap.anchor();
        }
    }

    /** A condition about an answer the dependency's value was composed without. */
    record OfADemand(DemandGap gap) implements ConditionGap {

        public OfADemand {
            if (gap == null) {
                throw new IllegalArgumentException("a gap of a demand is some gap");
            }
        }

        @Override
        public ConditionReportAnchor anchor() {
            return gap.anchor();
        }
    }
}
