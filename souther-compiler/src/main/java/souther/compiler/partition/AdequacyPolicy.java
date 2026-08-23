package souther.compiler.partition;

/**
 * What measuring one behavior and composing rows for it may spend.
 *
 * <p>Three numbers that were three private constants in three classes, none of them reachable from
 * a caller — which is the absence issue #969 opened on, and it was never only about the one limit
 * that issue removed. A limit is an input the query graph hands to the analysis (rule 4 of this
 * package's documentation), the way {@link souther.compiler.check.ReadingPolicy} and
 * {@link souther.compiler.examples.EvaluationPolicy} already are.
 *
 * <p><b>Grouped by which result each weakens, and not by being numbers.</b> A budget is only ever
 * read beside the answer it makes partial, and the two halves here are not interchangeable: the
 * pair space exhausting leaves a <em>measurement</em> partial and is reported as
 * {@code Weakening.PairSpaceTruncated}, while the row limit and the cell limit leave a
 * <em>generation</em> incomplete and are reported as {@link GenerationReason}s. Held as three
 * {@code int}s side by side, a caller raising one to fix a partial measurement would as readily
 * raise one that cannot change it.
 *
 * <p><b>Owned by the compilation and not made here.</b> Nothing that measures a behavior decides
 * what it may be measured with: a policy made where it is needed is one that can differ between two
 * measurements of the same behavior, and the two would report different coverage of one model while
 * each stayed sound. So this arrives from the query graph and the analysis takes it.
 */
public record AdequacyPolicy(OfTheMeasures measures, OfTheGeneration generation) {

    public AdequacyPolicy {
        java.util.Objects.requireNonNull(measures, "a compilation measures under some budget");
        java.util.Objects.requireNonNull(generation, "a compilation composes under some budget");
    }

    /**
     * What a measure of one behavior may walk.
     *
     * @param pairSpace how many two-class combinations across the behavior's positions are counted
     *                  off the rows. The space grows with the positions and their cardinalities
     *                  together, so what bounds it is the space itself and never a count of
     *                  positions (rules 1 and 2). Past it the measure is partial and says so
     */
    public record OfTheMeasures(int pairSpace) {

        public OfTheMeasures {
            // A guardrail is a positive number a count is compared against. Refused here rather
            // than left to whoever writes it: a bound that admits nothing measures nothing, and a
            // bound of nought would report every behavior as partial over a space it never walked.
            if (pairSpace < 1) {
                throw new IllegalArgumentException(
                        "a pair space holds at least one combination, so a limit below one bounds"
                                + " nothing: " + pairSpace);
            }
        }
    }

    /**
     * What composing rows for one behavior may spend.
     *
     * @param rows         how many rows one call will write. Past this the output stops being
     *                     something a person reads and pastes, and what the search did not reach is
     *                     written down rather than left absent
     * @param cellsPerGroup how many ways of choosing an outcome from each factor a group may have
     *                     and still be offered. It bounds the walk over a group's choices, which
     *                     goes on past the ones already answered and the ones nothing could be
     *                     built for — and a group whose choices run to the billions would have that
     *                     walk stand between the author and every other group. A group past it is
     *                     named as one nothing was offered for
     */
    public record OfTheGeneration(int rows, int cellsPerGroup) {

        public OfTheGeneration {
            if (rows < 1) {
                throw new IllegalArgumentException(
                        "a generation writes at least one row, so a limit below one bounds nothing: "
                                + rows);
            }
            if (cellsPerGroup < 1) {
                throw new IllegalArgumentException(
                        "a group has at least one choice, so a limit below one bounds nothing: "
                                + cellsPerGroup);
            }
        }
    }
}
