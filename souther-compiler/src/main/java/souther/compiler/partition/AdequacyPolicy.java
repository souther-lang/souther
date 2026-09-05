package souther.compiler.partition;

import souther.compiler.regex.PatternPlan;
import souther.compiler.values.Allowance;

import java.util.Objects;

/**
 * What measuring one behavior and composing rows for it may spend.
 *
 * <p>Figures that were private constants in classes of their own, none of them reachable from a
 * caller. A limit is an input the query graph hands to the analysis (rule 4 of this package's
 * documentation), the way {@link souther.compiler.check.ReadingPolicy} and
 * {@link souther.compiler.execute.EvaluationPolicy} already are.
 *
 * <p><b>Grouped by which result each weakens, and not by being numbers.</b> A budget is only ever
 * read beside the answer it makes partial, and the two halves here are not interchangeable: the
 * pair space running out leaves a <em>measurement</em> partial and is reported as
 * {@code Weakening.PairSpaceTruncated}, and so does a position whose body's rules about the strings
 * could not be composed into classes; the row limit and the cell limit leave a <em>generation</em>
 * incomplete and are reported as {@link GenerationReason}s. Held side by side, a caller raising one
 * to fix a partial measurement would as readily raise one that cannot change it.
 *
 * <p><b>Owned by the compilation and not made here.</b> Nothing that measures a behavior decides
 * what it may be measured with: a policy made where it is needed is one that can differ between two
 * measurements of the same behavior, and the two would report different coverage of one model while
 * each stayed sound. So this arrives from the query graph and the analysis takes it.
 */
public record AdequacyPolicy(OfTheMeasures measures, OfTheGeneration generation) {

    public AdequacyPolicy {
        Objects.requireNonNull(measures, "a compilation measures under some budget");
        Objects.requireNonNull(generation, "a compilation composes under some budget");
    }

    /**
     * What a measure of one behavior may walk, and what it may build.
     *
     * <p>Two figures because a measure is left partial two ways, and both of them leave the same
     * answer partial. The pair space runs out and the combinations past it go uncounted; the
     * machines a body's rules about the strings at a position need are not made and the position
     * comes back undivided. Which is what puts the second here rather than beside the figures a
     * reading spends ({@link souther.compiler.check.ReadingPolicy}): those bound what a declaration
     * is read to admit, and this one bounds what a behavior is read to tell apart. Raising either
     * of those must not make a class appear, and raising this one must not change what a
     * declaration admits.
     *
     * <p><b>Not a record, so that the figure stays in.</b> A record hands out its components, and
     * what a caller could do with a budget is make itself an allowance — one per question it
     * happened to ask, with the position allowed its machine once for each. So what leaves here is
     * an allowance and never the figure it was made from.
     */
    public static final class OfTheMeasures {

        private final int pairSpace;

        private final PatternPlan.Budget behaviorDistinctions;

        /**
         * @param pairSpace            how many two-class combinations across the behavior's
         *                             positions are counted off the rows. The space grows with the
         *                             positions and their cardinalities together, so what bounds it
         *                             is the space itself and never a count of positions (rules 1
         *                             and 2). Past it the measure is partial and says so
         * @param behaviorDistinctions what working out the classes a body's rules about the strings
         *                             at one position divide it into may build. Past it the
         *                             position's classes are not composed and it is recorded as one
         *                             this compiler did not divide, rather than divided by the
         *                             rules it could afford
         */
        public OfTheMeasures(int pairSpace,
                             PatternPlan.Budget behaviorDistinctions) {
            // A guardrail is a positive number a count is compared against. Refused here rather
            // than left to whoever writes it: a bound that admits nothing measures nothing, and a
            // bound of nought would report every behavior as partial over a space it never walked.
            if (pairSpace < 1) {
                throw new IllegalArgumentException(
                        "a pair space holds at least one combination, so a limit below one bounds"
                                + " nothing: " + pairSpace);
            }
            if (behaviorDistinctions == null) {
                throw new IllegalArgumentException(
                        "a measure builds what a behavior tells apart under some budget");
            }
            this.pairSpace = pairSpace;
            this.behaviorDistinctions = behaviorDistinctions;
        }

        public int pairSpace() {
            return pairSpace;
        }

        /**
         * A fresh allowance for the positions of one behavior's distinctions, at what this
         * compilation allows.
         *
         * <p>One measure, one of these. Asked twice while measuring one behavior, a position would
         * be allowed its machines once for each caller and what the two came to would be bought by
         * nobody — so where the measure is made is where this is asked, and it is handed on from
         * there.
         *
         * <p>On its own and not beside what a position's own answer built. Borrowing is for a
         * machine that exists, and the machines here are a body's rules rather than a
         * declaration's: a pattern written in both is the case where one would be made twice, and
         * until a model does that there is nothing to borrow and a reader wired to borrow it would
         * be carrying an allowance across a boundary for nothing. What must not follow from that is
         * the other direction — a position whose own answer stopped short still has its body's
         * rules read here, because what a behavior tells apart is not a projection of what the
         * position admits.
         *
         * @param <A> what a position is called
         */
        public <A> Allowance<A> allowanceForBehaviorDistinctions() {
            return Allowance.of(behaviorDistinctions);
        }

        /**
         * Two of these are the same where they allow the same things.
         *
         * <p>Written out because this is not a record. What a reader compares two for is whether a
         * behavior measured under one would be measured the same way under the other, which is what
         * they allow and nothing about which object holds it.
         */
        @Override
        public boolean equals(Object other) {
            return this == other || (other instanceof OfTheMeasures it
                    && pairSpace == it.pairSpace
                    && behaviorDistinctions.equals(it.behaviorDistinctions));
        }

        @Override
        public int hashCode() {
            return java.util.Objects.hash(pairSpace, behaviorDistinctions);
        }

        @Override
        public String toString() {
            return "OfTheMeasures[pairSpace=" + pairSpace
                    + ", behaviorDistinctions=" + behaviorDistinctions + "]";
        }
    }

    /**
     * What composing rows for one behavior may spend.
     *
     * @param rowLimit     how many rows one call will write. Past this the output stops being
     *                     something a person reads and pastes, and what the search did not reach is
     *                     written down rather than left absent
     * @param cellsPerGroup how many ways of choosing an outcome from each factor a group may have
     *                     and still be offered, which it may have exactly. It bounds the walk over a
     *                     group's choices, which goes on past the ones already answered and the ones
     *                     nothing could be built for — and a group whose choices run to the billions
     *                     would have that walk stand between the author and every other group. A
     *                     group past it is named as one nothing was offered for.
     *
     *                     <p>A capacity, like the two beside it: a pair space of {@code n} is walked
     *                     at {@code n} and a generation of {@code n} rows writes the {@code n}th.
     *                     This was an exclusive cutoff while it was a private constant, where
     *                     nothing had to say which it was; as a component with a name it is one or
     *                     the other, and a policy whose three numbers do not mean the same thing is
     *                     a policy a caller has to read the implementation of. At one, the smallest
     *                     group there is — a single choice — is offered, which is what a limit of
     *                     one should admit
     */
    public record OfTheGeneration(int rowLimit, int cellsPerGroup) {

        public OfTheGeneration {
            if (rowLimit < 1) {
                throw new IllegalArgumentException(
                        "a generation writes at least one row, so a limit below one bounds nothing: "
                                + rowLimit);
            }
            if (cellsPerGroup < 1) {
                throw new IllegalArgumentException(
                        "a group has at least one choice, so a limit below one bounds nothing: "
                                + cellsPerGroup);
            }
        }
    }
}
