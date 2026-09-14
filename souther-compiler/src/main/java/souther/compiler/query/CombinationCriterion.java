package souther.compiler.query;

/**
 * Which criterion a behavior's combinations are measured against.
 *
 * <p>One, never both. A behavior whose body brings decisions together is held to those; one whose
 * decisions meet nowhere, and one with no body to read at all, is held to the pair space. The two
 * state different requirements — the first is what the model reads together, the second the product
 * of every two positions — so a report showing both would put two universes on one page, and a
 * reader would act on the one that is not the criterion.
 *
 * <p><b>Chosen by the model and never by how the measuring went.</b> The question is whether the
 * walk found a meeting, asked of {@link souther.compiler.partition.InteractionRequirements#any()}.
 * A meeting whose combinations the classes could not place, one too wide for the measure to walk,
 * one whose rows carry no account: each of those is an interaction requirement that went unmeasured
 * and says so. Read off what was measured instead, a behavior would fall back to a different
 * criterion the day a budget ran out — which is the criterion switching ADR-0089 refuses, arriving
 * as a default rather than as a decision.
 *
 * <p>Settled here and read by every surface. Each of them asking whether the groups are empty is
 * the same rule written as many times as there are readers, and the first one to be worded
 * differently is a report that measures one thing and a verdict that refuses over another.
 */
public sealed interface CombinationCriterion {

    /** The combinations the body settles a value by. */
    record Interactions(InteractionEvidence measured) implements CombinationCriterion {

        public Interactions {
            java.util.Objects.requireNonNull(measured, "a criterion is measured by something");
        }
    }

    /**
     * The two-class combinations of the behavior's positions, where its decisions meet nowhere.
     *
     * <p>What the pair space has always counted, now as the criterion of the behaviors that have
     * nothing better. An injected behavior is the clearest of them: it has no body, so there is
     * nothing to read a meeting out of.
     */
    record PairFallback(PartitionEvidence.PairSpace space) implements CombinationCriterion {

        public PairFallback {
            java.util.Objects.requireNonNull(space, "a criterion is measured by something");
        }
    }

    /**
     * Which of the two this behavior is held to.
     *
     * <p>Null where neither can be answered: a behavior whose measures were not made has no
     * criterion rather than the fallback one, and answering the fallback would report the product
     * of positions nobody divided as the thing this behavior is held to.
     */
    static CombinationCriterion of(InteractionEvidence meetings, PartitionEvidence partition) {
        if (meetings != null && meetings.asked().any()) {
            return new Interactions(meetings);
        }
        return partition == null ? null : new PairFallback(partition.pairs());
    }
}
