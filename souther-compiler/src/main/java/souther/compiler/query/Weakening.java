package souther.compiler.query;

import souther.compiler.observe.Incompleteness;
import souther.compiler.partition.ClosureGap;
import souther.compiler.types.CoverageOrigin;

/**
 * One thing that leaves a measurement weaker than it looks.
 *
 * <p>What a measure kept as a local variable and threw away. Every measure that came back
 * {@code PARTIAL} worked out a boolean, and every reader above it worked the same boolean out again
 * from the fields beside the answer — a flag on the combinations, the rules nothing took in, the
 * rows that could not be classified. Each of those was a second representation of one assertion, and
 * each was that measure's own business to know about (issue #953).
 *
 * <p><b>A sum and not a shared shape.</b> Every arm holds what the reader that found it produced,
 * whole. Written as one record with a code and a subject wide enough to hold a rule, an axis, a
 * probe and a source, every reader wanting the fact would take the subject apart again by the code
 * beside it — which is the reconstruction this type exists to stop, one level down.
 *
 * <p>So what the arms share is that they weaken a measurement and travel up to whoever assembles
 * one. That is the only operation anything performs on them, and it is the only thing worth having
 * in common: {@link WeakeningSet#union}.
 *
 * <p><b>Every arm is identified well enough to survive that union.</b> Two facts that are one fact
 * collapse — one rule this compiler could not read, found from three behaviors, is one thing to tell
 * an author — and two that are not must not. A bare probe number is not a fact, which is why the
 * arms that are about one behavior say which.
 */
public sealed interface Weakening {

    /**
     * Something the rows were to be measured from was not observed.
     *
     * <p>The vocabulary already existed and was already collected, a list at a time, beside the
     * measures rather than inside them — which is why the report had to join the two by hand and
     * why a behavior's status was decided from a list its measures never saw.
     */
    record ObservationIncomplete(Incompleteness cause) implements Weakening {}

    /**
     * Rows were observed and what a behavior answered with could not be read back as a case.
     *
     * <p>Not an observation that went missing: the row ran and came back. How many there were is the
     * measurement's own count, and is not repeated here — this says which position could not be
     * read, which is what nothing else says.
     */
    record OutputCasesUnreadable(String behavior) implements Weakening {}

    /** The same at one of a behavior's inputs, counted from zero. */
    record InputCasesUnreadable(String behavior, int at) implements Weakening {}

    /**
     * A row was observed and stopped before it finished, so what it would have gone through went
     * with it.
     *
     * <p>Named by the row, which is what tells one from another. A measure weakened by this counted
     * over rows that are all there and one of which is not all there — which is not the same as a
     * measure over rows nothing saw, and reads identically without this.
     */
    record RowDidNotFinish(souther.compiler.observe.RowIdentity row) implements Weakening {}

    /** A row's value at one border could not be read, so what is not found at that border is
     *  undecided rather than absent. */
    record BorderValueUnreadable(souther.compiler.partition.Border border) implements Weakening {}

    /** The reading of the model that a measure depends on did not run out. */
    record ModelReadingIncomplete(ClosureGap cause) implements Weakening {}

    /**
     * The space of two-class combinations was too large to walk, so the counts describe part of it.
     *
     * <p>Not an observation that went missing and not a reading of the model that stopped: the model
     * was read and the rows were seen, and this measure's own enumeration is what ran out. It was
     * the one warrant a measure did carry — a {@code truncated} flag beside the status, which #951
     * had to add a constructor check to keep the two in step.
     */
    record PairSpaceTruncated(String behavior, long total, int limit) implements Weakening {}

    /**
     * A row went through an arm this compiler had proven nothing arrives at.
     *
     * <p>Nothing about the model is wrong here — the proof is. So this is not missing evidence: it
     * is evidence that an analysis the numbers were computed with does not hold, which is why it is
     * an arm of its own and never one of {@link ObservationIncomplete}.
     */
    record ProofContradicted(String behavior, int probe) implements Weakening {}

    /**
     * Two decisions of one body could not be told apart, so the arms counted as one arm are more
     * than one.
     *
     * <p>What the numbers then hold is more than they say. {@link CoverageOrigin} names the fork
     * within its module, so this needs nothing beside it to be a fact.
     */
    record ArmsUnsettled(CoverageOrigin fork) implements Weakening {}
}
