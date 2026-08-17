package souther.compiler.coverage;

import java.util.OptionalInt;

/**
 * A place in a body that something can or cannot arrive at, named once.
 *
 * <p>Not the probe number. A probe is made where a row can be recorded, which takes two things:
 * the place has to answer a value, and it has to stand where a row can get to. So the arms an
 * author writes and the arms a run can be observed in are different collections, and the ones with
 * no probe are exactly the ones a claim is about — an arm answering {@code unreachable} answers no
 * value, so it never had a number, and the reading that judges what the author declared there was
 * looking for it under one.
 *
 * <p>Two layers, made together and here only. Everything below reads whichever it needs: a claim is
 * judged at the {@code controlId}, a branch denominator counts the arms that carry a probe, and a
 * line drawn on a comparison asks about the outcome that leads into an arm rather than about the
 * arm. Derived apart, each of them would answer for a different collection of places, which is what
 * a measurement number standing in for an identity already did once.
 *
 * <p>Numbered per plan, in the order the walk makes them. Two calls of one helper are two
 * occurrences and two ids: each is reached under its caller's own conditions, so what can arrive at
 * one says nothing about the other. What they share is the obligation ({@link
 * CoverageSites.Obligation}), which is what a row is owed for and is not this.
 */
public sealed interface ControlPointId {

    /** Which place this is, among all the places of one plan. */
    int controlId();

    /**
     * One arm, as it stands in the tree that runs.
     *
     * @param probe where a run is recorded, or empty where no row that stands can be in this arm.
     *              Empty is an ordinary answer and not a gap: the arm is still an arm, still
     *              written, and still something a reading can prove nothing arrives at
     */
    record ArmOccurrence(int controlId, OptionalInt probe) implements ControlPointId {

        public ArmOccurrence {
            if (probe == null) {
                throw new IllegalArgumentException(
                        "an arm with no answer about its probe is one nothing numbered");
            }
        }

        /** Whether a run through this arm can be observed, which is what a branch denominator
         *  counts and what could show a proof about it wrong. */
        public boolean isMeasured() {
            return probe.isPresent();
        }
    }

    /**
     * One comparison coming out one way.
     *
     * <p>Which arm that leads to is not this, and the two are not each other's. A condition stops as
     * soon as it is settled, so under {@code A && B} the arm taken when the condition fails is
     * reached both by a value that made {@code B} false and by one that never reached {@code B} —
     * the arm cannot say which comparison came out which way, and a line is drawn on the comparison.
     *
     * @param comparisonProbe where the comparison's own value is recorded
     * @param result          the way it came out
     */
    record ComparisonOutcome(int controlId, int comparisonProbe, boolean result)
            implements ControlPointId {}
}
