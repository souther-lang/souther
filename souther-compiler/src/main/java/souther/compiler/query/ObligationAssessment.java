package souther.compiler.query;

import souther.compiler.partition.Criterion;

/**
 * What became of one point of an authored line, over every reading of that line.
 *
 * <p>Beside {@link ItemAssessment.Owed}, which answers the same three questions of one reading. What
 * differs is the coverage: a reading's is a {@link Measurement} of that reading and a debt's is
 * {@link ObligationCoverage}, which cannot hold the state where something went unread and a row was
 * seen anyway. So the two grains are two types, and a reader holding one of them can be asked only
 * the questions its grain answers.
 *
 * <p>Three answers rather than one, for the reason {@link ItemAssessment.Owed} keeps three: what the
 * rows showed is read off what this compilation ran, what the rules prove about a value existing
 * here is read off the rules, and what a search did is what a search did.
 *
 * @param projection what reading the rules reaching the value this point sits in established about a
 *                   value being there
 * @param attempt    what building a value here came to, or null where nobody asked for one
 */
public record ObligationAssessment(Criterion criterion, ObligationCoverage coverage,
                                   ItemAssessment.WritabilityProjection projection,
                                   ItemAssessment.Attempt attempt) {

    public ObligationAssessment {
        if (criterion == null || coverage == null || projection == null) {
            throw new IllegalArgumentException(
                    "an obligation is a criterion, what the readings came to, and what the rules"
                            + " prove: " + criterion + " " + coverage + " " + projection);
        }
    }

    /** Whether a row this compilation observed stands at the point. */
    public boolean hasRowWitness() {
        return coverage.hasRowWitness();
    }

    /**
     * Whether building a value here would tell anybody anything.
     *
     * <p>The measurement's own answer and not the search's. A point a row already sits at needs no
     * candidate, and one whose measurement never happened is not a piece of work to hand to anybody
     * — offered anyway, both put a specific row in front of an author that may already be written.
     */
    public boolean worthSearching() {
        return switch (coverage) {
            case ObligationCoverage.Missed _ -> true;
            case ObligationCoverage.NotMeasured it ->
                    it.why() == ItemAssessment.Coverage.NotAsked.NO_ROWS;
            case ObligationCoverage.Witnessed _, ObligationCoverage.Undecided _ -> false;
        };
    }

    /** The same point, with what a search of it came to. */
    public ObligationAssessment settledBy(ItemAssessment.Attempt searched) {
        if (attempt != null) {
            throw new IllegalStateException(
                    "a point searched twice: " + criterion + " already has " + attempt);
        }
        return new ObligationAssessment(criterion, coverage, projection, searched);
    }

    /**
     * What has shown that a row can be written here, read off the three things that show it.
     *
     * <p>Derived and never held, as it is of one reading: the grounds are answers to questions this
     * record already carries, and a set kept beside them would be the same facts written twice.
     */
    public ItemAssessment.WritabilityEvidence writabilityEvidence() {
        return ItemAssessment.WritabilityEvidence.of(projection, hasRowWitness(),
                attempt instanceof ItemAssessment.Attempt.Built);
    }

    /** What the readings behind this went without. */
    public WeakeningSet weakening() {
        return coverage.weakening();
    }

    /**
     * Whether this is a row an author is owed: the point was measured and missed, and something has
     * shown a row can be written there.
     *
     * <p>The two halves are asked of the two answers rather than of one flattened state. A missed
     * point nothing promises is writable is not a gap — the point is where the reading stopped
     * rather than where the model does — and a point nobody measured is not one either. Neither is
     * one the readings left undecided: the row that answers it may be in the part nobody read.
     */
    public boolean isUnmetGap() {
        return coverage instanceof ObligationCoverage.Missed && writabilityEvidence().known();
    }
}
