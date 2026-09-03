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
 * @param searches   what building a value here came to under each reading of the line, and empty
 *                   where nobody asked for one. Every one of them and not the strongest: what a
 *                   search of one reading came to is a fact about this point, two readings can have
 *                   come to two different things, and neither takes the other back. Kept as one, the
 *                   fact a reader was given was whichever the readings were walked in front of
 */
public record ObligationAssessment(Criterion criterion, ObligationCoverage coverage,
                                   ItemAssessment.WritabilityProjection projection,
                                   SearchOutcomes searches) {

    public ObligationAssessment {
        if (criterion == null || coverage == null || projection == null || searches == null) {
            throw new IllegalArgumentException(
                    "an obligation is a criterion, what the readings came to, what the rules prove"
                            + " and what was searched for: " + criterion + " " + coverage + " "
                            + projection + " " + searches);
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
            // Asked of the reasons rather than of one constant. A point nothing was read against is
            // work to hand to an author where nothing that was not read could be hiding a row
            // there — which is what "no row names this behavior" means and what a reason added
            // beside it would have to say for itself.
            case ObligationCoverage.NotMeasured it -> !it.why().mayHideARow();
            case ObligationCoverage.Witnessed _, ObligationCoverage.Undecided _ -> false;
        };
    }

    /** The same point, with what one more search of it came to. */
    public ObligationAssessment settledBy(ItemAssessment.Attempt searched) {
        return new ObligationAssessment(criterion, coverage, projection,
                searches.plus(SearchOutcomes.of(searched)));
    }

    /**
     * What has shown that a row can be written here, read off the three things that show it.
     *
     * <p>Derived and never held, as it is of one reading: the grounds are answers to questions this
     * record already carries, and a set kept beside them would be the same facts written twice.
     */
    public ItemAssessment.WritabilityEvidence writabilityEvidence() {
        // Any one of them. A value read back where it was built for is grounds that a row can be
        // written at the point whichever reading of the line composed it — the readings owe the one
        // row between them, so what one of them showed the point, they all showed it.
        return ItemAssessment.WritabilityEvidence.of(projection, hasRowWitness(),
                searches.certified());
    }

    /**
     * The same, and where the knowing stopped where there are no grounds.
     *
     * <p>What an account reads. The grounds alone answer one question and leave two situations
     * looking alike — nothing has shown a row can be written, and the showing of it was stopped —
     * and an account acts on those differently.
     *
     * <p>Over every search of the point, so that what stopped any of them is said. Two readings
     * stopped by two figures are two pieces of work, and a reader told about one of them would be
     * told about whichever the readings happened to be walked in front of.
     */
    public WritabilityKnowledge writabilityKnowledge() {
        return WritabilityKnowledge.of(writabilityEvidence(), searches);
    }

    /** What the readings behind this went without. */
    public WeakeningSet weakening() {
        return coverage.weakening();
    }

    /**
     * Where this stands in the account a report counts it in.
     *
     * <p>Derived here and read everywhere. A count, a finding and a build's refusal put one question
     * to the two answers this holds, and {@link ObligationDisposition} is that question asked once.
     */
    public ObligationDisposition disposition() {
        return ObligationDisposition.of(coverage, writabilityKnowledge());
    }
}
