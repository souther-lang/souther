package souther.compiler.query;

/**
 * Everything measured about one behavior, and the one place what it went without is worked out.
 *
 * <p>A whole holds what its parts went without and decides nothing of its own. That was already the
 * rule (issue #953); what it lacked was somewhere to be. The union was written where the document is
 * assembled, over a list of measures named there — so the parts a behavior has were a list somebody
 * had to remember to add to, and the fourth of them was missing from it. A run that went without
 * something reached the document only through the three that were named, and a module every one of
 * which had nothing to be about reported {@code complete} beside a line saying a row of it did not
 * come back (issue #996).
 *
 * <p><b>The reading is one of the parts.</b> It is the measure of the rows themselves rather than a
 * measure counted over them, and it is the only one that can never be inapplicable — so it is what
 * carries a run's shortfall where every other part has nothing to be about. Which is the whole of
 * the fix: the parts are asked here, and the reading is one of them by being a field rather than by
 * anybody remembering it.
 *
 * <p><b>Null is the compile not having got far enough to be asked.</b> Three of these are absent
 * where the module never reached the query that answers them, which is not a measure that came back
 * with nothing: every measure that ran says why it has no number. The reading is always there,
 * because there is always an answer to how far the rows were read — including that nobody asked.
 *
 * @param reading   how far the reading of this behavior's rows got, and what it read
 * @param signature what the rows establish about the cases of its inputs and its output
 * @param partition what they establish about the classes and the lines its rules draw
 * @param branch    what they establish about the arms of its body
 */
public record BehaviorEvidence(Adequacy.RowReading reading,
                               Adequacy.SignatureEvidence signature,
                               PartitionEvidence partition,
                               Adequacy.BranchEvidence branch) {

    public BehaviorEvidence {
        java.util.Objects.requireNonNull(reading,
                "there is always an answer to how far a behavior's rows were read");
    }

    /**
     * What this behavior's measures went without, all of them.
     *
     * <p>Asked of the parts, and each of those answers for its own. Nothing here reads the shape of
     * what came back: a measure nobody asked for is not a degradation and neither is one a behavior
     * has nothing to answer, so neither is in this — which is the measurement's own answer rather
     * than a question put to the field's name.
     */
    public WeakeningSet weakening() {
        WeakeningSet out = reading.measured().weakening();
        if (signature != null) {
            out = out.union(signature.weakening());
        }
        if (partition != null) {
            out = out.union(partition.weakening());
        }
        if (branch != null) {
            out = out.union(branch.measured().weakening());
        }
        return out;
    }
}
