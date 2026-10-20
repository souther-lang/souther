package souther.compiler.coverage;

/**
 * One condition of a numbering, and the way a run had it come out on one of its visits.
 *
 * <p>What {@link RecordedVisit} is once the number has been read as a place, as
 * {@link SeenConditionOutcome} is to {@link RecordedConditionOutcome}.
 */
public record SeenVisit(ConditionOutcomeSite at, int nth, boolean held) {

    public SeenVisit {
        if (at == null) {
            throw new IllegalArgumentException("a visit to a condition is a visit to one");
        }
        if (nth < 0 || nth >= RecordedVisit.MOST) {
            throw new IllegalArgumentException(
                    "a run records the first " + RecordedVisit.MOST + " visits, not visit " + nth);
        }
    }
}
