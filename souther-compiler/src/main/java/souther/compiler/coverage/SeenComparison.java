package souther.compiler.coverage;

/**
 * What the two sides of a comparison of whole numbers came to on one visit, at a place of the
 * numbering the run is read under.
 *
 * <p>{@link RecordedComparison} once its number is a place, as {@link SeenVisit} is of
 * {@link RecordedVisit}.
 *
 * @param at    where the comparison is
 * @param nth   which visit of the run, counting from none
 * @param left  what the left side came to
 * @param right what the right side came to
 */
public record SeenComparison(ConditionOutcomeSite at, int nth, long left, long right) {

    public SeenComparison {
        if (at == null) {
            throw new IllegalArgumentException("a visit to a comparison is a visit to one");
        }
        if (nth < 0 || nth >= RecordedVisit.MOST) {
            throw new IllegalArgumentException(
                    "a run records the first " + RecordedVisit.MOST + " visits, not visit " + nth);
        }
    }
}
