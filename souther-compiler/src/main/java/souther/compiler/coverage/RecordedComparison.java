package souther.compiler.coverage;

/**
 * What the two sides of a comparison of whole numbers came to on one visit, as a run records it.
 *
 * <p>Beside {@link RecordedVisit} and keyed the way it is: the visit is the one the way it came
 * out was recorded as, so the sides and the way are one evaluation of the comparison. Kept for the
 * visits that are kept ({@link RecordedVisit#MOST}) and for no other.
 *
 * <p>The numbers a run worked out, and not a reading of them. Which of the two is the number a
 * rule is about, and what a line on it says, is the measure's to settle.
 *
 * @param at    the number the run was recorded at
 * @param nth   which visit of the run, counting from none
 * @param left  what the left side came to
 * @param right what the right side came to
 */
public record RecordedComparison(int at, int nth, long left, long right) {

    public RecordedComparison {
        if (at < 0) {
            throw new IllegalArgumentException(
                    "a run is recorded at a number the emitter wrote: " + at);
        }
        if (nth < 0 || nth >= RecordedVisit.MOST) {
            throw new IllegalArgumentException("a run keeps the sides of the first "
                    + RecordedVisit.MOST + " visits to a comparison, not visit " + nth);
        }
    }
}
