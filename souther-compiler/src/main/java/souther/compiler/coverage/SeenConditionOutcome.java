package souther.compiler.coverage;

/**
 * One condition of a numbering, and the way a run had it come out.
 *
 * <p>What {@link RecordedConditionOutcome} is once the number has been read as a place. The two say
 * the same thing about one event and are not interchangeable: the first is what a running class
 * writes down, where a number is all there is to write, and this is what a reader asks about, where
 * a number addresses nothing on its own.
 *
 * <p>Which way it came out and not merely that it was reached, because those are different
 * questions and a reader that had only the second could not tell a row that took the other way from
 * one that never got there.
 */
public record SeenConditionOutcome(ConditionOutcomeSite at, boolean held) {

    public SeenConditionOutcome {
        if (at == null) {
            throw new IllegalArgumentException("a way a condition came out is a way one came out");
        }
    }
}
