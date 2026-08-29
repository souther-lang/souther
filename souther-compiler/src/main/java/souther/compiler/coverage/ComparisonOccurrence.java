package souther.compiler.coverage;

/**
 * One comparison of one body, as the thing a rule is read off and a run is recorded at.
 *
 * <p>What a reading of the model joins on. A line drawn on a comparison, a decision said of it and a
 * hit recorded at it are three readers of one place, and until now each of them held the emission
 * site — a number this compiler's instrumentation hands out — and matched on it. That made a
 * numbering the join key: two readers agreeing meant they had been given the same int, and nothing
 * said what the int was of.
 *
 * <p>So the number stays and stops being the identity. {@link #emissionSite} is read where the
 * bytecode is written and where a recording is read back, and nowhere that is deciding what a
 * comparison means.
 *
 * <p>Occurrence and not comparison: a non-recursive helper is spliced into each body that calls it,
 * so one comparison the author wrote is several here, each reached under its caller's own
 * conditions.
 *
 * @param emissionSite where a run through this is recorded, which is the instrumentation's number
 *                     for it and not this
 */
public record ComparisonOccurrence(int emissionSite) {

    @Override
    public String toString() {
        return "comparison@" + emissionSite;
    }
}
