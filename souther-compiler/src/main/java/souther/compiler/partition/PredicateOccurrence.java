package souther.compiler.partition;

/**
 * Which reading of a predicate this is, inside one body.
 *
 * <p>One rule the author wrote is read once per place it stands in the body that runs: a
 * non-recursive helper is expanded at each call, so
 *
 * <pre>let holds (p, s) = String.startsWith(p, s)</pre>
 *
 * applied twice with two different strings is one rule and two readings, and the two divide the
 * position they name into different sets. Filed under the rule alone, the second would close the
 * account the first opened and one of the two divisions would go missing.
 *
 * <p><b>Not the rule, and not a name anything outside this walk can be matched by.</b> Which rule it
 * is comes from the source and is
 * {@link souther.compiler.check.RuleRef.Predicate}'s; this says which of that rule's readings the
 * walk of one expanded body arrived at. The number is the walk's own count over that body, which is
 * a function of the body — what identity needs is that two readings never share one, and they do
 * not.
 *
 * <p><b>And it is not a place a run is recorded at.</b> A class a predicate divides a position into
 * is met by writing a value there, not by getting anything to answer, so nothing is instrumented for
 * one of these and there is no site beside it. That is the whole of what makes it something the walk
 * may issue: a coverage origin is minted where a source is read because two copies of one construct
 * must not become two obligations, and this exists precisely to tell those copies apart.
 *
 * @param ordinal which of the body's predicate readings this is, in the order the walk met them
 */
public record PredicateOccurrence(int ordinal) {

    public PredicateOccurrence {
        if (ordinal < 0) {
            throw new IllegalArgumentException(
                    "a reading of a predicate stands somewhere among the body's: " + ordinal);
        }
    }

    @Override
    public String toString() {
        return "predicate reading " + ordinal;
    }
}
