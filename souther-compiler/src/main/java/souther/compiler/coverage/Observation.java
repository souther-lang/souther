package souther.compiler.coverage;

import java.util.Set;

/**
 * What one run of one row was seen to do, as a value nothing goes on changing.
 *
 * <p>One snapshot and not two channels. What is recorded has two shapes — the places a run passed
 * through, and the ways the comparisons it evaluated came out — and they are taken together, of one
 * thread, between one {@code begin} and one {@code end}. Handed over as two values they would be two
 * things a reader could get from different runs, and a reader that asked for one of them would be
 * reasoning about a run it had only half of.
 *
 * <p>{@link #comparisons} and {@link #taken} agree about the comparisons, in both directions: one
 * call records a comparison as reached and records which way it came out, so a run holding either
 * without the other is one nothing produces. Held both ways because either half alone is a value a
 * reader is answered wrongly from — a way out of a place the run says it never reached, or a place
 * the run reached that no way out of it is recorded for, which reads as a comparison nothing
 * evaluated.
 *
 * <p><b>Numbers, and what numbering they are of.</b> A probed class is handed the number the
 * emitter wrote into the call and has no numbering to ask what it addresses, so what a run leaves
 * behind is numbers. What says which numbering they are of is the classes the run went through, and
 * this carries what those classes were emitted under. So the two halves of "where was this run
 * recorded" are here and nowhere else: a reader turns them into places by holding this against a
 * numbering ({@link SiteNumbering#align}), and one that does not match is refused rather than
 * answered.
 *
 * @param numbering   what the classes this run went through were numbered by
 * @param taken       the numbers the run was recorded at, which is what a branch measure counts and
 *                    what a boundary drawn on a guard is met by
 * @param comparisons the ways the comparisons it evaluated came out
 */
public record Observation(NumberingIdentity numbering, Set<Integer> taken,
                          Set<ComparisonOutcome> comparisons) {

    public Observation {
        if (numbering == null) {
            throw new IllegalArgumentException(
                    "a run was recorded under some numbering or its numbers mean nothing");
        }
        taken = taken == null ? Set.of() : Set.copyOf(taken);
        comparisons = comparisons == null ? Set.of() : Set.copyOf(comparisons);
        // Held here and not left to whoever records one. What a recording is written like is a
        // producer's business and can change; that a way out of a comparison means the comparison
        // was reached is what every reader of this is entitled to, and a value that broke it would
        // certify a claim about a place the same value says was never got to.
        //
        // Both ways out of one comparison together are not a breach and must not be refused: a
        // place a run comes back to is evaluated more than once, and a recording that held only
        // which way it went the first time would be saying less than it saw.
        for (ComparisonOutcome way : comparisons) {
            if (!taken.contains(way.at())) {
                throw new IllegalArgumentException(
                        "a run that saw " + way + " is one that reached " + way.at());
            }
        }
        // And the other way round, which is the same call seen from the other side. What a
        // comparison's number is written by is one call that records both, so a run holding the
        // number of a comparison and no way out of it is one nothing produces — and read, it says
        // the comparison was never reached, because a comparison is answered by the ways out and
        // the numbers a branch measure counts are the arms.
        //
        // Which family a number was issued to is the numbering's answer, and this run says which
        // numbering it is of, so it can be asked here.
        Set<Integer> answered = new java.util.LinkedHashSet<>();
        comparisons.forEach(way -> answered.add(way.at()));
        for (int raw : taken) {
            if (numbering.at(raw) instanceof SiteAddress.Comparison && !answered.contains(raw)) {
                throw new IllegalArgumentException("a run that reached " + numbering.at(raw)
                        + " is one that had it come out some way; " + raw
                        + " is recorded as reached and no way out of it is");
            }
        }
    }
}
